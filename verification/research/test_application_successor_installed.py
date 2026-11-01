"""Installed-distribution qualification of the successor application, end to end.

Runs the release pipeline's real steps on this interpreter's platform:

1. two independent builds of the wheel and sdist with the hash-locked tools
   (`scripts/build_distributions.py`), from a clean checkout of HEAD;
2. `verification/application_successor/check_installed_package.py`, which
   installs the wheel from the locks into a fresh environment, checks that the
   package imports from it with byte-identical data, runs the complete
   application suite against the installed code, runs the 26-profile
   walkthrough (and the native C10/C11 runs) through the installed CLI, and
   writes evidence records;
3. the release gate's re-derivation of those records from the raw results,
   and an assessment of this platform against the release policy.

The checkout is used directly when it is clean; otherwise a temporary
detached worktree of HEAD is qualified, so the result always belongs to a
commit. No skip or fallback: missing build or schema dependencies must be
installed and every step must pass. This qualifies one platform; only the
release workflow, with both Linux CPython platforms and an authenticated
GitHub run, can produce release evidence.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import venv

BASE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(BASE / 'verification/application_successor'))

import check_installed_package as runner  # noqa: E402
import release_gate as gate  # noqa: E402
from permansson_app.acceptance import AcceptanceTarget, assess_acceptance  # noqa: E402
from permansson_app.evidence import EvidenceSet, record_digest  # noqa: E402

APP = BASE / runner.APP_REL
RUN, ATTEMPT = 7, 1
GIT_ENV = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}


def _git(repo, *args):
    return subprocess.run(['git', *args], cwd=repo, check=True, capture_output=True, text=True,
                          env=GIT_ENV).stdout.strip()


class InstalledQualificationTest(unittest.TestCase):
    def test_the_built_wheel_qualifies_on_this_platform(self):
        platform = runner.platform_id()
        env = {k: v for k, v in GIT_ENV.items() if k not in ('PYTHONPATH', 'PYTHONHOME')}
        with tempfile.TemporaryDirectory(prefix='permansson-installed-') as td:
            work = Path(td)
            repo = BASE
            if _git(BASE, 'status', '--porcelain', '--untracked-files=all'):
                repo = work / 'checkout'
                _git(BASE, 'worktree', 'add', '--detach', str(repo), 'HEAD')
                self.addCleanup(lambda: _git(BASE, 'worktree', 'remove', '--force', str(repo)))
            policy = json.loads((repo / runner.APP_REL / runner.POLICY_REL).read_text(encoding='utf-8'))
            self.assertIn(platform, policy['platforms'], 'run this test with Linux CPython 3.12 or 3.13')
            builder = work / 'builder'
            venv.EnvBuilder(with_pip=True).create(builder)
            proc = subprocess.run([builder / 'bin/python', '-m', 'pip', 'install', '--disable-pip-version-check',
                                   '--no-input', '--require-hashes', '-r', repo / runner.APP_REL /
                                   'requirements-build.lock'], env=env, capture_output=True, text=True, timeout=600)
            self.assertEqual(proc.returncode, 0, proc.stderr[-4000:])
            build = work / 'build'
            for name in ('one', 'two'):
                proc = subprocess.run([builder / 'bin/python', '-B', repo / runner.APP_REL /
                                       'scripts/build_distributions.py', '--output', build / name,
                                       '--python', builder / 'bin/python'], cwd=repo, env=env,
                                      capture_output=True, text=True, timeout=900)
                self.assertEqual(proc.returncode, 0, proc.stderr[-4000:])

            key = gate.QUALIFY_JOBS[platform][0]
            out = work / 'qualification'
            # Relative --build and --output, from another working directory:
            # the runner must resolve them before its subprocesses change directory.
            proc = subprocess.run([sys.executable, '-B', BASE / 'verification/application_successor/'
                                   'check_installed_package.py', '--repo', repo, '--build', 'build',
                                   '--output', 'qualification', '--platform', platform], cwd=work,
                                  env={**env, 'GITHUB_RUN_ID': str(RUN), 'GITHUB_RUN_ATTEMPT':
                                       str(ATTEMPT), 'GITHUB_JOB': key},
                                  capture_output=True, text=True, timeout=3600)
            self.assertEqual(proc.returncode, 0, proc.stdout[-3000:] + proc.stderr[-6000:])
            summary = json.loads((out / 'qualification.json').read_text(encoding='utf-8'))
            results = json.loads((out / 'results.json').read_text(encoding='utf-8'))
            self.assertEqual(summary['status'], 'PASS')
            self.assertEqual(results['checks'], {k: True for k in results['checks']}, results['checks'])
            self.assertEqual(set(results['checks']), {
                'wheel_members_clean', 'pip_check', 'imports_from_installed_environment', 'version_matches_pyproject',
                'package_data_identical', 'suite_complete', 'suite_has_no_failures',
                'walkthrough_from_installed_package', 'walkthrough_passed', 'governance_entry_point'})
            self.assertEqual(len(results['walkthrough']), 25)

            # The gate's view: the records are exactly those derived from the
            # raw results, and they cover this platform completely.
            source = runner.source_identity(repo)
            built = runner.check_builds(build, source)
            records, _ = gate.derived_records(out, policy, platform, source, results['subject'],
                                              f'github-actions:run/{RUN}/attempt/{ATTEMPT}/job/{key}')
            self.assertEqual(len(records), 26 * 5)
            self.assertTrue(all(r['status'] == 'PASS' for r in records))
            _raw, _data, parsed = gate.load_policy(repo)
            target = AcceptanceTarget.parse({
                'source': {'repository': gate.REPOSITORY, 'commit': source['commit'], 'tree': source['tree'],
                           'application': results['subject']['version'], 'research': gate.RESEARCH_VERSION,
                           'paper': gate.PAPER_VERSION},
                'subject_sha256': runner.subject_sha256(results['subject']),
                'wheel_sha256': built['wheel']['sha256'], 'sdist_sha256': built['sdist']['sha256'],
                'capabilities': sorted(parsed.required), 'platforms': [platform], 'execution_profile': 'numeric'})
            evidence = EvidenceSet.from_external_hashes(
                records, trusted_expected_digests={r['evidence_id']: record_digest(r) for r in records})
            assessment = assess_acceptance(target, evidence, parsed).to_dict()
            self.assertEqual((assessment['status'], assessment['failing'], assessment['missing']),
                             ('EVIDENCE_COMPLETE_REVIEW_REQUIRED', [], ['EXTERNAL_OWNER_RELEASE_ACTIVATION']))
            self.assertIs(assessment['authorized_release'], False)


if __name__ == '__main__':
    unittest.main()
