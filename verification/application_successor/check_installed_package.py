#!/usr/bin/env python3
"""Installed-distribution qualification of one Linux CPython platform (REL-B, REL-C).

    python check_installed_package.py --repo . --build DIR --output NEW_DIR

`--build` is the output of the release build job: two independent runs of
`scripts/build_distributions.py` in `DIR/one` and `DIR/two`. This script, run
with the interpreter being qualified:

1. checks that the interpreter is one of the release policy's platforms
   (`linux-cpython-3.12`, `linux-cpython-3.13`) and that the checkout is clean;
2. checks that both builds came from this commit and are byte-identical;
3. installs the hash-locked test dependencies and then the wheel
   (`--no-deps`, then `pip check`) into a fresh virtual environment;
4. checks that `permansson_app` imports from that environment, reports the
   pyproject version, and that its packaged data equals the source;
5. runs the complete application test suite against the installed wheel
   (from a copy of the tests whose package sources are removed) and records
   every method's outcome, refusing a suite that does not match discovery;
6. runs the end-to-end walkthrough of all 26 exact profiles through the
   installed `permansson-app`;
7. writes `Permansson.App.EvidenceRecord.v1` records for every selected
   capability: `numeric_test`, `cross_platform`, `source_build` and `package`.

A record says PASS only for methods that actually passed here. Anything that
failed, errored, was skipped or did not run gets its own non-PASS record, so
the release gate sees it. Every record names, as its artifact, the SHA-256 of
`results.json`, the raw outcomes it was derived from.

The records are self-produced. They become release evidence only after the
release gate authenticates the GitHub run, job and artifact that carried them
(`release_gate.py`). This script grants nothing by itself.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import platform as host
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
import zipfile

BASE = Path(__file__).resolve().parents[2]
APP_REL = 'apps/permansson/application-successor'
POLICY_REL = 'src/permansson_app/data/acceptance_policy.successor_numeric.v1.json'
RUNNER_ID = 'installed-distribution:verification/application_successor/check_installed_package.py'
RECORD_FORMAT = 'Permansson.App.EvidenceRecord.v1'
QUALIFICATION_FORMAT = 'Permansson.App.InstalledQualification.v1'
SUBJECT_FORMAT = 'Permansson.App.ReleaseSubject.v1'
WALKTHROUGH = 'scripts/end_to_end.py:'


class QualificationError(Exception):
    pass


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode('utf-8')


def digest(data: bytes) -> str:
    return sha256(data).hexdigest()


def platform_id() -> str:
    return f'{sys.platform}-{sys.implementation.name}-{sys.version_info.major}.{sys.version_info.minor}'


def release_subject(*, package: str, version: str, scope: str, policy_sha256: str,
                    wheel_sha256: str, sdist_sha256: str) -> dict:
    """The exact thing a release is about; its SHA-256 is every record's subject."""
    return {'format': SUBJECT_FORMAT, 'package': package, 'version': version, 'scope': scope,
            'policy_sha256': policy_sha256, 'wheel_sha256': wheel_sha256, 'sdist_sha256': sdist_sha256}


def subject_sha256(subject: dict) -> str:
    return digest(canonical(subject))


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(['git', *args], cwd=repo, check=True, capture_output=True, text=True).stdout.strip()


def source_identity(repo: Path) -> dict:
    return {'commit': _git(repo, 'rev-parse', 'HEAD'), 'tree': _git(repo, 'rev-parse', 'HEAD^{tree}'),
            'clean': _git(repo, 'status', '--porcelain', '--untracked-files=all') == '',
            'commit_time': int(_git(repo, 'log', '-1', '--format=%ct', 'HEAD'))}


def project(app: Path) -> dict:
    return tomllib.loads((app / 'pyproject.toml').read_text(encoding='utf-8'))['project']


def check_builds(build: Path, source: dict) -> dict:
    """Both builds come from this commit, at its commit time, and are byte-identical."""
    records = []
    for name in ('one', 'two'):
        path = build / name / 'distributions.json'
        if not path.is_file():
            raise QualificationError(f'missing build record {path}')
        record = json.loads(path.read_text(encoding='utf-8'))
        if record.get('source') is None or record['source'].get('commit') != source['commit'] \
                or record['source'].get('tree') != source['tree'] or record['source'].get('clean') is not True:
            raise QualificationError(f'build {name} is not bound to the clean commit {source["commit"]}')
        if record.get('source_date_epoch') != source['commit_time']:
            raise QualificationError(f'build {name} did not use the commit time as SOURCE_DATE_EPOCH')
        for kind in ('wheel', 'sdist'):
            artifact = build / name / record[kind]['name']
            if digest(artifact.read_bytes()) != record[kind]['sha256']:
                raise QualificationError(f'build {name}: {kind} bytes differ from its record')
        records.append(record)
    if any(records[0][k] != records[1][k] for k in ('wheel', 'sdist', 'build_tools')):
        raise QualificationError('the two builds are not byte-identical')
    return records[0]


def _run(cmd, *, cwd, env, timeout):
    proc = subprocess.run([str(c) for c in cmd], cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    return proc.returncode, proc.stdout, proc.stderr


def _ignore(_dir, names):
    return [n for n in names if n in ('build', 'dist', '__pycache__') or n.endswith('.egg-info')]


# Runs inside the qualified environment: discover the mirrored suite, run it
# and record every method's outcome. Import failures are outcomes too.
_SUITE_RUNNER = r'''
import json, sys, unittest
tests, out = sys.argv[1], sys.argv[2]
loader = unittest.TestLoader()
suite = loader.discover(tests, top_level_dir=tests)
outcomes = {}
class Recorder(unittest.TextTestResult):
    def addSuccess(self, test): super().addSuccess(test); outcomes[test.id()] = 'PASS'
    def addFailure(self, test, err): super().addFailure(test, err); outcomes[test.id()] = 'FAIL'
    def addError(self, test, err): super().addError(test, err); outcomes[test.id()] = 'ERROR'
    def addSkip(self, test, reason): super().addSkip(test, reason); outcomes[test.id()] = 'SKIPPED'
    def addExpectedFailure(self, test, err): super().addExpectedFailure(test, err); outcomes[test.id()] = 'FAIL'
    def addUnexpectedSuccess(self, test): super().addUnexpectedSuccess(test); outcomes[test.id()] = 'FAIL'
    def addSubTest(self, test, subtest, err):
        # Keyed by the parent method: a failing subtest fails its method.
        super().addSubTest(test, subtest, err)
        if err is not None: outcomes[test.id()] = 'FAIL'
result = unittest.TextTestRunner(stream=sys.stderr, resultclass=Recorder, verbosity=0).run(suite)
json.dump({'ran': result.testsRun, 'loader_errors': [str(e)[:400] for e in loader.errors],
           'outcomes': outcomes}, open(out, 'w'), indent=1, sort_keys=True)
'''


def qualify(repo: Path, build: Path, output: Path, *, python: str = sys.executable,
            platform: str | None = None) -> dict:
    """Qualify the built wheel on `python`; write results.json, evidence_records.json, qualification.json."""
    # Subprocesses run in a temporary directory: resolve every path first.
    repo, build, output = repo.resolve(), build.resolve(), output.absolute()
    app = repo / APP_REL
    if output.exists():
        raise QualificationError(f'{output} exists; choose a new directory')
    probe = subprocess.run([python, '-I', '-c', 'import sys;print(f"{sys.platform}-{sys.implementation.name}-'
                            '{sys.version_info.major}.{sys.version_info.minor}")'],
                           capture_output=True, text=True, timeout=60)
    actual = probe.stdout.strip()
    policy_bytes = (app / POLICY_REL).read_bytes()
    policy = json.loads(policy_bytes)
    if platform is not None and platform != actual:
        raise QualificationError(f'asked to qualify {platform} with a {actual} interpreter')
    if actual not in policy['platforms']:
        raise QualificationError(f'{actual} is not a platform of the release policy {policy["platforms"]}')
    source = source_identity(repo)
    if not source['clean']:
        raise QualificationError('the checkout has modified or untracked files')
    built = check_builds(build, source)
    meta = project(app)
    wheel = build / 'one' / built['wheel']['name']
    members = zipfile.ZipFile(wheel).namelist()
    subject = release_subject(package=meta['name'], version=meta['version'], scope=policy['scope'],
                              policy_sha256=digest(policy_bytes), wheel_sha256=built['wheel']['sha256'],
                              sdist_sha256=built['sdist']['sha256'])
    checks: dict[str, bool | str] = {
        'wheel_members_clean': not [n for n in members if '/tests/' in n or n.startswith('tests/')
                                    or n.endswith(('.pyc', '.pyo'))]}
    env = {k: v for k, v in os.environ.items() if k not in ('PYTHONPATH', 'PYTHONHOME')}
    # The legacy and native tests need the repository (historical validator,
    # C10/C11 providers); they read it from here, never from the import path.
    env['PERMANSSON_SOURCE_ROOT'] = str(repo)
    with tempfile.TemporaryDirectory(prefix='permansson-qualify-') as td:
        work = Path(td)
        venv = work / 'venv'
        code, out, err = _run([python, '-m', 'venv', venv], cwd=work, env=env, timeout=300)
        if code:
            raise QualificationError(f'cannot create a virtual environment: {err[-800:]}')
        vpy = venv / 'bin/python'
        for args in (['--require-hashes', '-r', app / 'requirements-test.lock'], ['--no-deps', wheel]):
            code, out, err = _run([vpy, '-m', 'pip', 'install', '--disable-pip-version-check', '--no-input', *args],
                                  cwd=work, env=env, timeout=600)
            if code:
                raise QualificationError(f'install failed: {(err or out)[-1500:]}')
        code, out, err = _run([vpy, '-m', 'pip', 'check'], cwd=work, env=env, timeout=120)
        checks['pip_check'] = code == 0
        mirror = work / 'mirror'
        shutil.copytree(app, mirror, ignore=_ignore)
        for module in (mirror / 'src/permansson_app').rglob('*.py'):
            module.unlink()
        probe = ('import json,sys;from importlib.metadata import version;import permansson_app;'
                 'print(json.dumps([permansson_app.__file__,version(sys.argv[1]),permansson_app.__version__]))')
        code, out, err = _run([vpy, '-B', '-c', probe, meta['name']], cwd=work, env=env, timeout=60)
        if code:
            raise QualificationError(f'the installed package does not import: {err[-800:]}')
        located, dist_version, module_version = json.loads(out.strip().splitlines()[-1])
        package_dir = Path(located).resolve().parent
        checks['imports_from_installed_environment'] = str(package_dir).startswith(str(venv.resolve()))
        checks['version_matches_pyproject'] = dist_version == module_version == meta['version']
        source_data = {p.relative_to(app / 'src/permansson_app'): p
                       for p in (app / 'src/permansson_app/data').rglob('*') if p.is_file()}
        installed = {p.relative_to(package_dir): p for p in (package_dir / 'data').rglob('*') if p.is_file()}
        checks['package_data_identical'] = sorted(source_data) == sorted(installed) and all(
            digest(source_data[k].read_bytes()) == digest(installed[k].read_bytes()) for k in source_data)
        runner = work / 'suite_runner.py'
        runner.write_text(_SUITE_RUNNER, encoding='utf-8')
        code, out, err = _run([vpy, '-B', runner, mirror / 'tests', work / 'suite.json'],
                              cwd=work, env=env, timeout=1800)
        suite = json.loads((work / 'suite.json').read_text(encoding='utf-8'))
        counter = ('import json,sys,unittest;l=unittest.TestLoader();'
                   's=l.discover(sys.argv[1],top_level_dir=sys.argv[1]);print(json.dumps(s.countTestCases()))')
        code, out, err = _run([vpy, '-B', '-c', counter, app / 'tests'], cwd=work, env=env, timeout=300)
        expected = json.loads(out.strip().splitlines()[-1]) if code == 0 else None
        checks['suite_complete'] = (suite['loader_errors'] == [] and suite['ran'] == expected
                                    and len(suite['outcomes']) == expected)
        # Nothing in the suite may fail; a skip is allowed only for a test the
        # policy does not name (those need a Git checkout, not the package).
        named = {m for kinds in policy['required'].values() for m in kinds['numeric_test']}
        checks['suite_has_no_failures'] = all(
            status == 'PASS' or (status == 'SKIPPED' and method not in named)
            for method, status in suite['outcomes'].items())
        e2e_report = work / 'e2e.json'
        code, out, err = _run([vpy, '-B', app / 'scripts/end_to_end.py', '--app', venv / 'bin/permansson-app',
                               '--source-root', repo, '--report', e2e_report], cwd=work, env=env, timeout=3600)
        e2e = json.loads(e2e_report.read_text(encoding='utf-8')) if e2e_report.is_file() else {'profiles': [],
                                                                                               'failures': [], 'status': 'ERROR'}
        checks['walkthrough_from_installed_package'] = str(e2e.get('package_location', '')).startswith(str(venv.resolve()))
        # Every row, including the native C10/C11 runs through the installed CLI.
        checks['walkthrough_passed'] = e2e.get('status') == 'PASS' and not e2e.get('failures')
        code, out, err = _run([venv / 'bin/permansson-governance', '--help'], cwd=work, env=env, timeout=60)
        checks['governance_entry_point'] = code == 0
    walkthrough = {row['command']: 'PASS' for row in e2e.get('profiles', []) if row.get('command') != 'run'}
    for failure in e2e.get('failures', []):
        walkthrough[str(failure.get('command'))] = 'FAIL'
    results = {'format': 'Permansson.App.InstalledQualificationResults.v1', 'platform': actual,
               'python': host.python_version(), 'source': {k: source[k] for k in ('commit', 'tree')},
               'subject': subject, 'checks': checks, 'suite': suite, 'walkthrough': walkthrough}
    output.mkdir(parents=True)
    raw = json.dumps(results, indent=1, sort_keys=True).encode('utf-8') + b'\n'
    (output / 'results.json').write_bytes(raw)
    records = evidence_records(policy, results, digest(raw), producer=producer())
    (output / 'evidence_records.json').write_text(json.dumps(records, indent=1, sort_keys=True) + '\n',
                                                  encoding='utf-8')
    passed = all(r['status'] == 'PASS' for r in records) and all(v is True for v in checks.values())
    summary = {'format': QUALIFICATION_FORMAT, 'platform': actual, 'source': results['source'],
               'subject_sha256': subject_sha256(subject), 'results_sha256': digest(raw),
               'records': len(records), 'status': 'PASS' if passed else 'FAIL',
               'evidence_status': 'SELF_PRODUCED_UNTIL_THE_RELEASE_GATE_AUTHENTICATES_ITS_RUN'}
    (output / 'qualification.json').write_text(json.dumps(summary, indent=1, sort_keys=True) + '\n',
                                               encoding='utf-8')
    return summary


def producer() -> str:
    run, attempt, job = (os.environ.get(k) for k in ('GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_JOB'))
    if run and attempt and job and re.fullmatch(r'\d+', run) and re.fullmatch(r'\d+', attempt):
        return f'github-actions:run/{run}/attempt/{attempt}/job/{job}'[:160]
    return 'local'


def method_outcome(method: str, results: dict) -> str:
    if method.startswith(WALKTHROUGH):
        return results['walkthrough'].get(method[len(WALKTHROUGH):], 'NOT_EXECUTED')
    return results['suite']['outcomes'].get(method, 'NOT_EXECUTED')


def evidence_records(policy: dict, results: dict, results_sha256: str, *, producer: str) -> list[dict]:
    """Records for every selected capability, derived only from `results`."""
    subject = subject_sha256(results['subject'])
    plat = results['platform']
    installed_ok = all(v is True for v in results['checks'].values())
    records = []

    def record(cap, kind, methods, status, artifact):
        records.append({'format': RECORD_FORMAT, 'evidence_id': f'{plat}/{cap}/{kind}/{len(records)}',
                        'kind': kind, 'subject_sha256': subject, 'source_commit': results['source']['commit'],
                        'source_tree': results['source']['tree'], 'capability': cap, 'execution_profile': 'numeric',
                        'platform': plat, 'method_ids': sorted(methods), 'status': status,
                        'artifact_sha256': artifact, 'producer': producer, 'reviewer': None})

    for cap, kinds in sorted(policy['required'].items()):
        grouped: dict[str, list[str]] = {}
        for method in kinds['numeric_test']:
            grouped.setdefault(method_outcome(method, results), []).append(method)
        for status in sorted(grouped):
            record(cap, 'numeric_test', grouped[status], status if status in
                   ('PASS', 'FAIL', 'ERROR', 'SKIPPED', 'NOT_EXECUTED') else 'ERROR', results_sha256)
        record(cap, 'cross_platform', kinds['cross_platform'], 'PASS' if installed_ok else 'FAIL', results_sha256)
        record(cap, 'source_build', kinds['source_build'], 'PASS', results_sha256)
        for which in ('wheel_sha256', 'sdist_sha256'):
            record(cap, 'package', kinds['package'], 'PASS', results['subject'][which])
    return records


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--repo', type=Path, default=BASE)
    parser.add_argument('--build', type=Path, required=True, help='release build output (one/ and two/)')
    parser.add_argument('--output', type=Path, required=True, help='new directory for the evidence')
    parser.add_argument('--platform', help='the policy platform this interpreter must be')
    args = parser.parse_args(argv)
    try:
        summary = qualify(args.repo, args.build, args.output, platform=args.platform)
    except (QualificationError, subprocess.SubprocessError, OSError, ValueError, KeyError) as exc:
        print(json.dumps({'status': 'ERROR', 'error': str(exc)}), file=sys.stderr)
        return 2
    print(json.dumps(summary, indent=1, sort_keys=True))
    return 0 if summary['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
