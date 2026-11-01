"""Release gate for the finite numeric application: every check fails closed.

A throwaway Git repository holds the real release policy, registry and
package metadata; synthetic distributions and qualification results are
derived with the same record builder the qualification runner uses; a fake
GitHub API serves the run, its jobs and its artifacts. Each test changes one
thing and expects the gate to refuse it.
"""
from __future__ import annotations

from copy import deepcopy
from hashlib import sha256
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile

BASE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(BASE / 'verification/application_successor'))

import check_installed_package as runner  # noqa: E402
import release_gate as gate  # noqa: E402

APP = BASE / runner.APP_REL
RUN, ATTEMPT, OWNER = 4242, 1, 'HMarcusWH'
GIT_ENV = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
GIT_ENV.update(GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@example.invalid', GIT_COMMITTER_NAME='t',
               GIT_COMMITTER_EMAIL='t@example.invalid')


def git(repo, *args):
    return subprocess.run(['git', *args], cwd=repo, check=True, capture_output=True, text=True,
                          env=GIT_ENV).stdout.strip()


def zipped(directory: Path) -> bytes:
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, 'w') as archive:
        for path in sorted(directory.rglob('*')):
            if path.is_file():
                archive.write(path, path.relative_to(directory).as_posix())
    return buffer.getvalue()


class FakeGitHub:
    def __init__(self, routes: dict, blobs: dict):
        self.routes, self.blobs = routes, blobs

    def json(self, path):
        if path not in self.routes:
            raise gate.GateError(f'404 {path}')
        return deepcopy(self.routes[path])

    def bytes(self, path, accept=None):
        if path not in self.blobs:
            raise gate.GateError(f'404 {path}')
        return self.blobs[path]


class Fixture:
    """A complete, valid release run; tests mutate one part of it."""

    def __init__(self, root: Path, version: str = '0.2.0'):
        self.root = root
        self.repo = root / 'repo'
        app = self.repo / runner.APP_REL
        for rel in ('pyproject.toml', runner.POLICY_REL, 'src/permansson_app/data/capabilities.json'):
            (app / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(APP / rel, app / rel)
        if version != '0.2.0':
            text = (app / 'pyproject.toml').read_text(encoding='utf-8')
            (app / 'pyproject.toml').write_text(text.replace('version = "0.2.0"', f'version = "{version}"'),
                                                encoding='utf-8')
        git(self.repo, 'init', '-q', '-b', 'main')
        git(self.repo, 'add', '-A')
        git(self.repo, 'commit', '-q', '-m', 'release candidate')
        self.source = runner.source_identity(self.repo)
        self.commit = self.source['commit']
        self.policy_bytes = (app / runner.POLICY_REL).read_bytes()
        self.policy = json.loads(self.policy_bytes)
        self.meta = runner.project(app)
        self.make_build()
        self.make_qualifications()
        self.make_api()

    def make_build(self):
        self.build = self.root / 'artifacts/build'
        wheel = f'{self.meta["name"].replace("-", "_")}-{self.meta["version"]}-py3-none-any.whl'
        sdist = f'{self.meta["name"].replace("-", "_")}-{self.meta["version"]}.tar.gz'
        for name in ('one', 'two'):
            folder = self.build / name
            folder.mkdir(parents=True)
            (folder / wheel).write_bytes(b'wheel-bytes')
            (folder / sdist).write_bytes(b'sdist-bytes')
            record = {'format': 'Permansson.App.ReproducibleDistributions.v1',
                      'source': {**{k: self.source[k] for k in ('commit', 'tree', 'clean', 'commit_time')},
                                 'application_tree': 'f' * 40},
                      'source_date_epoch': self.source['commit_time'],
                      'build_tools': {'build': '1.3.0', 'setuptools': '84.2.1'}, 'python': '3.13.17',
                      'wheel': {'name': wheel, 'sha256': sha256(b'wheel-bytes').hexdigest()},
                      'sdist': {'name': sdist, 'sha256': sha256(b'sdist-bytes').hexdigest()},
                      'evidence_status': 'LOCAL_SELF_PRODUCED_NOT_AUTHENTICATED'}
            (folder / 'distributions.json').write_text(json.dumps(record), encoding='utf-8')
        self.subject = runner.release_subject(package=self.meta['name'], version=self.meta['version'],
                                              scope=self.policy['scope'],
                                              policy_sha256=sha256(self.policy_bytes).hexdigest(),
                                              wheel_sha256=sha256(b'wheel-bytes').hexdigest(),
                                              sdist_sha256=sha256(b'sdist-bytes').hexdigest())

    def results(self, platform):
        methods = {m for kinds in self.policy['required'].values() for m in kinds['numeric_test']}
        return {'format': 'Permansson.App.InstalledQualificationResults.v1', 'platform': platform,
                'python': platform[-4:], 'source': {'commit': self.commit, 'tree': self.source['tree']},
                'subject': self.subject,
                'checks': {'pip_check': True, 'imports_from_installed_environment': True,
                           'version_matches_pyproject': True, 'package_data_identical': True,
                           'suite_complete': True, 'suite_has_no_failures': True,
                           'walkthrough_from_installed_package': True},
                'suite': {'ran': len(methods), 'loader_errors': [],
                          'outcomes': {m: 'PASS' for m in methods if not m.startswith(runner.WALKTHROUGH)}},
                'walkthrough': {m[len(runner.WALKTHROUGH):]: 'PASS' for m in methods
                                if m.startswith(runner.WALKTHROUGH)}}

    def write_qualification(self, platform, results, records=None):
        folder = self.root / 'artifacts' / f'qualification-{platform}'
        if folder.exists():
            shutil.rmtree(folder)
        folder.mkdir(parents=True)
        raw = json.dumps(results, indent=1, sort_keys=True).encode('utf-8') + b'\n'
        (folder / 'results.json').write_bytes(raw)
        key = gate.QUALIFY_JOBS[platform][0]
        if records is None:
            records = runner.evidence_records(self.policy, results, sha256(raw).hexdigest(),
                                              producer=f'github-actions:run/{RUN}/attempt/{ATTEMPT}/job/{key}')
        (folder / 'evidence_records.json').write_text(json.dumps(records), encoding='utf-8')

    def make_qualifications(self):
        for platform in gate.QUALIFY_JOBS:
            self.write_qualification(platform, self.results(platform))

    def make_api(self):
        jobs = [{'id': 10, 'name': gate.BUILD_JOB[1]}] + [
            {'id': 11 + i, 'name': name} for i, (_key, name) in enumerate(gate.QUALIFY_JOBS.values())]
        for job in jobs:
            job.update(status='completed', conclusion='success', head_sha=self.commit, run_id=RUN)
        self.run = {'id': RUN, 'run_attempt': ATTEMPT, 'repository': {'full_name': gate.REPOSITORY},
                    'path': gate.WORKFLOW_PATH, 'head_sha': self.commit, 'head_branch': 'main',
                    'event': 'workflow_dispatch', 'actor': {'login': OWNER}, 'triggering_actor': {'login': OWNER}}
        self.jobs = {'jobs': jobs}
        self.refresh_artifacts()

    def refresh_artifacts(self):
        folders = {gate.BUILD_ARTIFACT: self.build}
        folders.update({f'qualification-{p}': self.root / 'artifacts' / f'qualification-{p}' for p in gate.QUALIFY_JOBS})
        self.artifacts, self.blobs = [], {}
        for i, (name, folder) in enumerate(sorted(folders.items())):
            blob = zipped(folder)
            self.artifacts.append({'id': 900 + i, 'name': name, 'expired': False, 'workflow_run': {'id': RUN},
                                   'digest': 'sha256:' + sha256(blob).hexdigest()})
            self.blobs[f'/actions/artifacts/{900 + i}/zip'] = blob

    def api(self):
        return FakeGitHub({f'/actions/runs/{RUN}': self.run,
                           f'/actions/runs/{RUN}/attempts/{ATTEMPT}/jobs?per_page=100': self.jobs,
                           f'/actions/runs/{RUN}/artifacts?per_page=100': {'artifacts': self.artifacts}},
                          self.blobs)

    def run_gate(self, inputs=None, output=None):
        output = output or self.root / 'out'
        if output.exists():
            shutil.rmtree(output)
        inputs = {'version': self.meta['version']} if inputs is None else inputs
        return gate.gate(self.repo, self.api(), RUN, ATTEMPT, inputs, output)


class ReleaseGateTests(unittest.TestCase):
    def setUp(self):
        self.td = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.td, True)
        self.fx = Fixture(self.td)

    def refused(self, message=None, **kwargs):
        with self.assertRaises(gate.GateError) as raised:
            self.fx.run_gate(**kwargs)
        if message:
            self.assertIn(message, str(raised.exception))

    def test_a_complete_owner_dispatched_run_is_qualified(self):
        manifest = self.fx.run_gate()
        self.assertEqual(manifest['status'], 'QUALIFIED_OWNER_ACTIVATED')
        self.assertEqual((manifest['version'], manifest['tag']), ('0.2.0', 'permansson-app-v0.2.0'))
        self.assertEqual(len(manifest['capabilities']), 26)
        self.assertEqual(manifest['platforms'], ['linux-cpython-3.12', 'linux-cpython-3.13'])
        self.assertEqual(manifest['release_authority']['kind'], 'OWNER_ENGINEERING_POLICY')
        self.assertIs(manifest['release_authority']['independent_security_review'], False)
        self.assertIs(manifest['claims']['independent_security_review'], False)
        self.assertEqual(manifest['claims']['lean_status'], 'NOT_EXECUTED')
        self.assertEqual(manifest['activation']['triggering_actor'], OWNER)
        self.assertEqual(manifest['assessment']['missing'], ['EXTERNAL_OWNER_RELEASE_ACTIVATION'])
        self.assertIs(manifest['assessment']['authorized_release'], False)
        self.assertEqual(manifest['evidence']['records'], 2 * 26 * 5)
        out = self.td / 'out'
        notes = (out / 'release-notes.md').read_text(encoding='utf-8')
        self.assertIn('No independent security review is claimed', notes)
        self.assertIn('lean_status=NOT_EXECUTED', notes)
        self.assertIn(manifest['distributions']['wheel']['sha256'], notes)
        sums = (out / 'SHA256SUMS').read_text(encoding='utf-8').splitlines()
        self.assertEqual(len(sums), 3)
        for line in sums:
            digest, name = line.split('  ')
            path = out / ('release-manifest.json' if name == 'release-manifest.json' else f'dist/{name}')
            self.assertEqual(sha256(path.read_bytes()).hexdigest(), digest)

    def test_only_the_owner_can_activate_a_release(self):
        for field, value in (('event', 'push'), ('event', 'pull_request'), ('actor', {'login': 'someone'}),
                             ('triggering_actor', {'login': 'someone'})):
            with self.subTest(field=field, value=value):
                original = deepcopy(self.fx.run)
                self.fx.run[field] = value
                self.refused()
                self.fx.run = original

    def test_the_run_must_be_the_release_workflow_on_main_at_this_commit(self):
        for field, value in (('path', '.github/workflows/research-lean.yml'), ('head_sha', 'f' * 40),
                             ('head_branch', 'feature'), ('repository', {'full_name': 'someone/fork'}),
                             ('run_attempt', 2), ('id', 1)):
            with self.subTest(field=field):
                original = deepcopy(self.fx.run)
                self.fx.run[field] = value
                self.refused()
                self.fx.run = original

    def test_every_required_job_must_have_succeeded_in_this_attempt(self):
        mutations = {
            'failed': lambda jobs: jobs[1].update(conclusion='failure'),
            'cancelled': lambda jobs: jobs[2].update(conclusion='cancelled'),
            'still running': lambda jobs: jobs[0].update(status='in_progress', conclusion=None),
            'missing': lambda jobs: jobs.pop(1),
            'duplicated': lambda jobs: jobs.append(dict(jobs[1])),
            'other commit': lambda jobs: jobs[0].update(head_sha='f' * 40),
        }
        for name, mutate in mutations.items():
            with self.subTest(name):
                original = deepcopy(self.fx.jobs)
                mutate(self.fx.jobs['jobs'])
                self.refused()
                self.fx.jobs = original

    def test_artifacts_must_match_the_digest_github_recorded(self):
        mutations = {
            'tampered bytes': lambda fx: fx.blobs.update({k: v + b'x' for k, v in list(fx.blobs.items())[:1]}),
            'no digest': lambda fx: fx.artifacts[0].update(digest=None),
            'expired': lambda fx: fx.artifacts[1].update(expired=True),
            'other run': lambda fx: fx.artifacts[2].update(workflow_run={'id': 1}),
            'missing': lambda fx: fx.artifacts.pop(0),
            'duplicated': lambda fx: fx.artifacts.append(dict(fx.artifacts[0])),
        }
        for name, mutate in mutations.items():
            with self.subTest(name):
                self.fx.refresh_artifacts()
                mutate(self.fx)
                self.refused()
        self.fx.refresh_artifacts()

    def test_qualification_jobs_fetch_the_build_through_the_same_check(self):
        out = self.td / 'fetched'
        result = gate.fetch_one(self.fx.api(), RUN, gate.BUILD_ARTIFACT, out)
        self.assertEqual(result['artifact'], gate.BUILD_ARTIFACT)
        self.assertEqual(sorted(p.name for p in out.iterdir()), ['one', 'two'])
        with self.assertRaises(gate.GateError):
            gate.fetch_one(self.fx.api(), RUN, gate.BUILD_ARTIFACT, out)  # exists
        build = next(a for a in self.fx.artifacts if a['name'] == gate.BUILD_ARTIFACT)
        self.fx.blobs[f'/actions/artifacts/{build["id"]}/zip'] += b'x'
        with self.assertRaises(gate.GateError):
            gate.fetch_one(self.fx.api(), RUN, gate.BUILD_ARTIFACT, self.td / 'tampered')
        self.assertFalse((self.td / 'tampered').exists())

    def test_unsafe_artifact_members_are_refused(self):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, 'w') as archive:
            archive.writestr('../escape.txt', 'x')
        blob = buffer.getvalue()
        self.fx.artifacts[0]['digest'] = 'sha256:' + sha256(blob).hexdigest()
        self.fx.blobs[f'/actions/artifacts/{self.fx.artifacts[0]["id"]}/zip'] = blob
        self.refused('unsafe artifact member')
        self.assertFalse((self.td / 'escape.txt').exists())

    def test_records_must_be_exactly_those_derived_from_the_raw_results(self):
        platform = 'linux-cpython-3.13'
        results = self.fx.results(platform)
        raw = json.dumps(results, indent=1, sort_keys=True).encode('utf-8') + b'\n'
        records = runner.evidence_records(self.fx.policy, results, sha256(raw).hexdigest(),
                                          producer=f'github-actions:run/{RUN}/attempt/{ATTEMPT}/job/{gate.QUALIFY_JOBS[platform][0]}')
        doctored = deepcopy(records)
        doctored[0]['method_ids'] = doctored[0]['method_ids'][1:]
        for name, value in (('dropped method', doctored), ('local producer', runner.evidence_records(
                self.fx.policy, results, sha256(raw).hexdigest(), producer='local'))):
            with self.subTest(name):
                self.fx.write_qualification(platform, results, value)
                self.fx.refresh_artifacts()
                self.refused('differ from their raw results')

    def test_a_failing_skipped_or_missing_method_blocks_the_release(self):
        platform = 'linux-cpython-3.12'
        method = next(m for m in self.fx.results(platform)['suite']['outcomes'])
        for status in ('FAIL', 'ERROR', 'SKIPPED', None):
            with self.subTest(status=status):
                results = self.fx.results(platform)
                if status is None:
                    del results['suite']['outcomes'][method]
                else:
                    results['suite']['outcomes'][method] = status
                self.fx.write_qualification(platform, results)
                self.fx.refresh_artifacts()
                self.refused()
        results = self.fx.results(platform)
        results['checks']['package_data_identical'] = False
        self.fx.write_qualification(platform, results)
        self.fx.refresh_artifacts()
        self.refused('failing evidence')

    def test_results_bound_to_another_source_or_subject_are_refused(self):
        platform = 'linux-cpython-3.13'
        for name, mutate in (('source', lambda r: r['source'].update(commit='f' * 40)),
                             ('subject', lambda r: r['subject'].update(wheel_sha256='f' * 64)),
                             ('platform', lambda r: r.update(platform='linux-cpython-3.11'))):
            with self.subTest(name):
                results = self.fx.results(platform)
                mutate(results)
                self.fx.write_qualification(platform, results)
                self.fx.refresh_artifacts()
                self.refused()

    def test_builds_must_be_identical_and_bound_to_this_commit(self):
        record_path = self.fx.build / 'two/distributions.json'
        original = record_path.read_text(encoding='utf-8')
        for name, mutate in (('different wheel', lambda r: r['wheel'].update(sha256='f' * 64)),
                             ('other commit', lambda r: r['source'].update(commit='f' * 40)),
                             ('dirty source', lambda r: r['source'].update(clean=False)),
                             ('other epoch', lambda r: r.update(source_date_epoch=1))):
            with self.subTest(name):
                record = json.loads(original)
                mutate(record)
                record_path.write_text(json.dumps(record), encoding='utf-8')
                self.fx.refresh_artifacts()
                self.refused()
        record_path.write_text(original, encoding='utf-8')

    def test_the_version_must_be_final_and_confirmed_by_the_dispatch(self):
        self.refused('dispatch confirmed', inputs={'version': '0.2.1'})
        self.refused('dispatch confirmed', inputs={})
        dev = Fixture(self.td / 'dev', version='0.2.0.dev0')
        with self.assertRaises(gate.GateError) as raised:
            dev.run_gate(inputs={'version': '0.2.0.dev0'})
        self.assertIn('not a final release version', str(raised.exception))

    def test_a_dirty_checkout_is_refused(self):
        (self.fx.repo / 'stray.txt').write_text('x', encoding='utf-8')
        self.refused('modified or untracked')

    def test_a_policy_that_claims_independent_review_is_refused(self):
        path = self.fx.repo / runner.APP_REL / runner.POLICY_REL
        policy = json.loads(path.read_text(encoding='utf-8'))
        policy['release_authority']['independent_security_review'] = True
        path.write_text(json.dumps(policy), encoding='utf-8')
        git(self.fx.repo, 'commit', '-qam', 'claim review')
        self.refused('release policy rejected')


class JobNameTests(unittest.TestCase):
    def test_release_jobs_never_reuse_a_required_check_context(self):
        sys.path.insert(0, str(BASE))
        from verification.integrity.workflow_contract import JOBS, LEGACY_CONTEXTS
        names = {gate.BUILD_JOB[0], gate.BUILD_JOB[1]} | {n for pair in gate.QUALIFY_JOBS.values() for n in pair}
        self.assertFalse(names & (set(JOBS) | set(LEGACY_CONTEXTS) | {'application-contract'}))


class FullScopeTests(unittest.TestCase):
    """HARD-02: the full release names all 26 profiles and both platforms, exactly."""

    def setUp(self):
        _raw, _data, self.policy = gate.load_policy(BASE)
        self.profiles = gate.registry_profiles(BASE)
        self.capabilities = sorted(self.policy.required)
        self.platforms = list(self.policy.platforms)

    def test_the_real_policy_and_registry_agree(self):
        gate.require_full_scope(self.capabilities, self.platforms, self.policy, self.profiles)
        self.assertEqual(len(self.capabilities), 26)

    def test_subsets_extras_relabels_and_duplicates_are_refused(self):
        cases = {
            'capability subset': (self.capabilities[1:], self.platforms),
            'extra capability': (self.capabilities + ['c10.fixed_six_state.numeric.v1'], self.platforms),
            'relabelled capability': (self.capabilities[1:] + [self.capabilities[0] + '.x'], self.platforms),
            'duplicated capability': (self.capabilities + self.capabilities[:1], self.platforms),
            'platform subset': (self.capabilities, self.platforms[:1]),
            'extra platform': (self.capabilities, self.platforms + ['windows-cpython-3.13']),
            'relabelled platform': (self.capabilities, ['linux-cpython-3.12', 'linux-cpython-3.14']),
            'duplicated platform': (self.capabilities, self.platforms + self.platforms[:1]),
        }
        for name, (capabilities, platforms) in cases.items():
            with self.subTest(name), self.assertRaises(gate.GateError):
                gate.require_full_scope(capabilities, platforms, self.policy, self.profiles)


class PublishedReleaseTests(unittest.TestCase):
    def setUp(self):
        self.td = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.td, True)
        self.fx = Fixture(self.td)
        self.manifest = self.fx.run_gate()
        out = self.td / 'out'
        self.manifest_path = out / 'release-manifest.json'
        wheel, sdist = self.manifest['distributions']['wheel']['name'], self.manifest['distributions']['sdist']['name']
        files = {wheel: (out / 'dist' / wheel).read_bytes(), sdist: (out / 'dist' / sdist).read_bytes(),
                 'SHA256SUMS': (out / 'SHA256SUMS').read_bytes(), 'release-manifest.json': self.manifest_path.read_bytes()}
        self.assets = [{'id': 70 + i, 'name': n} for i, n in enumerate(sorted(files))]
        self.blobs = {f'/releases/assets/{70 + i}': files[n] for i, n in enumerate(sorted(files))}
        self.ref = {'object': {'type': 'commit', 'sha': self.fx.commit}}
        self.release = {'draft': False, 'assets': self.assets}

    def api(self):
        tag = self.manifest['tag']
        return FakeGitHub({f'/git/ref/tags/{tag}': self.ref, f'/releases/tags/{tag}': self.release}, self.blobs)

    def test_the_published_release_matches_the_manifest(self):
        result = gate.verify_published(self.api(), self.manifest['tag'], self.manifest_path)
        self.assertEqual(result['status'], 'VERIFIED')

    def test_mismatches_are_refused(self):
        tag = self.manifest['tag']
        mutations = {
            'tag elsewhere': lambda: self.ref['object'].update(sha='f' * 40),
            'draft': lambda: self.release.update(draft=True),
            'extra asset': lambda: self.assets.append({'id': 99, 'name': 'extra.txt'}),
            'changed asset': lambda: self.blobs.update({'/releases/assets/70': b'changed'}),
        }
        for name, mutate in mutations.items():
            with self.subTest(name):
                self.setUp()
                mutate()
                with self.assertRaises(gate.GateError):
                    gate.verify_published(self.api(), tag, self.manifest_path)
        with self.assertRaises(gate.GateError):
            gate.verify_published(self.api(), 'permansson-app-v9.9.9', self.manifest_path)


if __name__ == '__main__':
    unittest.main()
