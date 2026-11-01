#!/usr/bin/env python3
"""Release gate for the Permansson finite numeric application (REL-D).

    python release_gate.py fetch --run-id ID --name ARTIFACT --output NEW_DIR
    python release_gate.py gate --repo . --run-id ID --attempt N --event-file PATH --output NEW_DIR
    python release_gate.py verify-published --tag TAG --manifest PATH

`fetch` lets the qualification jobs take the build job's artifact through the
same authenticated, digest-checked path the gate uses.

`gate` runs inside the release workflow's gate job, after the build and the
two qualification jobs. It passes only if all of the following hold, and then
writes `release-manifest.json` and `SHA256SUMS`:

- G0, scope: the release policy (format v3, owner-engineering authority)
  selects exactly the 26 exact profiles of the registry and exactly the two
  platforms `linux-cpython-3.12` and `linux-cpython-3.13`. The target names
  all of them; a subset, an extra, a relabelled or a duplicated entry fails.
- G0, source: the checkout is clean and at the run's commit; the package
  version is a final release version and matches the dispatch input.
- G1, distributions: the build job built wheel and sdist twice from this
  commit, with the locked tools and the commit time, byte-identically.
- G3, origin: through the GitHub API, the run is this repository's
  `.github/workflows/application-release.yml` on `main` at this commit; the
  build and both qualification jobs of this attempt completed successfully;
  every artifact the gate uses is downloaded through the API and its SHA-256
  equals the digest GitHub recorded for it.
- G2, evidence: every evidence record is re-derived from the raw results in
  its authenticated artifact (a record that differs from that derivation is
  refused), the expected record digests are computed here from that material,
  and the assessment against the policy is complete: nothing failing, and
  nothing missing except the owner activation.
- G5, activation: under the owner-engineering policy, the owner activates a
  release by dispatching this workflow. The run's event is `workflow_dispatch`
  and both its actor and its triggering actor are the policy's owner.

No independent security review is claimed: the policy's release authority is
an owner-engineering policy. The gate's strength is that of GitHub's own
records and of control of the owner's GitHub account; anyone able to act as
that account could also dispatch the workflow.

`verify-published` checks a published GitHub release afterwards: its tag
points at the manifest's commit, and its assets are exactly the wheel, the
sdist, `SHA256SUMS` and the manifest, each with the manifest's SHA-256.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import sys
import tempfile
import urllib.error
import urllib.request
import zipfile

BASE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(BASE / 'apps/permansson/application-successor/src'))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_installed_package import (APP_REL, POLICY_REL, QualificationError, canonical, check_builds,  # noqa: E402
                                     digest, evidence_records, project, release_subject, source_identity,
                                     subject_sha256)
from permansson_app.acceptance import AcceptancePolicy, AcceptanceTarget, assess_acceptance  # noqa: E402
from permansson_app.errors import AppError  # noqa: E402
from permansson_app.evidence import EvidenceSet, record_digest  # noqa: E402

MANIFEST_FORMAT = 'Permansson.App.ReleaseManifest.v1'
REPOSITORY = 'HMarcusWH/PermanssonLean'
WORKFLOW_PATH = '.github/workflows/application-release.yml'
RELEASE_BRANCH = 'main'
RESEARCH_VERSION = '0.2.0'
PAPER_VERSION = '0.1.8'
# (job key, job name). None of them may equal a required check context
# (`build`, `research`, `executable-verification`, the application and
# integrity contexts): a release job must never publish a colliding success.
BUILD_JOB = ('release-build', 'release build')
QUALIFY_JOBS = {'linux-cpython-3.12': ('release-qualify-py312', 'release qualify linux-cpython-3.12'),
                'linux-cpython-3.13': ('release-qualify-py313', 'release qualify linux-cpython-3.13')}
BUILD_ARTIFACT = 'release-build'
QUALIFY_ARTIFACT = 'qualification-{platform}'
FINAL_VERSION = re.compile(r'^\d+\.\d+\.\d+$')
CLAIMS = {'lean_status': 'NOT_EXECUTED', 'independent_security_review': False,
          'scientific_claims_verified': False, 'empirical_identification': 'NOT_IDENTIFIED',
          'independent_mathematical_certification': 'NOT_ASSESSED'}


class GateError(Exception):
    pass


class GitHub:
    """A minimal GitHub REST client; every request carries the job's token."""

    def __init__(self, repository: str, token: str, api: str = 'https://api.github.com'):
        self.repository, self.token, self.api = repository, token, api.rstrip('/')

    def _request(self, url: str, accept: str, auth: bool = True):
        headers = {'Accept': accept, 'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'permansson-release-gate'}
        if auth:
            headers['Authorization'] = f'Bearer {self.token}'
        return urllib.request.Request(url, headers=headers)

    def json(self, path: str) -> dict:
        url = f'{self.api}/repos/{self.repository}{path}'
        with urllib.request.urlopen(self._request(url, 'application/vnd.github+json'), timeout=60) as response:
            return json.loads(response.read())

    def bytes(self, path: str, accept: str = 'application/vnd.github+json') -> bytes:
        """Download, following one redirect to pre-signed storage without the token."""
        url = f'{self.api}/repos/{self.repository}{path}'

        class NoRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, *args, **kwargs):
                return None
        opener = urllib.request.build_opener(NoRedirect)
        try:
            with opener.open(self._request(url, accept), timeout=120) as response:
                return response.read()
        except urllib.error.HTTPError as exc:
            if exc.code not in (301, 302, 303, 307, 308) or not exc.headers.get('Location'):
                raise
            location = exc.headers['Location']
        with urllib.request.urlopen(self._request(location, 'application/octet-stream', auth=False),
                                    timeout=300) as response:
            return response.read()


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise GateError(message)


def load_policy(repo: Path) -> tuple[bytes, dict, AcceptancePolicy]:
    raw = (repo / APP_REL / POLICY_REL).read_bytes()
    data = json.loads(raw)
    try:
        policy = AcceptancePolicy.parse(data)
    except AppError as exc:
        raise GateError(f'release policy rejected: {exc}') from exc
    authority = policy.release_authority
    _require(authority is not None and authority.kind == 'OWNER_ENGINEERING_POLICY'
             and authority.independent_security_review is False,
             'the release policy must name an owner-engineering release authority')
    _require(policy.execution_profile == 'numeric', 'the release scope is numeric only')
    return raw, data, policy


def registry_profiles(repo: Path) -> set[str]:
    registry = json.loads((repo / APP_REL / 'src/permansson_app/data/capabilities.json').read_text(encoding='utf-8'))
    return set(registry['exact_profiles'])


def require_full_scope(capabilities, platforms, policy: AcceptancePolicy, profiles: set[str]) -> None:
    """HARD-02: a full release names every selected capability and platform, exactly once."""
    capabilities, platforms = list(capabilities), list(platforms)
    _require(len(profiles) == 26 and set(policy.required) == profiles,
             'the release policy must select exactly the 26 exact profiles of the registry')
    _require(len(capabilities) == len(set(capabilities)) and set(capabilities) == profiles,
             'the release target must name exactly the 26 exact profiles, once each')
    _require(len(platforms) == len(set(platforms)) and set(platforms) == set(policy.platforms)
             and set(platforms) == set(QUALIFY_JOBS),
             'the release target must name exactly linux-cpython-3.12 and linux-cpython-3.13')


def check_checkout(repo: Path, commit: str) -> dict:
    source = source_identity(repo)
    _require(source['commit'] == commit, f'the checkout is at {source["commit"]}, not the run commit {commit}')
    _require(source['clean'], 'the checkout has modified or untracked files')
    return source


def authenticate_run(api, run_id: int, attempt: int, commit: str, owner: str) -> dict:
    run = api.json(f'/actions/runs/{run_id}')
    _require(run.get('id') == run_id and run.get('run_attempt') == attempt, 'the run or attempt does not match')
    _require((run.get('repository') or {}).get('full_name') == REPOSITORY, 'the run belongs to another repository')
    _require(run.get('path') == WORKFLOW_PATH, f'the run is not {WORKFLOW_PATH}')
    _require(run.get('head_sha') == commit, 'the run was not made at the release commit')
    _require(run.get('head_branch') == RELEASE_BRANCH, f'releases are made from {RELEASE_BRANCH} only')
    _require(run.get('event') == 'workflow_dispatch', 'only a manual dispatch can activate a release')
    _require((run.get('actor') or {}).get('login') == owner and (run.get('triggering_actor') or {}).get('login') == owner,
             f'the release must be dispatched by the owner {owner}')
    jobs = api.json(f'/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100').get('jobs', [])
    found = {}
    for key, name in (BUILD_JOB, *QUALIFY_JOBS.values()):
        matching = [job for job in jobs if job.get('name') == name]
        _require(len(matching) == 1, f'job {name!r} must appear exactly once in this attempt')
        job = matching[0]
        _require(job.get('status') == 'completed' and job.get('conclusion') == 'success',
                 f'job {name!r} did not succeed')
        _require(job.get('head_sha') == commit and job.get('run_id') == run_id, f'job {name!r} is from another run')
        found[key] = job['id']
    return {'run_id': run_id, 'attempt': attempt, 'event': run['event'], 'actor': owner,
            'triggering_actor': owner, 'workflow': WORKFLOW_PATH, 'branch': RELEASE_BRANCH, 'jobs': found}


def _extract(blob: bytes, destination: Path) -> None:
    with zipfile.ZipFile(io.BytesIO(blob)) as archive:
        for member in archive.infolist():
            name = PurePosixPath(member.filename)
            _require(not name.is_absolute() and '..' not in name.parts and (member.external_attr >> 16) & 0o170000
                     != 0o120000, f'unsafe artifact member {member.filename!r}')
            if member.is_dir():
                continue
            target = destination.joinpath(*name.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(archive.read(member))


def fetch_artifacts(api, run_id: int, names: list[str], destination: Path) -> dict:
    """Download each named artifact of the run and check it against GitHub's digest."""
    listed = api.json(f'/actions/runs/{run_id}/artifacts?per_page=100').get('artifacts', [])
    fetched = {}
    for name in names:
        matching = [a for a in listed if a.get('name') == name]
        _require(len(matching) == 1, f'artifact {name!r} must appear exactly once in the run')
        artifact = matching[0]
        _require(artifact.get('expired') is False, f'artifact {name!r} has expired')
        _require((artifact.get('workflow_run') or {}).get('id') == run_id, f'artifact {name!r} is from another run')
        recorded = artifact.get('digest') or ''
        _require(re.fullmatch(r'sha256:[0-9a-f]{64}', recorded) is not None, f'artifact {name!r} has no SHA-256')
        blob = api.bytes(f'/actions/artifacts/{artifact["id"]}/zip')
        _require(digest(blob) == recorded.split(':', 1)[1], f'artifact {name!r} differs from its recorded digest')
        target = destination / name
        _extract(blob, target)
        fetched[name] = {'id': artifact['id'], 'digest': recorded, 'path': target}
    return fetched


def fetch_one(api, run_id: int, name: str, output: Path) -> dict:
    """One authenticated, digest-checked artifact of this run, unpacked at `output`."""
    _require(not output.exists(), f'{output} exists; choose a new directory')
    with tempfile.TemporaryDirectory(prefix='permansson-fetch-') as td:
        fetched = fetch_artifacts(api, run_id, [name], Path(td))
        shutil.move(str(fetched[name]['path']), str(output))
    return {'artifact': name, 'id': fetched[name]['id'], 'digest': fetched[name]['digest']}


def derived_records(qualification: Path, policy_data: dict, platform: str, source: dict, subject: dict,
                    producer: str) -> tuple[list[dict], str]:
    """Re-derive the platform's records from its raw results; refuse any difference."""
    raw = (qualification / 'results.json').read_bytes()
    results = json.loads(raw)
    _require(results.get('platform') == platform, f'{platform}: results are for {results.get("platform")}')
    _require(results.get('source') == {'commit': source['commit'], 'tree': source['tree']},
             f'{platform}: results are for another source')
    _require(results.get('subject') == subject, f'{platform}: results are for another release subject')
    expected = evidence_records(policy_data, results, digest(raw), producer=producer)
    supplied = json.loads((qualification / 'evidence_records.json').read_text(encoding='utf-8'))
    _require(supplied == expected, f'{platform}: evidence records differ from their raw results')
    return expected, digest(raw)


def gate(repo: Path, api, run_id: int, attempt: int, inputs: dict, output: Path) -> dict:
    repo = repo.resolve()
    _require(not output.exists(), f'{output} exists; choose a new directory')
    policy_raw, policy_data, policy = load_policy(repo)
    owner = policy.release_authority.owner
    commit = source_identity(repo)['commit']
    source = check_checkout(repo, commit)
    meta = project(repo / APP_REL)
    version = meta['version']
    _require(FINAL_VERSION.fullmatch(version) is not None, f'{version} is not a final release version')
    _require(inputs.get('version') == version, f'the dispatch confirmed version {inputs.get("version")!r}, '
             f'the source is {version}')
    activation = authenticate_run(api, run_id, attempt, commit, owner)
    with tempfile.TemporaryDirectory(prefix='permansson-gate-') as td:
        work = Path(td)
        names = [BUILD_ARTIFACT] + [QUALIFY_ARTIFACT.format(platform=p) for p in sorted(QUALIFY_JOBS)]
        artifacts = fetch_artifacts(api, run_id, names, work)
        build = artifacts[BUILD_ARTIFACT]['path']
        try:
            built = check_builds(build, source)
        except QualificationError as exc:
            raise GateError(str(exc)) from exc
        for kind in ('wheel', 'sdist'):
            _require(f'-{version}' in built[kind]['name'] and built[kind]['name'].startswith(
                meta['name'].replace('-', '_')), f'{kind} name does not carry {meta["name"]} {version}')
        subject = release_subject(package=meta['name'], version=version, scope=policy.scope,
                                  policy_sha256=digest(policy_raw), wheel_sha256=built['wheel']['sha256'],
                                  sdist_sha256=built['sdist']['sha256'])
        records, qualifications = [], {}
        for platform, (job_key, _name) in sorted(QUALIFY_JOBS.items()):
            name = QUALIFY_ARTIFACT.format(platform=platform)
            producer = f'github-actions:run/{run_id}/attempt/{attempt}/job/{job_key}'
            platform_records, results_sha = derived_records(artifacts[name]['path'], policy_data, platform,
                                                            source, subject, producer)
            records += platform_records
            qualifications[platform] = {'artifact': name, 'artifact_id': artifacts[name]['id'],
                                        'artifact_digest': artifacts[name]['digest'],
                                        'job_id': activation['jobs'][job_key], 'results_sha256': results_sha,
                                        'records': len(platform_records)}
        target = AcceptanceTarget.parse({
            'source': {'repository': REPOSITORY, 'commit': commit, 'tree': source['tree'],
                       'application': version, 'research': RESEARCH_VERSION, 'paper': PAPER_VERSION},
            'subject_sha256': subject_sha256(subject), 'wheel_sha256': built['wheel']['sha256'],
            'sdist_sha256': built['sdist']['sha256'], 'capabilities': sorted(policy.required),
            'platforms': list(policy.platforms), 'execution_profile': 'numeric'})
        require_full_scope(target.capabilities, target.platforms, policy, registry_profiles(repo))
        pins = {r['evidence_id']: record_digest(r) for r in records}
        evidence = EvidenceSet.from_external_hashes(records, trusted_expected_digests=pins)
        assessment = assess_acceptance(target, evidence, policy).to_dict()
        _require(assessment['failing'] == [], f'failing evidence: {assessment["failing"][:5]}')
        _require(assessment['missing'] == ['EXTERNAL_OWNER_RELEASE_ACTIVATION'],
                 f'missing evidence: {[m for m in assessment["missing"] if not m.startswith("EXTERNAL_")][:5]}')
        _require(assessment['status'] == 'EVIDENCE_COMPLETE_REVIEW_REQUIRED', 'evidence is not complete')
        output.mkdir(parents=True)
        dist = output / 'dist'
        dist.mkdir()
        for kind in ('wheel', 'sdist'):
            (dist / built[kind]['name']).write_bytes((build / 'one' / built[kind]['name']).read_bytes())
    manifest = {
        'format': MANIFEST_FORMAT, 'status': 'QUALIFIED_OWNER_ACTIVATED',
        'package': meta['name'], 'version': version, 'tag': f'permansson-app-v{version}',
        'source': {'repository': REPOSITORY, 'commit': commit, 'tree': source['tree']},
        'scope': policy.scope, 'policy': {'path': f'{APP_REL}/{POLICY_REL}', 'sha256': digest(policy_raw)},
        'capabilities': sorted(policy.required), 'platforms': list(policy.platforms),
        'release_authority': policy.release_authority.to_dict(),
        'activation': {k: activation[k] for k in ('run_id', 'attempt', 'event', 'actor', 'triggering_actor',
                                                 'workflow', 'branch')},
        'distributions': {'wheel': built['wheel'], 'sdist': built['sdist'], 'build_tools': built['build_tools'],
                          'source_date_epoch': built['source_date_epoch'],
                          'build_artifact_digest': artifacts[BUILD_ARTIFACT]['digest'],
                          'build_job_id': activation['jobs'][BUILD_JOB[0]]},
        'subject': subject, 'subject_sha256': subject_sha256(subject),
        'qualification': qualifications,
        'evidence': {'records': len(records), 'sha256': digest(canonical(sorted(pins.items())))},
        'assessment': assessment,
        'claims': CLAIMS,
    }
    text = json.dumps(manifest, indent=1, sort_keys=True) + '\n'
    (output / 'release-manifest.json').write_text(text, encoding='utf-8')
    sums = [(built['wheel']['sha256'], built['wheel']['name']), (built['sdist']['sha256'], built['sdist']['name']),
            (digest(text.encode('utf-8')), 'release-manifest.json')]
    (output / 'SHA256SUMS').write_text(''.join(f'{h}  {n}\n' for h, n in sums), encoding='utf-8')
    (output / 'release-notes.md').write_text(release_notes(manifest), encoding='utf-8')
    return manifest


def release_notes(manifest: dict) -> str:
    """The release description; generated from the manifest, not an asset."""
    wheel, sdist = manifest['distributions']['wheel'], manifest['distributions']['sdist']
    return (f"Permansson application {manifest['version']}: the 26 exact finite profiles of scope "
            f"`{manifest['scope']}`, numeric only, on Linux CPython 3.12 and 3.13.\n\n"
            f"- Source: `{manifest['source']['commit']}` (tree `{manifest['source']['tree']}`).\n"
            f"- Wheel `{wheel['name']}`: `{wheel['sha256']}`.\n"
            f"- Sdist `{sdist['name']}`: `{sdist['sha256']}`.\n"
            f"- Qualified on both platforms against the installed wheel; evidence records: "
            f"{manifest['evidence']['records']} (see `release-manifest.json`).\n"
            f"- Release authority: owner-engineering policy, activated by {manifest['activation']['actor']} "
            f"(run {manifest['activation']['run_id']}). **No independent security review is claimed.**\n\n"
            "Every output still reports `lean_status=NOT_EXECUTED`, `scientific_claims_verified=false` and "
            "`empirical_identification=NOT_IDENTIFIED`. This release is not mathematical certification, "
            "empirical identification or publication of results. Check the files with "
            "`sha256sum -c SHA256SUMS`.\n")


def verify_published(api, tag: str, manifest_path: Path) -> dict:
    """The published release is exactly the gated one."""
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    _require(manifest.get('format') == MANIFEST_FORMAT and manifest.get('tag') == tag, 'manifest is for another tag')
    ref = api.json(f'/git/ref/tags/{tag}')
    obj = ref.get('object') or {}
    if obj.get('type') == 'tag':
        obj = (api.json(f'/git/tags/{obj.get("sha")}').get('object') or {})
    _require(obj.get('type') == 'commit' and obj.get('sha') == manifest['source']['commit'],
             f'tag {tag} does not point at {manifest["source"]["commit"]}')
    release = api.json(f'/releases/tags/{tag}')
    _require(release.get('draft') is False, 'the release is still a draft')
    sums = ''.join(f'{h}  {n}\n' for h, n in (
        (manifest['distributions']['wheel']['sha256'], manifest['distributions']['wheel']['name']),
        (manifest['distributions']['sdist']['sha256'], manifest['distributions']['sdist']['name']),
        (digest(manifest_bytes), 'release-manifest.json'))).encode('utf-8')
    expected = {manifest['distributions']['wheel']['name']: manifest['distributions']['wheel']['sha256'],
                manifest['distributions']['sdist']['name']: manifest['distributions']['sdist']['sha256'],
                'release-manifest.json': digest(manifest_bytes), 'SHA256SUMS': digest(sums)}
    assets = release.get('assets') or []
    _require(sorted(a.get('name') for a in assets) == sorted(expected), 'release assets differ from the manifest')
    for asset in assets:
        blob = api.bytes(f'/releases/assets/{asset["id"]}', accept='application/octet-stream')
        _require(digest(blob) == expected[asset['name']], f'published {asset["name"]} differs from the manifest')
    return {'tag': tag, 'commit': manifest['source']['commit'], 'assets': sorted(expected), 'status': 'VERIFIED'}


def _api_from_env() -> GitHub:
    token = os.environ.get('GITHUB_TOKEN')
    if not token or os.environ.get('GITHUB_REPOSITORY') != REPOSITORY:
        raise GateError('the gate runs in this repository\'s release workflow with its GITHUB_TOKEN')
    return GitHub(REPOSITORY, token, os.environ.get('GITHUB_API_URL', 'https://api.github.com'))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    sub = parser.add_subparsers(dest='command', required=True)
    g = sub.add_parser('gate')
    g.add_argument('--repo', type=Path, default=BASE)
    g.add_argument('--run-id', type=int, required=True)
    g.add_argument('--attempt', type=int, required=True)
    g.add_argument('--event-file', type=Path, required=True, help="the workflow's GITHUB_EVENT_PATH")
    g.add_argument('--output', type=Path, required=True)
    f = sub.add_parser('fetch')
    f.add_argument('--run-id', type=int, required=True)
    f.add_argument('--name', required=True)
    f.add_argument('--output', type=Path, required=True)
    v = sub.add_parser('verify-published')
    v.add_argument('--tag', required=True)
    v.add_argument('--manifest', type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        api = _api_from_env()
        if args.command == 'fetch':
            result = fetch_one(api, args.run_id, args.name, args.output)
        elif args.command == 'gate':
            event = json.loads(args.event_file.read_text(encoding='utf-8'))
            result = gate(args.repo, api, args.run_id, args.attempt, event.get('inputs') or {}, args.output)
            result = {k: result[k] for k in ('status', 'package', 'version', 'tag', 'source', 'subject_sha256')}
        else:
            result = verify_published(api, args.tag, args.manifest)
    except (GateError, AppError, QualificationError, urllib.error.URLError, OSError, ValueError, KeyError) as exc:
        print(json.dumps({'status': 'BLOCKED', 'error': str(exc)}), file=sys.stderr)
        return 2
    print(json.dumps(result, indent=1, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
