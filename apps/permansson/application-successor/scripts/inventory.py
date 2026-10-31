"""Current-state inventory of IMPLEMENTATION_MANIFEST.json, recomputed from the Git tree.

The manifest keeps three things apart:

* `historical` — planning facts and per-round records from earlier rounds,
  preserved verbatim and explicitly not current-head evidence;
* `current_inventory` — counts this script recomputes from the tracked tree
  (`--write-current` refreshes them; `--check` fails when they are stale);
* `entries` — one row per inventoried path. A path that is not tracked
  carries a `disposition_current` from `DISPOSITIONS` with its reason.

A tracked file cannot contain the commit that contains it, so the exact head
SHA, trees and manifest digest go into a detached post-commit receipt
(`--receipt PATH`), produced after committing and attached to the pull
request or CI artifacts. The synthetic merge commit and CI run identities are
recorded by CI, not here.

    python scripts/inventory.py --check
    python scripts/inventory.py --write-current
    python scripts/inventory.py --receipt /tmp/inventory-receipt.json
"""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

APP = Path(__file__).resolve().parents[1]
MANIFEST = APP / 'IMPLEMENTATION_MANIFEST.json'
APP_PREFIX = 'apps/permansson/application-successor/'
FORMAT = 'Permansson.App.ImplementationManifest.v2'
DISPOSITIONS = {
    'EXCLUDED_GENERATED_BUILD_PRODUCT': 'generated build output (build/lib); never committed',
    'SUPERSEDED_BY_IMPLEMENTED_EQUIVALENT': 'implemented under the paths in superseded_by (all tracked)',
    'DEFERRED_ALTERNATE_LAYOUT': 'the planned file was not created; related_implemented lists tracked files that '
                                 'cover part of its role, without asserting a full equivalent',
    'DEFERRED_CONTRACT_LAYER': 'part of the cross-profile versioned contract layer, not implemented; per-profile '
                               'schemas and strict parsers are used instead',
    'DEFERRED_SCOPE': 'outside the current implementation scope; no computation is fabricated for it',
    'DEFERRED_DOMAIN_INTEGRATION': 'source-grade domain importers and federation providers; the current domain '
                                   'intake checks evidence envelopes only',
    'REQUIRED_BEFORE_RELEASE': 'needed for a release qualification that has not been selected or authorized',
    'REVIEW_GATED': 'CI trust-profile, workflow or release-gate surface that needs separate independent review',
}
HISTORICAL_PLANNING = {'v2': 217, 'v3': 251, 'overlap': 110, 'union_entries': 358, 'excluded_generated': 21}


class InventoryError(Exception):
    pass


def git(repo: Path, *args: str) -> str:
    proc = subprocess.run(['git', '-C', str(repo), *args], text=True, capture_output=True, timeout=120)
    if proc.returncode != 0:
        raise InventoryError(f'git {" ".join(args)} failed: {proc.stderr.strip()[:300]}')
    return proc.stdout


def repository(start: Path = APP) -> Path:
    try:
        return Path(git(start, 'rev-parse', '--show-toplevel').strip())
    except (InventoryError, OSError) as exc:
        raise InventoryError('a Git checkout is required for the inventory') from exc


def tracked(repo: Path) -> set[str]:
    return set(git(repo, 'ls-files', '-z').split('\0')) - {''}


def load(path: Path = MANIFEST) -> dict:
    return json.loads(path.read_text(encoding='utf-8'))


def dump(manifest: dict, path: Path = MANIFEST):
    path.write_text(json.dumps(manifest, indent=2, ensure_ascii=True) + '\n', encoding='utf-8')


def compute_current(repo: Path, manifest: dict) -> dict:
    files = tracked(repo)
    entries = manifest['entries']
    paths = [e['path'] for e in entries]
    app_files = sorted(p for p in files if p.startswith(APP_PREFIX))
    registry = json.loads((APP / 'src/permansson_app/data/capabilities.json').read_text(encoding='utf-8'))
    bridges = sorted(p for p in files if re.fullmatch(r'PermanssonResearch/ApplicationBridge/[A-Za-z0-9]+\.lean', p))
    live = sorted(p for p in files if re.fullmatch(r'verification/research/test_application_[a-z0-9_]+_live_lean\.py', p))
    methods = sum(len(re.findall(r'^    def test_', (repo / p).read_text(encoding='utf-8'), re.M)) for p in live)
    absent = [e for e in entries if e['path'] not in files]
    return {
        'computed_by': 'scripts/inventory.py --write-current (recomputed from git ls-files; see --check)',
        'manifest_rows': len(entries),
        'unique_paths': len(set(paths)),
        'rows_by_candidate_state': dict(sorted(Counter(e['candidate']['state'] for e in entries).items())),
        'tracked_rows': len(entries) - len(absent),
        'absent_rows': len(absent),
        'absent_rows_by_disposition': dict(sorted(Counter(e.get('disposition_current', 'MISSING') for e in absent).items())),
        'application_tracked_files': len(app_files),
        'application_tracked_files_without_row': len([p for p in app_files if p not in set(paths)]),
        'registered_exact_profiles': len(registry['exact_profiles']),
        'registered_native_capabilities': len(registry['capabilities']),
        'research_bridge_modules': len(bridges),
        'live_lean_replay_files': len(live),
        'live_lean_replay_test_methods': methods,
    }


def check(repo: Path, manifest: dict) -> list[str]:
    """Every invariant the inventory promises; an empty list means it holds."""
    problems = []
    if manifest.get('format') != FORMAT:
        problems.append(f'format is {manifest.get("format")!r}, expected {FORMAT!r}')

    def walk(value, where):
        if isinstance(value, dict):
            if value and all(isinstance(k, str) and k.isdigit() for k in value):
                problems.append(f'{where}: numeric-key object (a spread string or list), not a typed record')
            for key, item in value.items():
                walk(item, f'{where}.{key}')
        elif isinstance(value, list):
            for i, item in enumerate(value):
                walk(item, f'{where}[{i}]')
    walk({k: v for k, v in manifest.items() if k != 'entries'}, 'manifest')
    for i, entry in enumerate(manifest.get('entries', [])):
        walk(entry, f'entries[{i}]')
    historical = manifest.get('historical', {})
    if historical.get('planning_counts', {}) != {**historical.get('planning_counts', {}), **HISTORICAL_PLANNING}:
        problems.append('historical planning counts changed; they are fixed facts of the v2/v3 reconciliation')
    for name, record in historical.get('round_records', {}).items():
        if not str(record.get('evidence_status', '')).startswith('HISTORICAL_') or \
                not str(record.get('evidence_status', '')).endswith('_NOT_EVIDENCE'):
            problems.append(f'historical record {name} is not marked as non-evidence')
    for entry in manifest.get('entries', []):
        state = str((entry.get('candidate') or {}).get('state', ''))
        # CI results are external (the pull request and the detached receipt); a
        # tracked row can only say they are pending.
        if re.search(r'(^|_)(CI|GITHUB)(_|$)', state) and 'PENDING' not in state:
            problems.append(f"{entry.get('path')}: candidate state {state} claims CI evidence inside the tracked manifest")
    files = tracked(repo)
    paths = [e['path'] for e in manifest.get('entries', [])]
    if len(paths) != len(set(paths)):
        problems.append('duplicate manifest paths')
    rows = set(paths)
    for p in sorted(f for f in files if f.startswith(APP_PREFIX) and f not in rows):
        problems.append(f'tracked application file without a manifest row: {p}')
    for entry in manifest.get('entries', []):
        path, disposition = entry['path'], entry.get('disposition_current')
        if path in files:
            if disposition is not None:
                problems.append(f'{path}: tracked but carries absent-path disposition {disposition}')
            continue
        if disposition not in DISPOSITIONS:
            problems.append(f'{path}: absent without a valid disposition_current ({disposition!r})')
            continue
        if not entry.get('disposition_reason'):
            problems.append(f'{path}: disposition without a reason')
        if disposition == 'EXCLUDED_GENERATED_BUILD_PRODUCT' and '/build/lib/' not in path:
            problems.append(f'{path}: only build/lib products may be excluded as generated')
        if disposition == 'SUPERSEDED_BY_IMPLEMENTED_EQUIVALENT':
            targets = entry['candidate'].get('superseded_by') or []
            if not targets or any(t not in files for t in targets):
                problems.append(f'{path}: superseded_by targets missing or untracked: {targets}')
        if disposition == 'DEFERRED_ALTERNATE_LAYOUT':
            related = entry.get('related_implemented') or []
            if not related or any(t not in files for t in related):
                problems.append(f'{path}: related_implemented missing or untracked: {related}')
    current = manifest.get('current_inventory')
    expected = compute_current(repo, manifest)
    if current != expected:
        stale = sorted(k for k in set(expected) | set(current or {}) if (current or {}).get(k) != expected.get(k))
        problems.append(f'current_inventory is stale (run --write-current): {stale}')
    return problems


def receipt(repo: Path) -> dict:
    """Detached post-commit identity of the committed head; never written into the tracked tree."""
    if git(repo, 'status', '--porcelain', '--untracked-files=no').strip():
        raise InventoryError('commit first: the receipt describes a clean committed head')
    head = git(repo, 'rev-parse', 'HEAD').strip()
    committed = git(repo, 'show', f'{head}:{APP_PREFIX}IMPLEMENTATION_MANIFEST.json').encode('utf-8')
    return {
        'format': 'Permansson.App.InventoryReceipt.v1',
        'head_sha': head,
        'head_tree': git(repo, 'rev-parse', f'{head}^{{tree}}').strip(),
        'application_tree': git(repo, 'rev-parse', f'{head}:{APP_PREFIX.rstrip("/")}').strip(),
        'manifest_sha256': sha256(committed).hexdigest(),
        'current_inventory': json.loads(committed)['current_inventory'],
        'created_utc': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
        'not_recorded_here': ['synthetic merge commit', 'CI run and attempt identities', 'independent review'],
        'evidence_status': 'LOCAL_SELF_PRODUCED_IDENTITY_NOT_AUTHENTICATED',
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write-current', action='store_true')
    mode.add_argument('--receipt', type=Path)
    args = parser.parse_args(argv)
    try:
        repo = repository()
        manifest = load()
        if args.write_current:
            manifest['current_inventory'] = compute_current(repo, manifest)
            dump(manifest)
            print(json.dumps(manifest['current_inventory'], indent=2))
            return 0
        if args.receipt:
            args.receipt.write_text(json.dumps(receipt(repo), indent=2) + '\n', encoding='utf-8')
            print(json.dumps({'receipt': str(args.receipt)}))
            return 0
        problems = check(repo, manifest)
        print(json.dumps({'status': 'PASS' if not problems else 'FAIL', 'problems': problems}, indent=2))
        return 0 if not problems else 1
    except InventoryError as exc:
        print(json.dumps({'status': 'ERROR', 'error': str(exc)}), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
