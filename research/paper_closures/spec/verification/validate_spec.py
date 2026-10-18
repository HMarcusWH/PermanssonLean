#!/usr/bin/env python3
"""Validate this paper-specification package's structure and literal tables.

This is not a proof checker for the mathematical prose and does not run Lean.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def strict_json(path: Path):
    def pairs(values):
        out = {}
        for key, value in values:
            require(key not in out, f'Duplicate JSON key: {key}')
            out[key] = value
        return out
    return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=pairs)


def validate(root: Path) -> dict:
    root = root.resolve()
    registry = strict_json(root / 'registries/closure_contracts.json')
    atlas = strict_json(root / 'sources/input_atlas.json')
    records = registry['contracts']
    ids = [r['atlas_id'] for r in records]
    require(len(ids) == 42 and len(set(ids)) == 42, 'Need 42 unique atlas entries')
    require(set(ids) == {r['id'] for r in atlas['entries']}, 'Atlas coverage differs')
    graph = {}
    for r in records:
        p = (root / r['chapter']).resolve()
        require(p.is_relative_to(root) and p.is_file(), 'Invalid chapter reference')
        text = p.read_text(encoding='utf-8')
        require(r['formal_status'] == 'NOT_LEAN_VERIFIED', 'Unexpected proof promotion')
        require(bool(r['selected_scope']) and bool(r['residual_scope']), 'Missing scope')
        for ident in r['paper_theorem_ids']:
            require(ident in text, 'Missing paper theorem ' + ident)
        for p in r['proposed_new_modules']:
            require(p.startswith('PermanssonResearch/') and p.endswith('.lean')
                    and '..' not in Path(p).parts, 'Unsafe proposed source path')
        graph[r['atlas_id']] = r['selected_build_dependencies']
    active, done = set(), set()
    def visit(ident):
        require(ident in graph, 'Unknown dependency ' + ident)
        if ident in done:
            return
        require(ident not in active, 'Dependency cycle at ' + ident)
        active.add(ident)
        for other in graph[ident]:
            visit(other)
        active.remove(ident)
        done.add(ident)
    for ident in graph:
        visit(ident)
    cases = strict_json(root / 'registries/acceptance_tests.json')['cases']
    require(len({r['id'] for r in cases}) == len(cases), 'Duplicate acceptance ID')
    for r in cases:
        require(set(r['atlas_ids']) <= set(ids), 'Unknown acceptance atlas ID')
        require(r['status'] == 'REQUIRED_NOT_AN_EXECUTED_LEAN_TEST', 'Test-status promotion')
    source = strict_json(root / 'sources/source_register.json')['sources']
    require(len({r['path'] for r in source}) == len(source), 'Duplicate source path')
    for r in source:
        require(bool(re.fullmatch('[0-9a-f]{64}', r['sha256'])), 'Malformed source hash')
        require(bool(re.fullmatch('[0-9a-f]{40}', r['git_blob_sha1'])), 'Malformed blob ID')
    module_path = root / 'verification/exact_checks.py'
    module_spec = importlib.util.spec_from_file_location('paper_exact_checks', module_path)
    require(module_spec is not None and module_spec.loader is not None, 'Missing table checker')
    module = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(module)
    table_path = root / 'certificates/x1_exact_tables.json'
    module.validate_candidate_tables(strict_json(table_path))
    execution = strict_json(root / 'certificates/exact_check_report.json')
    require(execution['status'] == 'PASS' and execution['failures'] == 0
            and execution['errors'] == 0 and execution['skipped'] == 0,
            'Supplied finite execution did not pass')
    require(execution['x1_table_sha256'] == hashlib.sha256(table_path.read_bytes()).hexdigest(),
            'Table differs from execution receipt')
    checked = 0
    manifest_path = root / 'MANIFEST.json'
    if manifest_path.exists():
        manifest = strict_json(manifest_path)
        names = []
        for r in manifest['files']:
            p = (root / r['path']).resolve()
            require(p.is_relative_to(root) and p.is_file(), 'Manifest path absent or invalid')
            raw = p.read_bytes()
            require(len(raw) == r['bytes'] and hashlib.sha256(raw).hexdigest() == r['sha256'],
                    'Package file hash differs: ' + r['path'])
            names.append(r['path'])
        require(len(names) == len(set(names)), 'Duplicate manifest path')
        actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
        expected = set(names) | {'MANIFEST.json', 'MANIFEST.sha256'}
        require(actual == expected, 'Unexpected or missing delivered file')
        sidecar = (root / 'MANIFEST.sha256').read_text().split()[0]
        require(sidecar == hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
                'Manifest sidecar differs')
        checked = len(names)
    return {'status': 'PASS', 'atlas_entries': 42, 'acceptance_requirements': len(cases),
            'source_records': len(source), 'new_formal_proofs_claimed': 0,
            'dependency_graph': 'acyclic', 'literal_tables': 'checked',
            'observed_finite_test_methods': execution['test_methods_run'],
            'manifest_files_checked': checked,
            'boundary': 'Package structure/arithmetic, not verification of all prose proofs or Lean.'}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(validate(args.root), indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
