"""Recheck *source identity* of a finite-world Lean fixture, not Lean proof.

This intentionally rerenders the trusted generator in addition to checking
both content hashes and exact input bytes. Matching bytes do not establish
independent implementation correctness or a successful Lean theorem check.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..errors import AppError
from ..finite_world import parse_finite_world
from ..identity import canonical_bytes
from ..strict_json import strict_read
from .finite_emit import emit_source, MAX_SOURCE_BYTES


def check_files(model_path: Path, candidate_dir: Path) -> dict:
    directory = candidate_dir.absolute()
    if (not directory.is_dir() or directory.is_symlink() or
            any(parent.is_symlink() for parent in directory.parents)):
        raise AppError('REIFICATION_PATH', 'candidate must be an ordinary directory')
    path = directory / 'ReifiedFiniteWorld.lean'
    receipt_path = directory / 'source_candidate.json'
    if path.is_symlink() or not path.is_file():
        raise AppError('REIFICATION_PATH', 'missing or symlinked Lean source')
    try:
        with path.open('rb') as stream:
            source_bytes = stream.read(MAX_SOURCE_BYTES + 1)
    except OSError as exc:
        raise AppError('REIFICATION_PATH', 'cannot read Lean source') from exc
    if len(source_bytes) > MAX_SOURCE_BYTES:
        raise AppError('REIFICATION_SCOPE', 'candidate source exceeds byte bound')
    receipt_bytes, supplied = strict_read(receipt_path)
    if type(supplied) is not dict:
        raise AppError('REIFICATION_RECEIPT', 'candidate metadata must be object')
    model_raw, model_doc = strict_read(model_path)
    generated, expected = emit_source(parse_finite_world(model_doc))
    expected['source_bytes_sha256'] = sha256(model_raw).hexdigest()
    if (supplied != expected or receipt_bytes != canonical_bytes(expected)+b'\n'):
        raise AppError('REIFICATION_RECEIPT', 'candidate metadata differs from exact source/model identity')
    if source_bytes != generated.encode('utf-8'):
        raise AppError('REIFICATION_SOURCE', 'candidate Lean text differs from reflected model')
    return {
        'format': 'Permansson.App.FiniteWorldSourceRecheck.v1',
        'status': 'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF',
        'source_sha256': expected['lean_source_sha256'],
        'input_bytes_sha256': expected['source_bytes_sha256'],
        'theorem_count': len(expected['theorem_names']),
        'infeasible_extension_count': len(expected['p_u_infeasible_normalized_extensions']),
        'lean_status': 'NOT_EXECUTED',
        'independent_axiom_audit': False,
        'scientific_claims_verified': False,
        'release_authorized': False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model', type=Path)
    parser.add_argument('candidate', type=Path)
    args = parser.parse_args(argv)
    try:
        print(json.dumps(check_files(args.model, args.candidate), sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok': False, 'error': {'code': exc.code, 'message': str(exc)}}), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
