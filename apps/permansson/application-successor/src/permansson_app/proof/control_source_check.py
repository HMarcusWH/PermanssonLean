"""Independent byte/semantic binding of Bellman control-table Lean candidates.

This re-derives the candidate from the original problem and receipt bytes and
compares metadata and exact Lean bytes. It is NOT a compiler, trusted source
signer, proof kernel or release attestation.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.hitting import parse_hitting_problem
from ..errors import AppError
from ..identity import canonical_bytes
from ..strict_json import strict_read
from .control_emit import emit_source,MAX_SOURCE_BYTES


def check_files(problem_path:Path,receipt_path:Path,directory:Path)->dict:
    root=directory.absolute()
    if not root.is_dir() or root.is_symlink() or any(p.is_symlink() for p in root.parents):
        raise AppError('CONTROL_REIFY_PATH','candidate must be an ordinary non-symlinked directory')
    expected_set={'ReifiedControlTable.lean','source_candidate.json'}
    files=list(root.iterdir())
    if len(files)!=2 or {p.name for p in files}!=expected_set or any(not p.is_file() or p.is_symlink() for p in files):
        raise AppError('CONTROL_REIFY_PATH','candidate directory has missing/extra/symlinked contents')
    problem_raw,problem=strict_read(problem_path)
    receipt_raw,receipt=strict_read(receipt_path)
    lean,expected=emit_source(parse_hitting_problem(problem),receipt)
    expected['problem_bytes_sha256']=sha256(problem_raw).hexdigest()
    expected['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    actual_raw,actual=strict_read(root/'source_candidate.json')
    if type(actual) is not dict or actual!=expected or actual_raw!=canonical_bytes(expected)+b'\n':
        raise AppError('CONTROL_REIFY_RECEIPT','candidate metadata does not match original problem and receipt bytes')
    with (root/'ReifiedControlTable.lean').open('rb') as stream:
        current=stream.read(MAX_SOURCE_BYTES+1)
    if len(current)>MAX_SOURCE_BYTES or current!=lean.encode('utf-8'):
        raise AppError('CONTROL_REIFY_SOURCE','candidate Lean bytes differ from verified original inputs')
    return {'format':'Permansson.App.ControlTableSourceRecheck.v1',
            'status':'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF',
            'problem_semantic_identity':expected['problem_semantic_identity'],
            'receipt_sha256':expected['receipt_sha256'],
            'lean_source_sha256':expected['lean_source_sha256'],
            'theorem_names':list(expected['theorem_names']),
            'compiler_evidence_authenticated':False,
            'lean_status':'NOT_EXECUTED',
            'independent_math_certification':False,
            'application_release_authorized':False}


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('candidate',type=Path)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(check_files(args.problem,args.receipt,args.candidate),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
