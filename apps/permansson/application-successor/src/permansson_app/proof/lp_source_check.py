"""Independent byte/semantic binding of exact LP Lean source candidates.

This checks input, original LP normalization, witness identity and exact Lean
bytes. It is NOT a compiler, trusted source signer, proof kernel or release
attestation. A matching self-authored digest cannot grant proof authority.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.lp_types import parse_lp
from ..errors import AppError
from ..identity import canonical_bytes
from ..strict_json import strict_read
from .lp_emit import emit_source,MAX_SOURCE_BYTES


def check_files(model_path:Path,receipt_path:Path,directory:Path)->dict:
    root=directory.absolute()
    if not root.is_dir() or root.is_symlink() or any(p.is_symlink() for p in root.parents):
        raise AppError('LP_REIFY_PATH','candidate must be an ordinary non-symlinked directory')
    expected_set={'ReifiedLP.lean','source_candidate.json'}
    files=list(root.iterdir())
    if len(files)!=2 or {p.name for p in files}!=expected_set or any(not p.is_file() or p.is_symlink() for p in files):
        raise AppError('LP_REIFY_PATH','candidate directory has missing/extra/symlinked contents')
    model_raw,model=strict_read(model_path)
    receipt_raw,receipt=strict_read(receipt_path)
    lean,expected=emit_source(parse_lp(model),receipt)
    expected['model_bytes_sha256']=sha256(model_raw).hexdigest()
    expected['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    actual_raw,actual=strict_read(root/'source_candidate.json')
    if type(actual) is not dict or actual!=expected or actual_raw!=canonical_bytes(expected)+b'\n':
        raise AppError('LP_REIFY_RECEIPT','candidate metadata does not match original LP and certificate bytes')
    with (root/'ReifiedLP.lean').open('rb') as stream:
        current=stream.read(MAX_SOURCE_BYTES+1)
    if len(current)>MAX_SOURCE_BYTES or current!=lean.encode('utf-8'):
        raise AppError('LP_REIFY_SOURCE','candidate Lean bytes differ from verified original inputs')
    return {'format':'Permansson.App.LPSourceRecheck.v1',
            'status':'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF',
            'lp_semantic_identity':expected['lp_semantic_identity'],
            'certificate_sha256':expected['certificate_sha256'],
            'lean_source_sha256':expected['lean_source_sha256'],
            'theorem_names':list(expected['theorem_names']),
            'compiler_evidence_authenticated':False,
            'lean_status':'NOT_EXECUTED',
            'independent_math_certification':False,
            'application_release_authorized':False}


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('candidate',type=Path)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(check_files(args.model,args.receipt,args.candidate),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
