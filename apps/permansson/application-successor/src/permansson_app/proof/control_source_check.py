"""Independent byte/semantic binding of finite-control Lean candidates.

This re-derives a candidate from the original problem and receipt bytes and
compares metadata and exact Lean bytes. It is NOT a compiler, trusted source
signer, proof kernel or release attestation. It covers every application
bridge emitter (Bellman control table, safety core, residence, frozen menu,
killed-kernel survival, occupation, first-exit routing, nonlinear objective,
perturbation, typed quotient, patch grammar, risk flow and robust nature),
which share one layout. The exit family also binds the original region bytes.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.hitting import parse_hitting_problem
from ..engines.safety import parse_safety_problem
from ..errors import AppError
from ..identity import canonical_bytes
from ..strict_json import strict_read
from . import (control_emit, exit_emit, flow_emit, grammar_emit, menu_emit, nonlinear_emit,
               occupation_emit, perturbation_emit, quotient_emit, residence_emit,
               safety_emit, survival_emit)

# family -> (parser, emitter module, Lean file name, error-code prefix, recheck format)
FAMILIES={
    'control-table':(parse_hitting_problem,control_emit,'ReifiedControlTable.lean','CONTROL_REIFY',
                     'Permansson.App.ControlTableSourceRecheck.v1'),
    'safety-core':(parse_safety_problem,safety_emit,'ReifiedSafetyCore.lean','SAFETY_REIFY',
                   'Permansson.App.SafetyCoreSourceRecheck.v1'),
    # The residence emitter re-parses and rechecks the raw request itself.
    'residence':(lambda raw:raw,residence_emit,'ReifiedResidence.lean','RESIDENCE_REIFY',
                 'Permansson.App.ResidenceSourceRecheck.v1'),
    'menu':(lambda raw:raw,menu_emit,'ReifiedMenu.lean','MENU_REIFY',
            'Permansson.App.MenuSourceRecheck.v1'),
    'survival':(lambda raw:raw,survival_emit,'ReifiedSurvival.lean','SURVIVAL_REIFY',
                'Permansson.App.SurvivalSourceRecheck.v1'),
    # The occupation emitter parses the raw finite model itself.
    'occupation':(lambda raw:raw,occupation_emit,'ReifiedOccupation.lean','OCCUPATION_REIFY',
                  'Permansson.App.OccupationSourceRecheck.v1'),
    # The exit emitter parses the raw model and region itself.
    'exit':(lambda raw:raw,exit_emit,'ReifiedExit.lean','EXIT_REIFY',
            'Permansson.App.ExitSourceRecheck.v1'),
    'nonlinear':(lambda raw:raw,nonlinear_emit,'ReifiedNonlinear.lean','NONLINEAR_REIFY',
                 'Permansson.App.NonlinearSourceRecheck.v1'),
    'perturbation':(lambda raw:raw,perturbation_emit,'ReifiedPerturbation.lean','PERTURBATION_REIFY',
                    'Permansson.App.PerturbationSourceRecheck.v1'),
    'quotient':(lambda raw:raw,quotient_emit,'ReifiedQuotient.lean','QUOTIENT_REIFY',
                'Permansson.App.QuotientSourceRecheck.v1'),
    'grammar':(lambda raw:raw,grammar_emit,'ReifiedGrammar.lean','GRAMMAR_REIFY',
               'Permansson.App.GrammarSourceRecheck.v1'),
    'flow':(lambda raw:raw,flow_emit,'ReifiedFlow.lean','FLOW_REIFY',
            'Permansson.App.FlowSourceRecheck.v1'),
}
# Families whose source also depends on a separate region file.
REGION_FAMILIES={'exit'}


def check_family(family:str,problem_path:Path,receipt_path:Path,directory:Path,
                 region_path:Path|None=None)->dict:
    if family not in FAMILIES:
        raise AppError('REIFY_FAMILY','unknown source-candidate family')
    if (region_path is not None)!=(family in REGION_FAMILIES):
        raise AppError('REIFY_FAMILY','a region file is required exactly for region families')
    parse,emitter,lean_name,code,fmt=FAMILIES[family]
    root=directory.absolute()
    if not root.is_dir() or root.is_symlink() or any(p.is_symlink() for p in root.parents):
        raise AppError(code+'_PATH','candidate must be an ordinary non-symlinked directory')
    expected_set={lean_name,'source_candidate.json'}
    files=list(root.iterdir())
    if len(files)!=2 or {p.name for p in files}!=expected_set or any(not p.is_file() or p.is_symlink() for p in files):
        raise AppError(code+'_PATH','candidate directory has missing/extra/symlinked contents')
    problem_raw,problem=strict_read(problem_path)
    receipt_raw,receipt=strict_read(receipt_path)
    if region_path is None:
        lean,expected=emitter.emit_source(parse(problem),receipt)
        expected['problem_bytes_sha256']=sha256(problem_raw).hexdigest()
    else:
        region_raw,region=strict_read(region_path)
        lean,expected=emitter.emit_source(parse(problem),region,receipt)
        expected['problem_bytes_sha256']=sha256(problem_raw).hexdigest()
        expected['region_bytes_sha256']=sha256(region_raw).hexdigest()
    expected['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    actual_raw,actual=strict_read(root/'source_candidate.json')
    if type(actual) is not dict or actual!=expected or actual_raw!=canonical_bytes(expected)+b'\n':
        raise AppError(code+'_RECEIPT','candidate metadata does not match original problem and receipt bytes')
    with (root/lean_name).open('rb') as stream:
        current=stream.read(emitter.MAX_SOURCE_BYTES+1)
    if len(current)>emitter.MAX_SOURCE_BYTES or current!=lean.encode('utf-8'):
        raise AppError(code+'_SOURCE','candidate Lean bytes differ from verified original inputs')
    return {'format':fmt,
            'status':'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF',
            'problem_semantic_identity':expected['problem_semantic_identity'],
            'receipt_sha256':expected['receipt_sha256'],
            'lean_source_sha256':expected['lean_source_sha256'],
            'theorem_names':list(expected['theorem_names']),
            'compiler_evidence_authenticated':False,
            'lean_status':'NOT_EXECUTED',
            'independent_math_certification':False,
            'application_release_authorized':False}


def check_files(problem_path:Path,receipt_path:Path,directory:Path)->dict:
    return check_family('control-table',problem_path,receipt_path,directory)


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('candidate',type=Path)
    parser.add_argument('--family',choices=sorted(FAMILIES),default='control-table')
    parser.add_argument('--region',type=Path,default=None)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(check_family(args.family,args.problem,args.receipt,args.candidate,
                                      args.region),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
