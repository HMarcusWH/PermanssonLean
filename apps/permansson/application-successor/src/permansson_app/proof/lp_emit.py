"""Source-bound exact LP certificate -> concrete Lean theorem *candidate*.

Only independently checked original LP optimal/Farkas receipts can be emitted.
Theorems prove soundness for the exact affine-normalized LP over REAL decision
vectors. Emission never equals compiler replay, scientific certification or
release acceptance; not finding an LP candidate is never infeasibility.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.lp_types import LP, parse_lp
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.lp import OPTIMAL, INFEASIBLE, check_lp_certificate, check_farkas_certificate
from ..strict_json import strict_read
from .finite_emit import rational_expr

FORMAT='Permansson.App.LPLeanSourceCandidate.v1'
MAX_VAR=3
MAX_CONSTRAINT=6
MAX_SOURCE_BYTES=128*1024
MODULE='PermanssonResearch.ApplicationBridge.ReifiedLP'


def _fin_case(variable:str, values:tuple[str,...])->str:
    if not 1 <= len(values) <= MAX_CONSTRAINT:
        raise AppError('LP_REIFY_SCOPE','finite LP table length unsupported')
    n=len(values)
    result=values[-1]
    for k in range(n-2,-1,-1):
        result=f'(if {variable} = ({k} : Fin {n}) then {values[k]} else {result})'
    return result


def _shape(lp:LP)->tuple[int,int]:
    n,m=len(lp.variables),len(lp.A)
    if not (1 <= n <= MAX_VAR and 1 <= m <= MAX_CONSTRAINT):
        raise AppError('LP_REIFY_SCOPE','LP reflection limited to 1..3 variables and 1..6 normalized rows')
    if any(len(row)!=n for row in lp.A) or len(lp.c)!=n or len(lp.b)!=m:
        raise AppError('LP_REIFY_SCOPE','original normalized LP dimensions disagree')
    return m,n


def emit_source(lp:LP,receipt:dict)->tuple[str,dict]:
    if type(lp) is not LP or type(receipt) is not dict:
        raise AppError('LP_REIFY_INPUT','typed LP and raw exact certificate required')
    m,n=_shape(lp)
    typ=receipt.get('format')
    if typ==OPTIMAL:
        checked=check_lp_certificate(lp,receipt)
        x=tuple(exact_ratio(s)-lo for s,lo in zip(receipt['primal'],lp.lower))
        y=tuple(exact_ratio(s) for s in receipt['dual'])
        assert len(x)==n and len(y)==m
        family='PRIMAL_DUAL_OPTIMUM'
    elif typ==INFEASIBLE:
        checked=check_farkas_certificate(lp,receipt)
        y=tuple(exact_ratio(s) for s in receipt['multiplier'])
        x=None
        assert len(y)==m
        family='FARKAS_INFEASIBILITY'
    else:
        raise AppError('LP_REIFY_INPUT','expected exact optimality or Farkas witness')
    def vec(values):return _fin_case('j',tuple(rational_expr(t) for t in values))
    matrix=_fin_case('i',tuple(_fin_case('j',tuple(rational_expr(t) for t in row)) for row in lp.A))
    bounds=_fin_case('i',tuple(rational_expr(t) for t in lp.b))
    coefs=vec(lp.c)
    multipliers=_fin_case('i',tuple(rational_expr(t) for t in y))
    source=[
        'import PermanssonResearch.ApplicationBridge.LinearProgramReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact LP certificate; application source candidate only.',
        f'    Original normalized LP semantic SHA-256: {lp.semantic_id()["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["certificate_sha256"]}',
        '    Lower-bound shifts and negative objective-sense normalization',
        '    were checked by the application checker before source emission.',
        '    A compiler result and independent review are NOT asserted. -/','',
        'namespace PermanssonResearch.ApplicationBridge.ReifiedLP',
        'open PermanssonResearch.ApplicationBridge.LinearProgramReceipt',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        f'def A : Fin {m} → Fin {n} → ℚ := fun i j => {matrix}',
        f'def b : Fin {m} → ℚ := fun i => {bounds}',
        f'def c : Fin {n} → ℚ := fun j => {coefs}',
        f'def dual : Fin {m} → ℚ := fun i => {multipliers}',
    ]
    names=[]
    if family=='PRIMAL_DUAL_OPTIMUM':
        source.extend([
            f'def primal : Fin {n} → ℚ := fun j => {vec(x)}','',
            'theorem primal_checked : primalFeasible A b primal := by decide +kernel',
            'theorem dual_checked : dualFeasible A c dual := by decide +kernel',
            'theorem gap_checked : objective c primal = dualBound b dual := by decide +kernel',
            '',
            '/-- Global optimum over real-valued feasible vectors, not just rational',
            '    candidate vertices. The preconditions have executable proofs above. -/',
            f'theorem real_optimal : ∀ z : Fin {n} → ℝ,',
            '    (∀ j, 0 ≤ z j) →',
            f'    (∀ i, (∑ j : Fin {n}, (A i j : ℝ) * z j) ≤ (b i : ℝ)) →',
            f'    (∑ j : Fin {n}, (c j : ℝ) * z j) ≤',
            f'      (∑ j : Fin {n}, (c j : ℝ) * (primal j : ℝ)) :=',
            '  optimum_over_reals A b c primal dual primal_checked dual_checked gap_checked',''
        ])
        names=['primal_checked','dual_checked','gap_checked','real_optimal']
    else:
        source.extend([
            '',
            'theorem multiplier_nonnegative : ∀ i, 0 ≤ dual i := by decide +kernel',
            f'theorem multiplier_column_nonnegative :',
            f'    ∀ j, 0 ≤ ∑ i : Fin {m}, dual i * A i j := by decide +kernel',
            f'theorem multiplier_bound_negative :',
            f'    (∑ i : Fin {m}, dual i * b i) < 0 := by decide +kernel',
            '',
            '/-- Farkas witness excludes every real vector meeting the original',
            '    normalized constraints, not merely enumerated vertices. -/',
            f'theorem real_infeasible : ¬ ∃ z : Fin {n} → ℝ,',
            '    (∀ j, 0 ≤ z j) ∧',
            f'    (∀ i, (∑ j : Fin {n}, (A i j : ℝ) * z j) ≤ (b i : ℝ)) :=',
            '  infeasible_over_reals A b dual multiplier_nonnegative',
            '    multiplier_column_nonnegative multiplier_bound_negative',''
        ])
        names=['multiplier_nonnegative','multiplier_column_nonnegative',
               'multiplier_bound_negative','real_infeasible']
    source.append('end PermanssonResearch.ApplicationBridge.ReifiedLP')
    source.append('')
    for name in names:
        source.append(f'#print axioms {MODULE}.{name}')
    source.append('')
    text='\n'.join(source)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('LP_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'lp_semantic_identity':lp.semantic_id(),
        'certificate_sha256':checked['certificate_sha256'],
        'certificate_family':family,
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'normalized_constraints':m,'variables':n},
        'normalization':{'original_sense':'maximize' if lp.maximize else 'minimize',
                         'lower_bounds':[str(v) for v in lp.lower],
                         'objective_offset':str(lp.offset),
                         'row_labels':list(lp.row_labels)},
        'lean_status':'NOT_EXECUTED',
        'source_emitted':True,
        'compiler_evidence_authenticated':False,
        'independent_math_certification':False,
        'empirical_identification':False,
        'application_release_authorized':False,
    }
    return text,out


def _new_dir(target:Path)->Path:
    path=target.absolute()
    if path.exists() or path.is_symlink() or any(p.is_symlink() for p in path.parents):
        raise AppError('OUTPUT_SCOPE','new non-symlinked output directory required')
    path.mkdir(parents=True,exist_ok=False)
    return path


def emit_files(model_file:Path,receipt_file:Path,out_dir:Path)->dict:
    model_raw,model=strict_read(model_file)
    receipt_raw,receipt=strict_read(receipt_file)
    lean,metadata=emit_source(parse_lp(model),receipt)
    metadata['model_bytes_sha256']=sha256(model_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedLP.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedLP.lean'),
            'metadata_file':str(destination/'source_candidate.json'),
            'lean_status':'NOT_EXECUTED','candidate_sha256':metadata['lean_source_sha256']}


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(emit_files(args.model,args.receipt,args.output),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
