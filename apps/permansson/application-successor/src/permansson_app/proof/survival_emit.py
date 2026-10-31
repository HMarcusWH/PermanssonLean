"""Checked killed-kernel survival comparison -> source-bound Lean *candidate*.

Only receipts that pass the independent survival checker are emitted. The
baseline and treated models are reflected as `FiniteWorldInput`s; both
complete survival tables are checked against `inducedMatrix` of their own
input, the treated model is proved to hold P/feasibility and the undeclared
generator fixed, and each comparison state's horizon effect is stated as a
difference of canonical-law survival probabilities. This is a finite-horizon
diagnostic: no exact invariance, GR/PR classification, QSD or forecast.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.finite_survival import parse_comparison
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.finite_survival import check_survival_receipt
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _nat_case, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.SurvivalLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedSurvival'
MAX_HORIZON=6
MAX_SOURCE_BYTES=512*1024


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('SURVIVAL_REIFY_INPUT','raw survival comparison and receipt required')
    checked=check_survival_receipt(raw,receipt)
    base,treated,states,region,selected,horizon=parse_comparison(raw)
    if not 1<=horizon<=MAX_HORIZON:
        raise AppError('SURVIVAL_REIFY_SCOPE',f'Lean survival reflection limited to 1..{MAX_HORIZON} transitions')
    base_lines,(ns,nx,na),base_ext=input_definition(base,'base')
    treated_lines,dims,treated_ext=input_definition(treated,'treated')
    if dims!=(ns,nx,na):
        raise AppError('SURVIVAL_REIFY_SCOPE','treated model must share the baseline dimensions')
    N=ns*nx
    assert list(states)==[(s,x) for s in base.strategic for x in base.world]
    target=raw['target']
    tables={}
    for key in ('baseline_survival','treated_survival'):
        tables[key]=[[exact_ratio(v,probability=True) for v in row] for row in receipt[key]]
    region_idx=[states.index(r) for r in region]
    compare=[states.index(s) for s in selected]

    dim=f'({ns} * {nx})'
    def table_def(name,rows):
        body=_nat_case('t',[_fin_case('y',[rational_expr(v) for v in row],N) for row in rows],'(0 : ℚ)')
        return f'def {name} : ℕ → Fin {dim} → ℚ := fun t y => {body}'
    lines=[
        'import PermanssonResearch.ApplicationBridge.MenuReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact killed-kernel survival comparison; application source candidate only.',
        f'    Comparison identity SHA-256: {receipt["comparison_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["certificate_sha256"]}',
        '    Finite-horizon diagnostic only. Infeasible P/U entries are normalized',
        '    Dirac extensions. A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ReverseSolver',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *base_lines,'',*treated_lines,'',
        f'/-- The treated model is a declared `{target}` intervention. -/',
        'theorem treated_held_fixed : HeldFixed base treated := by',
        '  unfold HeldFixed',
        '  simp only [base, treated]',
        '  decide +kernel',
    ]
    names=['treated_held_fixed']
    if target=='alpha':
        lines+=['theorem treated_update_held_fixed :',
                '    ∀ s x a xp sp, treated.update s x a xp sp = base.update s x a xp sp := by',
                '  simp only [base, treated]','  decide +kernel']
        names.append('treated_update_held_fixed')
    elif target=='U':
        lines+=['theorem treated_alpha_held_fixed :',
                '    ∀ s x a, treated.alpha s x a = base.alpha s x a := by',
                '  simp only [base, treated]','  decide +kernel']
        names.append('treated_alpha_held_fixed')
    lines+=['',
        f'def region : Finset (Fin {dim}) := {_finset(region_idx,N)}',
        f'def horizon : ℕ := {horizon}',
        table_def('baselineTable',tables['baseline_survival']),
        table_def('treatedTable',tables['treated_survival']),
        '',
        '/-- Kernel evaluation of both complete survival tables. -/',
        'theorem baseline_table_checked :',
        '    checkSurvivalTable (inducedMatrix base) region horizon baselineTable = true := by',
        '  decide +kernel',
        'theorem treated_table_checked :',
        '    checkSurvivalTable (inducedMatrix treated) region horizon treatedTable = true := by',
        '  decide +kernel','',
    ]
    names+=['baseline_table_checked','treated_table_checked']
    last_b,last_t=tables['baseline_survival'][-1],tables['treated_survival'][-1]
    for y in compare:
        d=last_b[y]-last_t[y]
        name=f'horizon_effect_{y}'
        names.append(name)
        surv=lambda m:(f'(1 - hittingValue (rationalTargetAsFrozen (exitTarget region))'
                       f' (rationalFiniteKernel (inducedMatrix {m})) ({y} : Fin {N}) horizon)')
        lines+=[f'/-- Baseline minus treated survival through the horizon from state {y}. -/',
                f'theorem {name} :',
                f'    {surv("base")} - {surv("treated")} = (({rational_expr(d)} : ℚ) : ℝ) := by',
                '  rw [← checked_survival_table_canonical (inducedMatrix base) region horizon',
                f'      baselineTable baseline_table_checked horizon le_rfl ({y} : Fin {N}),',
                '    ← checked_survival_table_canonical (inducedMatrix treated) region horizon',
                f'      treatedTable treated_table_checked horizon le_rfl ({y} : Fin {N})]',
                f'  have hb : baselineTable horizon ({y} : Fin {N}) = {rational_expr(last_b[y])} := by decide +kernel',
                f'  have ht : treatedTable horizon ({y} : Fin {N}) = {rational_expr(last_t[y])} := by decide +kernel',
                '  rw [hb, ht]',
                '  push_cast',
                '  norm_num','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('SURVIVAL_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['comparison_identity'],
        'receipt_sha256':checked['certificate_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'horizon':horizon,
                 'comparison_states':compare,'target':target,
                 'interpretation':'FINITE_HORIZON_DIAGNOSTIC_ONLY'},
        'p_u_infeasible_normalized_extensions':{'base':base_ext,'treated':treated_ext},
        'lean_status':'NOT_EXECUTED',
        'source_emitted':True,
        'compiler_evidence_authenticated':False,
        'independent_math_certification':False,
        'empirical_identification':False,
        'application_release_authorized':False,
    }
    return text,out


def emit_files(request_file:Path,receipt_file:Path,out_dir:Path)->dict:
    request_raw,request=strict_read(request_file)
    receipt_raw,receipt=strict_read(receipt_file)
    lean,metadata=emit_source(request,receipt)
    metadata['problem_bytes_sha256']=sha256(request_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedSurvival.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedSurvival.lean'),
            'metadata_file':str(destination/'source_candidate.json'),
            'lean_status':'NOT_EXECUTED','candidate_sha256':metadata['lean_source_sha256']}


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(emit_files(args.request,args.receipt,args.output),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
