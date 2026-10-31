"""Checked frozen-menu receipt -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent menu checker are emitted. The
baseline and every listed intervention are reflected as `FiniteWorldInput`s;
each member is the α/P/U-induced matrix (`inducedMatrix`) of its own input,
with `HeldFixed` (feasible actions and world kernel P) and the undeclared
generator (α or U) proved equal to the baseline. Optimality is over the
declared menu only. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.menu import _get
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.menu import check_menu
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.MenuLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedMenu'
MAX_MEMBERS=4
MAX_HORIZON=6
MAX_SOURCE_BYTES=512*1024


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('MENU_REIFY_INPUT','raw frozen-menu request and receipt required')
    checked=check_menu(raw,receipt)
    base,states,region,start,horizon,menu=_get(raw)
    if not 1<=len(menu)<=MAX_MEMBERS or not 1<=horizon<=MAX_HORIZON:
        raise AppError('MENU_REIFY_SCOPE',f'Lean menu reflection limited to 1..{MAX_MEMBERS} members and 1..{MAX_HORIZON} transitions')
    base_lines,(ns,nx,na),base_ext=input_definition(base,'base')
    member_lines=[];extensions={'base':base_ext}
    for i,(ident,treat,target) in enumerate(menu):
        lines_i,dims,ext=input_definition(treat,f'member_{i}')
        if dims!=(ns,nx,na):
            raise AppError('MENU_REIFY_SCOPE','menu members must share the baseline dimensions')
        member_lines.append(lines_i);extensions[ident]=ext
    N=ns*nx
    assert list(states)==[(s,x) for s in base.strategic for x in base.world]
    k=len(menu)
    values=[exact_result(item['value'],probability=True) for item in receipt['menu_values']]
    ids=[ident for ident,_,_ in menu]
    tied=[ids.index(t) for t in receipt['attaining_ids']]
    survival=raw['value_type']=='survival_horizon'
    maximize=raw['direction']=='max'
    region_idx=[states.index(r) for r in region]
    start_idx=states.index(start)
    baseline_survival=exact_result(receipt['baseline_survival'],probability=True)

    dim=f'({ns} * {nx})'
    members=_fin_case('i',[f'inducedMatrix member_{i}' for i in range(k)],k)
    lines=[
        'import PermanssonResearch.ApplicationBridge.MenuReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact frozen intervention menu; application source candidate only.',
        f'    Request identity SHA-256: {checked["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Infeasible P/U entries are normalized Dirac extensions.',
        '    Optimality is over the declared menu only.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ReverseSolver',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *base_lines,'',
    ]
    names=[]
    for i,(ident,treat,target) in enumerate(menu):
        lines+=[*member_lines[i],'',
                f'/-- Listed intervention `{ident}` (declared target: {target}). -/',
                f'theorem member_{i}_held_fixed : HeldFixed base member_{i} := by',
                '  unfold HeldFixed',
                f'  simp only [base, member_{i}]',
                '  decide +kernel']
        names.append(f'member_{i}_held_fixed')
        if target=='alpha':
            lines+=[f'theorem member_{i}_update_held_fixed :',
                    f'    ∀ s x a xp sp, member_{i}.update s x a xp sp = base.update s x a xp sp := by',
                    f'  simp only [base, member_{i}]',
                    '  decide +kernel']
            names.append(f'member_{i}_update_held_fixed')
        elif target=='U':
            lines+=[f'theorem member_{i}_alpha_held_fixed :',
                    f'    ∀ s x a, member_{i}.alpha s x a = base.alpha s x a := by',
                    f'  simp only [base, member_{i}]',
                    '  decide +kernel']
            names.append(f'member_{i}_alpha_held_fixed')
        lines.append('')
    lines+=[
        f'def members : Fin {k} → RationalMarkovMatrix {dim} := fun i => {members}',
        f'def region : Finset (Fin {dim}) := {_finset(region_idx,N)}',
        f'def start : Fin {dim} := ({start_idx} : Fin {N})',
        f'def horizon : ℕ := {horizon}',
        f'def survival : Bool := {"true" if survival else "false"}',
        f'def maximize : Bool := {"true" if maximize else "false"}',
        f'def values : Fin {k} → ℚ := fun i => {_fin_case("i",[rational_expr(v) for v in values],k)}',
        f'def tied : Finset (Fin {k}) := {_finset(sorted(tied),k)}',
        '',
        '/-- Kernel evaluation: every listed value is exact and `tied` is exactly',
        '    the set of listed optima in the declared direction. -/',
        'theorem receipt_checked :',
        '    checkMenuReceipt members region horizon start survival maximize values tied = true := by',
        '  decide +kernel','',
        'theorem tied_exactly_listed_optima :',
        '    tied.Nonempty ∧ ∀ i, i ∈ tied ↔ ∀ j, atLeastAsGood maximize',
        '      (menuObjective survival (members i) region horizon start)',
        '      (menuObjective survival (members j) region horizon start) :=',
        '  checked_tied_exactly_listed_optima members region horizon start survival maximize',
        '    values tied receipt_checked','',
        '/-- The baseline (no intervention) survival value. -/',
        'theorem baseline_survival :',
        f'    1 - rationalHittingValue (inducedMatrix base) (exitTarget region) horizon start = {rational_expr(baseline_survival)} := by',
        '  decide +kernel','',
    ]
    names+=['receipt_checked','tied_exactly_listed_optima','baseline_survival']
    event=('1 - hittingValue (rationalTargetAsFrozen (exitTarget region))' if survival
           else 'hittingValue (rationalTargetAsFrozen (exitTarget region))')
    for i,v in enumerate(values):
        name=f'member_value_{i}'
        names.append(name)
        lines+=[f'/-- Actual canonical path-law probability for listed member `{ids[i]}`. -/',
                f'theorem {name} :',
                f'    (({rational_expr(v)} : ℚ) : ℝ) =',
                f'      {event} (rationalFiniteKernel (members {i})) start horizon := by',
                f'  have hv : values {i} = {rational_expr(v)} := by decide +kernel',
                '  have h := checked_value_canonical members region horizon start survival maximize',
                f'    values tied receipt_checked {i}',
                '  rw [hv] at h',
                '  simpa only [survival, Bool.false_eq_true, ↓reduceIte] using h','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('MENU_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':checked['request_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'members':k,'horizon':horizon,
                 'value_type':raw['value_type'],'direction':raw['direction'],
                 'optimality':'DECLARED_MENU_ONLY'},
        'member_ids':ids,
        'p_u_infeasible_normalized_extensions':extensions,
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
    receipt_raw,receipt=read_result(receipt_file)
    lean,metadata=emit_source(request,receipt)
    metadata['problem_bytes_sha256']=sha256(request_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedMenu.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedMenu.lean'),
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
