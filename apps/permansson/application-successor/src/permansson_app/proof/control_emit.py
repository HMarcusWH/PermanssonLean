"""Checked finite Bellman table -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent application checker are emitted. The
Lean control system is constructed from the reflected alpha/P/U input with
`boundControlSystem`, so the theorems concern the submitted source model and
its declared feasible-action relation, not a separately supplied matrix.
Emission is never compiler replay, independent certification, empirical
identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.hitting import HittingProblem, parse_hitting_problem
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.control import check_bellman
from ..strict_json import strict_read, read_result
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.ControlTableLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedControlTable'
MAX_HORIZON=6
MAX_SOURCE_BYTES=256*1024
# Lean `chosen t` is applied with t+1 transitions remaining. At terminal
# (goal/forbidden) states the receipt selects no action; the checked table
# still requires an admitted control there, so the first declared feasible
# action is reflected. It carries no policy or source authority.
TERMINAL_FILL='first_declared_feasible_action'


def _fin_case(variable:str,values:list[str],dimension:int)->str:
    result=values[-1]
    for k in range(len(values)-2,-1,-1):
        result=f'(if {variable} = ({k} : Fin {dimension}) then {values[k]} else {result})'
    return result


def _nat_case(variable:str,values:list[str],default:str)->str:
    result=default
    for k in range(len(values)-1,-1,-1):
        result=f'(if {variable} = {k} then {values[k]} else {result})'
    return result


def _finset(indices,dimension:int)->str:
    if not indices:
        return f'(∅ : Finset (Fin {dimension}))'
    return '({'+', '.join(str(i) for i in indices)+'} : Finset (Fin '+str(dimension)+'))'


def bound_system_lines(feasible:list[list[int]],ns:int,nx:int,na:int)->list[str]:
    """`options`, `options_exact`, `states_pos` and `sys := boundControlSystem input ...`.

    Shared by emitters whose controls are the reflected feasible actions.
    """
    N=ns*nx
    dim=f'({ns} * {nx})'
    options=_fin_case('y',[_finset(indices,na) for indices in feasible],N)
    return [
        f'def options : Fin {dim} → Finset (Fin {na}) := fun y => {options}',
        '',
        '/-- Admitted controls are exactly the reflected feasible actions. -/',
        'theorem options_exact : AdmittedExactly input options := by',
        '  unfold AdmittedExactly',
        '  simp only [input]',
        '  decide',
        f'theorem states_pos : 0 < {ns} * {nx} := by norm_num','',
        f'def sys : FiniteControlSystem (Fin {na}) {dim} :=',
        '  boundControlSystem input options options_exact states_pos','',
    ]


def emit_source(problem:HittingProblem,receipt:dict)->tuple[str,dict]:
    if type(problem) is not HittingProblem or type(receipt) is not dict:
        raise AppError('CONTROL_REIFY_INPUT','parsed hitting problem and raw Bellman receipt required')
    checked=check_bellman(problem,receipt)
    model=problem.world
    input_lines,(ns,nx,na),extensions=input_definition(model)
    H=problem.horizon
    if not 1<=H<=MAX_HORIZON:
        raise AppError('CONTROL_REIFY_SCOPE',f'Lean control-table reflection limited to 1..{MAX_HORIZON} transitions')
    pairs=[(s,x) for s in model.strategic for x in model.world]
    N=len(pairs)
    assert N==ns*nx
    actions=list(model.actions)
    feasible=[[actions.index(a) for a in model.feasible[s,x]] for s,x in pairs]
    values=[[exact_result(v,probability=True) for v in row]
            for row in receipt['values_by_remaining_transitions']]
    selected=receipt['selected_actions_by_remaining_transitions']
    fill=[options[0] for options in feasible]
    chosen=[[fill[y] if selected[t+1][y] is None else actions.index(selected[t+1][y])
             for y in range(N)] for t in range(H)]

    dim=f'({ns} * {nx})'
    def state_row(entries):return _fin_case('y',entries,N)
    value_rows=[state_row([rational_expr(v) for v in row]) for row in values]
    choice_rows=[state_row([f'({a} : Fin {na})' for a in row]) for row in chosen]
    fill_row=state_row([f'({a} : Fin {na})' for a in fill])
    soundness=('(checkBellmanReceipt_sound_of_finite_world input options options_exact states_pos\n'
               f'    target {H} values chosen receipt_checked)')
    lines=[
        'import PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact finite Bellman control table; application source candidate only.',
        f'    Problem semantic SHA-256: {problem.semantic_id["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Infeasible P/U entries are normalized Dirac extensions; terminal-state',
        '    controls are filled with the first declared feasible action.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'open PermanssonResearch.ReverseSolver.Bellman',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        *bound_system_lines(feasible,ns,nx,na),
        f'def target : RationalHittingTarget {dim} where',
        f'  goal := {_finset(problem.goal,N)}',
        f'  forbidden := {_finset(problem.forbidden,N)}',
        '  disjoint := by decide','',
        f'def values : ℕ → Fin {dim} → ℚ := fun t y => {_nat_case("t",value_rows,"(0 : ℚ)")}',
        f'def chosen : ℕ → Fin {dim} → Fin {na} := fun t y => {_nat_case("t",choice_rows,fill_row)}',
        '',
        '/-- Kernel evaluation of the executable checker on the complete table:',
        '    terminal values, every recurrence, admitted controls and all',
        '    admitted action-score comparisons. -/',
        f'theorem receipt_checked : checkBellmanReceipt sys target {H} values chosen = true := by',
        '  decide +kernel','',
        f'theorem bellman_values (y : Fin {dim}) :',
        f'    values {H} y = bellmanValue sys target {H} y :=',
        f'  {soundness}.1 y','',
        f'theorem schedule_upper_bound (π : MarkovSchedule sys) (y : Fin {dim}) :',
        f'    policyValue sys target π {H} y ≤ values {H} y :=',
        f'  {soundness}.2.1 π y','',
        f'theorem optimum_attained : ∃ π : MarkovSchedule sys, ∀ y : Fin {dim},',
        f'    policyValue sys target π {H} y = values {H} y :=',
        f'  {soundness}.2.2.1','',
        f'theorem selected_feasible (t : Fin {H}) (y : Fin {dim}) :',
        '    input.feasible (jointIndex.symm y).1 (jointIndex.symm y).2 (chosen t.val y) :=',
        f'  {soundness}.2.2.2 t y','',
    ]
    names=['options_exact','receipt_checked','bellman_values','schedule_upper_bound',
           'optimum_attained','selected_feasible']
    for y,v in enumerate(values[H]):
        name=f'bellman_value_{y}'
        names.append(name)
        lines+=[f'theorem {name} : bellmanValue sys target {H} ({y} : Fin {N}) = {rational_expr(v)} := by',
                f'  rw [← bellman_values ({y} : Fin {N})]',
                '  decide +kernel','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('CONTROL_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':problem.semantic_id,
        'model_semantic_identity':model.semantic_id(),
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'horizon':H},
        'terminal_control_fill':TERMINAL_FILL,
        'p_u_infeasible_normalized_extensions':extensions,
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


def emit_files(problem_file:Path,receipt_file:Path,out_dir:Path)->dict:
    problem_raw,problem=strict_read(problem_file)
    receipt_raw,receipt=read_result(receipt_file)
    lean,metadata=emit_source(parse_hitting_problem(problem),receipt)
    metadata['problem_bytes_sha256']=sha256(problem_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedControlTable.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedControlTable.lean'),
            'metadata_file':str(destination/'source_candidate.json'),
            'lean_status':'NOT_EXECUTED','candidate_sha256':metadata['lean_source_sha256']}


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('problem',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(emit_files(args.problem,args.receipt,args.output),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
