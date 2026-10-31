"""Checked rectangular-vs-committed nature receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent nature checker are emitted. The
baseline and every nature model are reflected as `FiniteWorldInput`s; nature
models are proved to keep feasibility, α and U and to change only P. Three
finite rectangular games are built from the controlled P·U rows: the
optimized game (all admitted controls, all nature rows), the declared fixed
policy against rectangular nature, and the fixed policy under each single
committed model. Lean checks every value table and transfers Research's
chronological saddle theorem to each. Committed-game optimality and
private-stage statements are not claimed. Emission is never compiler replay,
independent certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.robust_nature import parse_nature
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.robust_nature import check_nature
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _nat_case, _new_dir, bound_system_lines
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.RobustNatureLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedRobustNature'
MAX_HORIZON=6
MAX_SOURCE_BYTES=512*1024


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('ROBUST_REIFY_INPUT','raw nature request and receipt required')
    checked=check_nature(raw,receipt)
    q=parse_nature(raw)
    if not q.horizon<=MAX_HORIZON:
        raise AppError('ROBUST_REIFY_SCOPE',f'Lean nature reflection limited to horizon 0..{MAX_HORIZON}')
    input_lines,(ns,nx,na),extensions=input_definition(q.baseline)
    N=ns*nx;K=len(q.nature_worlds);H=q.horizon
    states=list(q.states)
    assert states==[(s,x) for s in q.baseline.strategic for x in q.baseline.world]
    actions=list(q.baseline.actions)
    feasible=[[actions.index(a) for a in q.baseline.feasible[pair]] for pair in states]
    policy=[actions.index(a) for a in q.policy]

    dim=f'({ns} * {nx})'
    def exact(v):return v if type(v) is Fraction else exact_result(v)
    def vector(values):return _fin_case('y',[rational_expr(exact(v)) for v in values],N)
    def table(rows):return _nat_case('r',[vector(row) for row in rows],'(0 : ℚ)')
    lines=[
        'import PermanssonResearch.ApplicationBridge.RobustReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact rectangular-vs-committed nature receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Nature observes the realized control, then selects a physical P row; it may',
        '    reselect at every node (rectangular) or commit to one model. Strategic α and',
        '    U are held fixed. A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.RobustReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'open PermanssonResearch.ReverseSolver.RectangularFiniteGame',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        *bound_system_lines(feasible,ns,nx,na),
    ]
    names=['options_exact'];all_extensions={'input':extensions}
    for j,(ident,world) in enumerate(zip(q.nature_ids,q.nature_worlds)):
        nature_lines,dims,ext=input_definition(world,f'nature_{j}')
        if dims!=(ns,nx,na):raise AppError('ROBUST_REIFY_SCOPE','nature models must share dimensions')
        all_extensions[f'nature_{j}']=ext
        lines+=[*nature_lines,'',
                f'/-- Nature model `{ident}` changes only the physical kernel P. -/',
                f'theorem nature_{j}_held_fixed :',
                f'    (∀ s x a, nature_{j}.feasible s x a ↔ input.feasible s x a) ∧',
                f'    (∀ s x a, nature_{j}.alpha s x a = input.alpha s x a) ∧',
                f'    (∀ s x a xp sp, nature_{j}.update s x a xp sp = input.update s x a xp sp) := by',
                f'  simp only [input, nature_{j}]',
                '  decide +kernel','']
        names.append(f'nature_{j}_held_fixed')
    matrix=_fin_case('θ',[f'controlledMatrix nature_{j} c' for j in range(K)],K)
    rewards=vector(q.rewards)
    lines+=[
        f'def natureMatrix : Fin {K} → Fin {na} → RationalMarkovMatrix {dim} := fun θ c => {matrix}',
        f'def reward : Fin {dim} → ℚ := fun y => {rewards}',
        f'def policy : Fin {dim} → Fin {na} := fun y => {_fin_case("y",[f"({a} : Fin {na})" for a in policy],N)}',
        f'def horizon : ℕ := {H}','',
        '/-- Optimized game: every admitted control against every nature row. -/',
        f'def game : Game (Fin {na}) (Fin {K}) {dim} where',
        '  states_nonempty := by norm_num',
        '  options := options',
        '  options_nonempty := by decide +kernel',
        '  natureOptions := fun _ _ _ => Finset.univ',
        '  nature_nonempty := fun _ _ _ => Finset.univ_nonempty',
        '  matrix := fun _ c θ => natureMatrix θ c','',
        '/-- The declared fixed policy against rectangular nature. -/',
        f'def fixedGame : Game (Fin {na}) (Fin {K}) {dim} where',
        '  states_nonempty := by norm_num',
        '  options := fun y => {policy y}',
        '  options_nonempty := fun _ => Finset.singleton_nonempty _',
        '  natureOptions := fun _ _ _ => Finset.univ',
        '  nature_nonempty := fun _ _ _ => Finset.univ_nonempty',
        '  matrix := fun _ c θ => natureMatrix θ c','',
        '/-- The declared fixed policy under one committed nature model. -/',
        f'def committedGame (j : Fin {K}) : Game (Fin {na}) (Fin {K}) {dim} where',
        '  states_nonempty := by norm_num',
        '  options := fun y => {policy y}',
        '  options_nonempty := fun _ => Finset.singleton_nonempty _',
        '  natureOptions := fun _ _ _ => {j}',
        '  nature_nonempty := fun _ _ _ => Finset.singleton_nonempty _',
        '  matrix := fun _ c θ => natureMatrix θ c','',
        '/-- The fixed policy is admitted. -/',
        'theorem policy_admitted : ∀ y, policy y ∈ options y := by decide +kernel','',
        f'def gameTable : ℕ → Fin {dim} → ℚ := fun r y => {table(receipt["rectangular_optimal_values_by_remaining"])}',
        f'def fixedTable : ℕ → Fin {dim} → ℚ := fun r y => {table(receipt["fixed_policy_rectangular_values_by_remaining"])}',
    ]
    committed=receipt['fixed_policy_committed_values_by_nature']
    for j in range(K):
        lines.append(f'def committedTable_{j} : ℕ → Fin {dim} → ℚ := fun r y => {table(committed[j])}')
    lines+=['',
        'theorem game_checked : checkRectangularTable game reward horizon gameTable = true := by',
        '  decide +kernel',
        'theorem fixed_checked : checkRectangularTable fixedGame reward horizon fixedTable = true := by',
        '  decide +kernel']
    names+=['policy_admitted','game_checked','fixed_checked']
    for j in range(K):
        lines+=[f'theorem committed_{j}_checked :',
                f'    checkRectangularTable (committedGame {j}) reward horizon committedTable_{j} = true := by',
                '  decide +kernel']
        names.append(f'committed_{j}_checked')
    lines.append('')

    def saddle(name,game,checked_name,tab,value,y,doc):
        names.append(name)
        v=rational_expr(exact_result(value))
        return [f'/-- {doc} from state {y}: saddle value on the actual chronological law. -/',
                f'theorem {name} :',
                f'    (∃ σ : Controller {game}, ∀ η : Nature {game},',
                f'      (({v} : ℚ) : ℝ) ≤ gameExpectation {game} reward σ η horizon 0 (({y} : Fin {N}), []) ({y} : Fin {N})) ∧',
                f'    (∃ η : Nature {game}, ∀ σ : Controller {game},',
                f'      gameExpectation {game} reward σ η horizon 0 (({y} : Fin {N}), []) ({y} : Fin {N}) ≤ (({v} : ℚ) : ℝ)) := by',
                f'  have h := checked_rectangular_saddle {game} reward horizon {tab} {checked_name} ({y} : Fin {N})',
                f'  have hv : {tab} horizon ({y} : Fin {N}) = {v} := by decide +kernel',
                '  rw [hv] at h',
                '  exact h','']
    final=lambda rows,y:rows[H][y]
    for y in q.starts:
        lines+=saddle(f'rectangular_optimum_{y}','game','game_checked','gameTable',
                      final(receipt['rectangular_optimal_values_by_remaining'],y),y,'Optimized rectangular value')
        lines+=saddle(f'fixed_rectangular_{y}','fixedGame','fixed_checked','fixedTable',
                      final(receipt['fixed_policy_rectangular_values_by_remaining'],y),y,
                      'Fixed policy against rectangular nature')
        for j in range(K):
            lines+=saddle(f'committed_{j}_{y}',f'(committedGame {j})',f'committed_{j}_checked',
                          f'committedTable_{j}',final(committed[j],y),y,
                          f'Fixed policy under committed model `{q.nature_ids[j]}`')
    starts=_finset(list(q.starts),N)
    lines+=['/-- On the comparison states, rectangular nature holds the fixed policy to at',
            '    most its value under every single committed model. -/',
            'theorem rectangular_le_committed :',
            f'    ∀ y ∈ {starts}, '
            + ' ∧ '.join(f'fixedTable horizon y ≤ committedTable_{j} horizon y' for j in range(K))
            + ' := by',
            '  decide +kernel','']
    names.append('rectangular_le_committed')
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('ROBUST_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['request_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'nature_models':list(q.nature_ids),
                 'horizon':H,'comparison_states':list(q.starts),
                 'not_claimed':['committed_game_optimum','private_stage','unbounded_horizon']},
        'p_u_infeasible_normalized_extensions':all_extensions,
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
    (destination/'ReifiedRobustNature.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedRobustNature.lean'),
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
