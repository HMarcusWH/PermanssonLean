"""Checked belief receipt (one step or finite tree) -> source-bound Lean *candidate*.

Only receipts that pass the independent one-step belief or belief-tree checker
are emitted. The model is reflected as a `FiniteWorldInput`, the observation
kernel, prior and terminal rewards as literal rationals, and the receipt's
selected observation-history tree, terminal law, optimum and blind baseline as
literal data. Lean checks them on unnormalized forward vectors and transfers
them to Research's chronological belief law through the time-shifted
embedding of `BeliefTreeReceipt`: every real behavioral observation-history
policy admitted on the hidden support is bounded by the optimum, which the
selected tree attains. A one-step request is the horizon-1 case with one
strategic state. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.belief import REQUEST as ONE_STEP_REQUEST, parse_belief
from ..engines.belief_tree import REQUEST as TREE_REQUEST, parse_belief_tree
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.belief import check_belief
from ..receipts.belief_tree import check_belief_tree
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.BeliefLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedBelief'
MAX_SOURCE_BYTES=512*1024
MAX_HORIZON=3
# Unreachable observations carry no receipt action; any action is admitted on
# their zero forward vector and contributes nothing.
UNREACHABLE_FILL='action_index_0'


def _one_step(raw:dict,receipt:dict):
    checked=check_belief(raw,receipt)
    p=parse_belief(raw)
    actions=list(p.model.actions)
    nodes=[None if row['unreachable'] else (actions.index(row['selected_action']),None)
           for row in receipt['policy']]
    blind=receipt['best_blind_policy_reward']
    return (checked,p.model,1,list(p.prior),list(p.terminal_rewards),[list(r) for r in p.likelihood],
            list(p.observations),nodes,[exact_ratio(v,probability=True) for v in receipt['next_world_law']],
            exact_ratio(receipt['optimal_expected_terminal_reward']),
            None if blind is None else exact_ratio(blind),'ONE_STEP')


def _tree_nodes(tree:dict,actions:list[str]):
    nodes=[]
    for row in tree['observations']:
        if row['unreachable']:
            nodes.append(None)
            continue
        child=None if row['next_tree'] is None else _tree_nodes(row['next_tree'],actions)
        nodes.append((actions.index(row['selected_action']),child))
    return nodes


def _belief_tree(raw:dict,receipt:dict):
    checked=check_belief_tree(raw,receipt)
    p=parse_belief_tree(raw)
    actions=list(p.model.actions)
    blind=receipt['best_blind_action_sequence_reward']
    return (checked,p.model,p.horizon,list(p.prior),list(p.terminal_rewards),[list(r) for r in p.likelihoods],
            list(p.observations),_tree_nodes(receipt['optimal_policy_tree'],actions),
            [exact_ratio(v,probability=True) for v in receipt['terminal_joint_law']],
            exact_ratio(receipt['optimal_expected_terminal_reward']),
            None if blind is None else exact_ratio(blind),'TREE')


def _blind_mirror(model,states,feasible,rewards,prior,H):
    """Best blind sequence by the Lean `blindValue` recursion (first maximum).

    Returns (value, sequence, live); `live` is False when the maximum runs
    through an empty admitted set, which Lean values at 0.
    """
    N=len(states);actions=list(model.actions);world=list(model.world);strategic=list(model.strategic)
    def atom(a,y,z):
        (s,x),(sp,xp)=states[y],states[z];act=actions[a]
        return model.P[s,x,act][world.index(xp)]*model.U[s,x,act,xp][strategic.index(sp)]
    def legal(f,a):return all(a in feasible[y] for y in range(N) if f[y])
    def advance(f,a):
        return tuple(sum((f[y]*atom(a,y,z) for y in range(N) if f[y]),Fraction(0)) for z in range(N))
    def best(f,h):
        if h==0:return sum((f[y]*rewards[y] for y in range(N)),Fraction(0)),[],True
        result=None
        for a in range(len(actions)):
            if legal(f,a):
                value,seq,live=best(advance(f,a),h-1)
                if result is None or value>result[0]:result=(value,[a]+seq,live)
        return result if result is not None else (Fraction(0),[0]*h,False)
    return best(tuple(prior),H)


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('BELIEF_REIFY_INPUT','raw belief request and receipt required')
    if raw.get('format')==ONE_STEP_REQUEST:
        parts=_one_step(raw,receipt)
    elif raw.get('format')==TREE_REQUEST:
        parts=_belief_tree(raw,receipt)
    else:
        raise AppError('BELIEF_REIFY_INPUT','one-step belief or finite belief-tree request required')
    checked,m,H,prior,rewards,likelihood,observations,nodes,law,D,B,profile=parts
    if not 1<=H<=MAX_HORIZON:
        raise AppError('BELIEF_REIFY_SCOPE',f'Lean belief reflection limited to 1..{MAX_HORIZON} transitions')
    input_lines,(ns,nx,na),extensions=input_definition(m)
    no=len(observations)
    states=[(s,x) for s in m.strategic for x in m.world]
    N=len(states)
    assert N==ns*nx==len(prior)==len(rewards)==len(law)
    actions=list(m.actions)
    feasible=[[actions.index(a) for a in m.feasible[pair]] for pair in states]
    blind=None
    if B is not None:
        value,seq,live=_blind_mirror(m,states,feasible,rewards,prior,H)
        if value!=B or not live:
            raise AppError('BELIEF_REIFY_SCOPE','blind baseline runs through an empty admitted set')
        blind=seq

    def joint(values):
        return _fin_case('y.1',[_fin_case('y.2',[rational_expr(values[s*nx+x]) for x in range(nx)],nx)
                                for s in range(ns)],ns)
    def tree(h,node,depth):
        if h==0:return 'PUnit.unit'
        a=0 if node is None else node[0]
        children=None if node is None else node[1]
        if h==1:return f'(({a} : Fin {na}), fun _ => PUnit.unit)'
        subtrees=[tree(h-1,None if children is None else children[o],depth+1) for o in range(no)]
        return f'(({a} : Fin {na}), fun o{depth} => {_fin_case(f"o{depth}",subtrees,no)})'
    roots=_fin_case('o0',[tree(H,nodes[o],1) for o in range(no)],no)
    def pair(y):s,x=divmod(y,nx);return f'(({s} : Fin {ns}), ({x} : Fin {nx}))'
    Dl=rational_expr(D)
    chron=f'((model obsInput prior).chronologicalLaw ({H} + 1) 0 (realPrior prior) (selectedPolicy {H} roots))'

    lines=[
        'import PermanssonResearch.ApplicationBridge.BeliefTreeReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact observe-then-act belief receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        f'    Profile: {profile}; {H} transition(s); the first observation is of the initial state.',
        '    Values, admissibility and the terminal law are kernel-checked on unnormalized',
        '    forward vectors. A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.BeliefTreeReceipt',
        'open PermanssonResearch.ReverseSolver',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        f'def options : Fin ({ns} * {nx}) → Finset (Fin {na}) := fun y => '
        f'{_fin_case("y",[_finset(f,na) for f in feasible],N)}','',
        '/-- Admitted actions are exactly the reflected feasible actions. -/',
        'theorem options_exact : AdmittedExactly input options := by',
        '  unfold AdmittedExactly',
        '  simp only [input]',
        '  decide','',
        f'def likelihood : Fin {nx} → Fin {no} → ℚ := fun x o => '
        +_fin_case('x',[_fin_case('o',[rational_expr(v) for v in row],no) for row in likelihood],nx),
        'theorem likelihood_nonneg : ∀ x o, 0 ≤ likelihood x o := by',
        '  decide +kernel','',
        'theorem likelihood_sum_one : ∀ x, (∑ o, likelihood x o) = 1 := by',
        '  decide +kernel','',
        f'def obsInput : RationalObservationInput {ns} {nx} {na} {no} :=',
        '  ⟨input, likelihood, likelihood_nonneg, likelihood_sum_one⟩','',
        f'def priorWeight : Joint {ns} {nx} → ℚ := fun y => {joint(prior)}',
        'theorem prior_nonneg : ∀ y, 0 ≤ priorWeight y := by',
        '  decide +kernel','',
        'theorem prior_sum_one : (∑ y, priorWeight y) = 1 := by',
        '  decide +kernel','',
        f'def prior : RationalBelief {ns} {nx} := ⟨priorWeight, prior_nonneg, prior_sum_one⟩','',
        f'def reward : Joint {ns} {nx} → ℚ := fun y => {joint(rewards)}',
        f'def roots : Fin {no} → Belief.Tree (Fin {na}) (Fin {no}) {H} := fun o0 => {roots}',
        f'def D : ℚ := {Dl}',
        f'def law : Joint {ns} {nx} → ℚ := fun y => {joint(law)}','',
        '/-- Kernel evaluation: optimum, selected-tree value and admissibility, terminal law. -/',
        'theorem receipt_checked :',
        f'    checkBeliefTree obsInput options reward prior.weight {H} roots D law = true := by',
        '  decide +kernel','',
        '/-- Every admitted real behavioral observation-history policy is bounded by the',
        '    optimum on the actual chronological law; the selected tree attains it. -/',
        'theorem observation_optimum :',
        f'    (∀ π : Belief.Behavioral (Fin {na}) (Fin {no}) ({H} + 1),',
        f'      RootLegal obsInput prior options {H} π →',
        f'        actualValue obsInput prior reward {H} π ≤ (({Dl} : ℚ) : ℝ)) ∧',
        f'    RootLegal obsInput prior options {H} (selectedPolicy {H} roots) ∧',
        f'    actualValue obsInput prior reward {H} (selectedPolicy {H} roots) = (({Dl} : ℚ) : ℝ) := by',
        f'  have h := checked_observation_optimum obsInput prior options reward {H} roots D law receipt_checked',
        f'  have hD : D = {Dl} := by decide +kernel',
        '  rw [hD] at h',
        '  exact h','',
    ]
    names=['options_exact','likelihood_nonneg','likelihood_sum_one','prior_nonneg','prior_sum_one',
           'receipt_checked','observation_optimum']
    for y,value in enumerate(law):
        name=f'terminal_law_{y}'
        names.append(name)
        lines+=[f'theorem {name} :',
                f'    (∫ q, (if Belief.Model.terminal ({H} + 1) q.1 q.2 = {pair(y)} then (1 : ℝ) else 0)',
                f'      ∂{chron}.pmf.toMeasure) = (({rational_expr(value)} : ℚ) : ℝ) := by',
                f'  have h := checked_terminal_law obsInput prior options reward {H} roots D law receipt_checked',
                f'    {pair(y)}',
                f'  have hv : law {pair(y)} = {rational_expr(value)} := by decide +kernel',
                '  rw [hv] at h',
                '  exact h','']
    if blind is not None:
        Bl=rational_expr(B)
        seq='['+', '.join(f'({a} : Fin {na})' for a in blind)+']'
        lines+=[
            f'def blindSeq : List (Fin {na}) := {seq}',
            f'def B : ℚ := {Bl}','',
            '/-- Kernel evaluation: the blind sequence is admitted and attains the best',
            '    observation-independent value. -/',
            'theorem blind_checked :',
            f'    checkBlind obsInput options reward prior.weight {H} blindSeq B = true := by',
            '  decide +kernel','',
            'theorem blind_baseline :',
            f'    RootLegal obsInput prior options {H} (blindPolicy {H} blindSeq) ∧',
            f'    actualValue obsInput prior reward {H} (blindPolicy {H} blindSeq) = (({Bl} : ℚ) : ℝ) ∧',
            f'    ∀ seq : List (Fin {na}), seq.length = {H} →',
            '      seqLegal obsInput options seq prior.weight = true →',
            f'        actualValue obsInput prior reward {H} (blindPolicy {H} seq) ≤ (({Bl} : ℚ) : ℝ) := by',
            f'  have h := checked_blind obsInput prior options reward {H} blindSeq B blind_checked',
            f'  have hB : B = {Bl} := by decide +kernel',
            '  rw [hB] at h',
            '  exact h','',
            '/-- Observation can only help. -/',
            f'theorem value_of_observation : ({Bl} : ℚ) ≤ {Dl} := by',
            f'  have h := checked_value_of_observation obsInput prior options reward {H} roots D law',
            '    blindSeq B receipt_checked blind_checked',
            f'  have hD : D = {Dl} := by decide +kernel',
            f'  have hB : B = {Bl} := by decide +kernel',
            # A calc chain, not `rw ... at h`: when B = D, rw's closing rfl
            # would discharge the goal and leave `exact h` with no goal.
            f'  calc ({Bl} : ℚ) = B := hB.symm',
            '    _ ≤ D := h',
            f'    _ = {Dl} := hD','',
        ]
        names+=['blind_checked','blind_baseline','value_of_observation']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('BELIEF_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['request_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'profile':profile,'ns':ns,'nx':nx,'na':na,'no':no,'horizon':H,'joint_states':N,
                 'chronology':'OBSERVE_CURRENT_STATE_THEN_ACT_THEN_P_THEN_U_TIME_SHIFTED_INTO_RESEARCH_BELIEF',
                 'optimization':'ALL_REAL_BEHAVIORAL_OBSERVATION_HISTORY_POLICIES_ADMITTED_ON_HIDDEN_SUPPORT',
                 'blind_baseline':'CHECKED' if blind is not None else 'NONE_REPORTED',
                 'unreachable_observation_fill':UNREACHABLE_FILL,
                 'not_claimed':['posterior_values','action_scores','hidden_state_controllers',
                                'empirical_observation_model']},
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
    receipt_raw,receipt=strict_read(receipt_file)
    lean,metadata=emit_source(request,receipt)
    metadata['problem_bytes_sha256']=sha256(request_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedBelief.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedBelief.lean'),
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
