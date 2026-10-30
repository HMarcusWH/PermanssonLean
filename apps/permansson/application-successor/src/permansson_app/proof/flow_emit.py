"""Checked one-step risk-constrained occupancy receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent risk-occupancy checker are emitted.
The model is reflected as a `FiniteWorldInput`; the controlled rows are its
fixed-action P·U rows (`controlledMatrix`) and the admitted actions are
exactly the declared feasible ones. The receipt's LP certificate is mapped to
a dual for the mass equalities, the risk cap and the bounds; Lean checks the
primal flow, the dual and the reconstructed policy and proves optimality over
every admissible real randomized one-step policy within the cap. The
reconstructed policy is reflected as its own α/P/U input (P and U fixed) and
its next-state law is identified with the realized model's one-step atoms.
One transition only. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys
from types import MappingProxyType

from ..engines.risk_occupancy import parse_risk
from ..errors import AppError
from ..finite_world import FiniteWorld, exact_ratio
from ..identity import canonical_bytes
from ..receipts.risk_occupancy import check_risk
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _new_dir, bound_system_lines
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.FlowLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedFlow'
MAX_SOURCE_BYTES=512*1024


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('FLOW_REIFY_INPUT','raw risk-occupancy request and receipt required')
    checked=check_risk(raw,receipt)
    q=parse_risk(raw)
    m=q.model
    input_lines,(ns,nx,na),extensions=input_definition(m)
    N=ns*nx
    states=list(q.states)
    assert states==[(s,x) for s in m.strategic for x in m.world]
    actions=list(m.actions)
    feasible=[[actions.index(a) for a in m.feasible[pair]] for pair in states]
    cert=receipt['lp_certificate']
    primal=[exact_ratio(v) for v in cert['primal']]
    dual={label:exact_ratio(v) for label,v in zip(q.lp.row_labels,cert['dual'])}
    zero=Fraction(0)
    flow=[[zero]*na for _ in range(N)];bound=[[zero]*na for _ in range(N)]
    for name,(i,a),value in zip(q.lp.variables,q.variables,primal):
        flow[i][actions.index(a)]=value
        bound[i][actions.index(a)]=dual.get('bound:'+name,zero)
    v=[dual[f'mass{y}:le']-dual[f'mass{y}:ge'] for y in range(N)]
    lam=dual['risk_cap:le']
    D=exact_ratio(cert['objective_value'])+q.lp.offset
    policy=[[zero]*na for _ in range(N)]
    alpha={}
    for y,row in enumerate(receipt['policy']):
        weights=[exact_ratio(row['action_weights'].get(a,'0'),probability=True) for a in actions]
        policy[y]=weights
        alpha[states[y]]=tuple(weights)
    policy_model=FiniteWorld(m.strategic,m.world,m.actions,m.feasible,MappingProxyType(alpha),m.P,m.U)
    policy_lines,dims,policy_ext=input_definition(policy_model,'policyWorld')
    if dims!=(ns,nx,na):raise AppError('FLOW_REIFY_SCOPE','policy world must share dimensions')
    law=[exact_ratio(x,probability=True) for x in receipt['next_state_law']]

    dim=f'({ns} * {nx})'
    def vector(values,var='y'):return _fin_case(var,[rational_expr(x) for x in values],N)
    def table(rows):return _fin_case('y',[_fin_case('a',[rational_expr(x) for x in row],na) for row in rows],N)
    lines=[
        'import PermanssonResearch.ApplicationBridge.FlowReceipt',
        'import PermanssonResearch.ApplicationBridge.MenuReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact one-step risk-constrained occupancy receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    One transition, fully observed randomized Markov controls from the declared',
        '    initial law. The LP certificate is checked, not assumed. P and U are fixed.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ApplicationBridge.FlowReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'open PermanssonResearch.ReverseSolver.FiniteStrategicRealization',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        *bound_system_lines(feasible,ns,nx,na),
        f'def rows : Fin {na} → RationalMarkovMatrix {dim} := fun a => controlledMatrix input a',
        f'def μ : Fin {dim} → ℚ := fun y => {vector(q.initial)}',
        f'def reward : Fin {dim} → ℚ := fun y => {vector(q.rewards)}',
        f'def risk : Finset (Fin {dim}) := {_finset(list(q.risk_states),N)}',
        f'def cap : ℚ := {rational_expr(q.risk_cap)}',
        f'def flow : Fin {dim} → Fin {na} → ℚ := fun y a => {table(flow)}',
        f'def v : Fin {dim} → ℚ := fun y => {vector(v)}',
        f'def lam : ℚ := {rational_expr(lam)}',
        f'def wB : Fin {dim} → Fin {na} → ℚ := fun y a => {table(bound)}',
        f'def D : ℚ := {rational_expr(D)}',
        f'def πr : Fin {dim} → Fin {na} → ℚ := fun y a => {table(policy)}',
        '',
        '/-- Kernel evaluation: primal flow, dual certificate and reconstructed policy. -/',
        'theorem receipt_checked :',
        '    checkFlowReceipt rows options μ reward risk cap flow v lam wB D πr = true := by',
        '  decide +kernel','',
        '/-- Optimal over every admissible real randomized one-step policy within the cap;',
        '    attained by the reconstructed policy. -/',
        'theorem risk_optimum :',
        '    (∀ π : Fin (2 * 2) → Fin 2 → ℝ, Admissible options π → riskMass rows μ risk π ≤ cap →',
        f'      expectedReward rows μ reward π ≤ (({rational_expr(D)} : ℚ) : ℝ)) ∧',
        '    Admissible options (realPolicy πr) ∧',
        f'    expectedReward rows μ reward (realPolicy πr) = (({rational_expr(D)} : ℚ) : ℝ) ∧',
        '    riskMass rows μ risk (realPolicy πr) ≤ cap := by',
        '  have h := checked_risk_optimum rows options μ reward risk cap flow v lam wB D πr receipt_checked',
        f'  have hD : D = {rational_expr(D)} := by decide +kernel',
        '  rw [hD] at h',
        '  exact h','',
        *policy_lines,'',
        '/-- The reconstructed policy as a source intervention: feasibility and P held fixed. -/',
        'theorem policy_held_fixed : HeldFixed input policyWorld := by',
        '  unfold HeldFixed',
        '  simp only [input, policyWorld]',
        '  decide +kernel',
        'theorem policy_update_held_fixed :',
        '    ∀ s x a xp sp, policyWorld.update s x a xp sp = input.update s x a xp sp := by',
        '  simp only [input, policyWorld]',
        '  decide +kernel',
        '/-- Its induced rows are the policy mixture of the controlled rows. -/',
        'theorem policy_rows : ∀ y z, (inducedMatrix policyWorld).entry y z =',
        '    ∑ a, πr y a * (rows a).entry y z := by',
        '  decide +kernel','',
        '/-- The next-state law is the realized policy model\'s one-step law. -/',
        'theorem next_state_law_actual : ∀ z : Fin (2 * 2), nextLaw rows μ (realPolicy πr) z =',
        '    ∑ y, (μ y : ℝ) * ((realizedModel (inducedMatrix policyWorld)).inducedKernel',
        '      (decode y)).real {decode z} := by',
        '  intro z',
        '  unfold nextLaw realPolicy',
        '  apply Finset.sum_congr rfl',
        '  intro y _',
        '  rw [realized_one_step_atom, policy_rows y z]',
        '  push_cast',
        '  rw [Finset.mul_sum]',
        '  apply Finset.sum_congr rfl',
        '  intro a _',
        '  ring','',
    ]
    lines=[l.replace('Fin (2 * 2) → Fin 2 → ℝ',f'Fin {dim} → Fin {na} → ℝ').replace('∀ z : Fin (2 * 2)',f'∀ z : Fin {dim}')
           for l in lines]
    names=['options_exact','receipt_checked','risk_optimum','policy_held_fixed','policy_update_held_fixed',
           'policy_rows','next_state_law_actual']
    for z,value in enumerate(law):
        name=f'next_state_mass_{z}'
        names.append(name)
        lines+=[f'theorem {name} : nextLaw rows μ (realPolicy πr) ({z} : Fin {N}) = (({rational_expr(value)} : ℚ) : ℝ) := by',
                '  unfold nextLaw realPolicy',
                f'  have hv : (∑ y, ∑ a, μ y * πr y a * (rows a).entry y ({z} : Fin {N})) = {rational_expr(value)} := by',
                '    decide +kernel',
                '  rw [← hv]',
                '  push_cast',
                '  rfl','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('FLOW_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['request_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,
                 'optimization':'ONE_TRANSITION_ALL_ADMISSIBLE_REAL_RANDOMIZED_MARKOV_POLICIES',
                 'not_claimed':['multi_stage_occupancy','private_information','robust_nature']},
        'p_u_infeasible_normalized_extensions':{'input':extensions,'policyWorld':policy_ext},
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
    (destination/'ReifiedFlow.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedFlow.lean'),
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
