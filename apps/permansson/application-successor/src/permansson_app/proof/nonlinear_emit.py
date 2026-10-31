"""Checked nonlinear classwise objective -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent nonlinear checker are emitted. The
model is reflected as a `FiniteWorldInput` and bound to a control system with
`boundControlSystem`, so the policies are exactly the declared feasible
deterministic stationary action maps, with P and U fixed. Lean enumerates
every such policy and evaluates the exact C10/C11 class arithmetic; the
theorems identify each listed value with the expected Boolean score of the
actual random occupation limit (mixed over the initial law) and the optimum
with the maximum over the whole declared policy class. Randomized and history
-dependent policies are not compared. Emission is never compiler replay,
independent certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.nonlinear import parse_nonlinear
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.nonlinear import check_nonlinear
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _finset, _new_dir, bound_system_lines
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.NonlinearLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedNonlinear'
MAX_POLICIES=16
MAX_SOURCE_BYTES=512*1024


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('NONLINEAR_REIFY_INPUT','raw nonlinear request and receipt required')
    checked=check_nonlinear(raw,receipt)
    model,pairs,truth,initial=parse_nonlinear(raw)
    policies=receipt['policies']
    if len(policies)>MAX_POLICIES:
        raise AppError('NONLINEAR_REIFY_SCOPE',f'Lean nonlinear reflection limited to {MAX_POLICIES} policies')
    input_lines,(ns,nx,na),extensions=input_definition(model)
    N=ns*nx
    assert list(pairs)==[(s,x) for s in model.strategic for x in model.world]
    actions=list(model.actions)
    feasible=[[actions.index(a) for a in model.feasible[pair]] for pair in pairs]
    maps=[[actions.index(a) for a in p['selected_actions']] for p in policies]
    values=[exact_result(p['expected_classwise_score'],probability=True) for p in policies]
    optimum=exact_result(receipt['optimum_value'],probability=True)
    tied=[maps[i] for i in receipt['attaining_policy_indices']]

    dim=f'({ns} * {nx})'
    fn_type=f'Fin {dim} → Fin {na}'
    def literal(m):return f'(![{", ".join(str(a) for a in m)}] : {fn_type})'
    value_body='(0 : ℚ)'
    for m,v in reversed(list(zip(maps,values))):
        value_body=f'(if f = {literal(m)} then {rational_expr(v)} else {value_body})'
    true_idx=[pairs.index(t) for t in truth]
    lines=[
        'import PermanssonResearch.ApplicationBridge.NonlinearReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact nonlinear classwise occupation objective; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Functional: 1 - |p - 2/3| of the true-descriptor share, applied classwise',
        '    to the random occupation limit, then averaged. Policy class: every declared',
        '    feasible deterministic stationary action map. P and U are held fixed.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.NonlinearReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        *bound_system_lines(feasible,ns,nx,na),
        f'instance : NeZero {dim} := ⟨by norm_num⟩',
        f'/-- Boolean descriptor: true exactly on the declared true joint states. -/',
        f'def h : Fin {dim} → Bool := fun y => decide (y ∈ {_finset(true_idx,N)})',
        f'def μ : Fin {dim} → ℚ := fun y => {_fin_case("y",[rational_expr(m) for m in initial],N)}',
        f'def values : ({fn_type}) → ℚ := fun f => {value_body}',
        f'def optimum : ℚ := {rational_expr(optimum)}',
        f'def tied : Finset ({fn_type}) := {{{", ".join(literal(m) for m in tied)}}}',
        '',
        '/-- Kernel evaluation over every admissible deterministic stationary policy. -/',
        'theorem receipt_checked : checkBooleanClassObjective h sys μ values optimum tied = true := by',
        '  decide +kernel','',
        '/-- The optimum is attained and maximizes the actual expected classwise score',
        '    over the whole declared policy class; `tied` is exactly the optimal set. -/',
        'theorem stationary_optimum :',
        '    (∀ f : StateFeedback sys, actualLawScore h sys μ f ≤ optimum) ∧',
        '    (∀ f : StateFeedback sys, f.choose ∈ tied ↔ actualLawScore h sys μ f = optimum) ∧',
        '    ∃ f : StateFeedback sys, f.choose ∈ tied ∧ actualLawScore h sys μ f = optimum :=',
        '  checked_stationary_class_optimum h sys μ values optimum tied receipt_checked','',
    ]
    names=['options_exact','receipt_checked','stationary_optimum']
    for i,(m,v) in enumerate(zip(maps,values)):
        name=f'policy_value_{i}'
        names.append(name)
        lines+=[f'/-- Policy {i} selects {policies[i]["selected_actions"]}. -/',
                f'def policy_{i} : StateFeedback sys where',
                f'  choose := {literal(m)}',
                '  permitted := by decide +kernel',
                f'theorem {name} : actualLawScore h sys μ policy_{i} = (({rational_expr(v)} : ℚ) : ℝ) := by',
                f'  rw [← checked_classwise_objective h sys μ values optimum tied receipt_checked policy_{i}]',
                f'  have hv : values policy_{i}.choose = {rational_expr(v)} := by decide +kernel',
                '  rw [hv]','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('NONLINEAR_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['request_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'policies':len(maps),
                 'functional_id':receipt['functional_id'],'policy_class':receipt['policy_class'],
                 'aggregation_order':'EXPECTATION_OF_CLASSWISE_FUNCTIONAL',
                 'not_compared':['randomized_policies','history_dependent_policies']},
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
    (destination/'ReifiedNonlinear.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedNonlinear.lean'),
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
