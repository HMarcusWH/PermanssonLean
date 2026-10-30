"""Checked residence receipt -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent residence checker are emitted. Each
application mode maps to the Lean monitor whose literal event it computes:
retryable -> `checkResidenceValues` (compact residence monitor), first_entry ->
`checkFirstEntryValues`, avoid -> `checkAvoidValues` (danger before or at
success fails). The Lean control system is `boundControlSystem` over the
reflected alpha/P/U input. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.monitors import parse_residence
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.residence import check_residence
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.ResidenceLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedResidence'
MAX_HORIZON=6
MAX_SOURCE_BYTES=256*1024
# mode -> (Lean checker, behavioral probability, soundness theorem, uses danger set)
MODES={
    'retryable':('checkResidenceValues','behavioralResidenceProbability',
                 'checkResidenceValues_sound',False),
    'first_entry':('checkFirstEntryValues','behavioralFirstEntryProbability',
                   'checkFirstEntryValues_sound',False),
    'avoid':('checkAvoidValues','behavioralAvoidResidenceProbability',
             'checkAvoidValues_sound',True),
}


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('RESIDENCE_REIFY_INPUT','raw residence request and receipt required')
    checked=check_residence(raw,receipt)
    problem=parse_residence(raw)
    if problem.mode not in MODES:
        raise AppError('RESIDENCE_REIFY_SCOPE','residence mode has no Lean bridge')
    checker,probability,soundness,uses_danger=MODES[problem.mode]
    if not 1<=problem.horizon<=MAX_HORIZON:
        raise AppError('RESIDENCE_REIFY_SCOPE',f'Lean residence reflection limited to 1..{MAX_HORIZON} transitions')
    model=problem.model
    input_lines,(ns,nx,na),extensions=input_definition(model)
    pairs=[(s,x) for s in model.strategic for x in model.world]
    N=len(pairs)
    assert N==ns*nx
    actions=list(model.actions)
    feasible=[[actions.index(a) for a in model.feasible[s,x]] for s,x in pairs]
    values=[exact_ratio(v,probability=True) for v in receipt['probability_by_initial_state']]
    dwell,latest=problem.dwell_transitions,problem.latest_entry
    # The Lean event spans latest + dwell transitions; this is the receipt horizon.
    assert latest+dwell==problem.horizon

    dim=f'({ns} * {nx})'
    def state_row(entries):return _fin_case('y',entries,N)
    sets='targetSet dangerSet' if uses_danger else 'targetSet'
    events='(· ∈ targetSet) (· ∈ dangerSet)' if uses_danger else '(· ∈ targetSet)'
    lines=[
        'import PermanssonResearch.ApplicationBridge.ResidenceReceipt',
        'import Mathlib.Tactic','',
        f'/-! Reified exact {problem.mode} residence values; application source candidate only.',
        f'    Problem semantic SHA-256: {problem.semantic_id["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Infeasible P/U entries are normalized Dirac extensions.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.ResidenceReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'open PermanssonResearch.ReverseSolver.FiniteMonitor',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        f'def options : Fin {dim} → Finset (Fin {na}) := fun y => '
        f'{state_row([_finset(indices,na) for indices in feasible])}',
        '',
        '/-- Admitted controls are exactly the reflected feasible actions. -/',
        'theorem options_exact : AdmittedExactly input options := by',
        '  unfold AdmittedExactly',
        '  simp only [input]',
        '  decide',
        f'theorem states_pos : 0 < {ns} * {nx} := by norm_num','',
        f'def sys : FiniteControlSystem (Fin {na}) {dim} :=',
        '  boundControlSystem input options options_exact states_pos','',
        f'def targetSet : Finset (Fin {dim}) := {_finset(list(problem.target),N)}',
        *([f'def dangerSet : Finset (Fin {dim}) := {_finset(list(problem.danger),N)}'] if uses_danger else []),
        f'def values : Fin {dim} → ℚ := fun y => {state_row([rational_expr(v) for v in values])}',
        f'def dwell : ℕ := {dwell}',
        f'def latest : ℕ := {latest}',
        '',
        '/-- Kernel evaluation of the layer-wise optimal residence table at every start. -/',
        f'theorem receipt_checked : {checker} sys {sets} dwell latest values = true := by',
        '  decide +kernel','',
    ]
    names=['options_exact','receipt_checked']
    for y,v in enumerate(values):
        name=f'optimal_residence_{y}'
        names.append(name)
        literal=f'(({rational_expr(v)} : ℚ) : ℝ)'
        lines+=[f'theorem {name} :',
                '    (∀ σ : BehavioralPolicy sys,',
                f'      {probability} sys σ {events} dwell latest ({y} : Fin {N}) ≤ {literal}) ∧',
                '    (∃ σ : BehavioralPolicy sys,',
                f'      {probability} sys σ {events} dwell latest ({y} : Fin {N}) = {literal}) := by',
                f'  have hv : values ({y} : Fin {N}) = {rational_expr(v)} := by decide +kernel',
                f'  simpa only [hv] using',
                f'    {soundness} sys {sets} dwell latest values receipt_checked ({y} : Fin {N})','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('RESIDENCE_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':problem.semantic_id,
        'model_semantic_identity':model.semantic_id(),
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'mode':problem.mode,
                 'dwell_transitions':dwell,'latest_entry':latest,'horizon':problem.horizon},
        'initial_law_mixture':'NOT_REFLECTED_PER_START_VALUES_ONLY',
        'p_u_infeasible_normalized_extensions':extensions,
        'lean_status':'NOT_EXECUTED',
        'source_emitted':True,
        'compiler_evidence_authenticated':False,
        'independent_math_certification':False,
        'empirical_identification':False,
        'application_release_authorized':False,
    }
    return text,out


def emit_files(problem_file:Path,receipt_file:Path,out_dir:Path)->dict:
    problem_raw,problem=strict_read(problem_file)
    receipt_raw,receipt=strict_read(receipt_file)
    lean,metadata=emit_source(problem,receipt)
    metadata['problem_bytes_sha256']=sha256(problem_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedResidence.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedResidence.lean'),
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
