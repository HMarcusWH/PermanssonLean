"""Checked finite safety core -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent safety checker are emitted. The Lean
control system is `boundControlSystem` over the reflected alpha/P/U input, so
the infinite-horizon almost-sure safety theorems concern the submitted source
model. Emission is never compiler replay, independent certification,
empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.safety import SafetyProblem, parse_safety_problem
from ..errors import AppError
from ..identity import canonical_bytes
from ..receipts.safety import check_safety_core
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition

FORMAT='Permansson.App.SafetyCoreLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedSafetyCore'
MAX_SOURCE_BYTES=256*1024
# Witness controls are only checked on core states. Elsewhere the first
# declared feasible action is reflected; it carries no policy authority.
NONCORE_FILL='first_declared_feasible_action'


def emit_source(problem:SafetyProblem,receipt:dict)->tuple[str,dict]:
    if type(problem) is not SafetyProblem or type(receipt) is not dict:
        raise AppError('SAFETY_REIFY_INPUT','parsed safety problem and raw core receipt required')
    checked=check_safety_core(problem,receipt)
    model=problem.model
    input_lines,(ns,nx,na),extensions=input_definition(model)
    pairs=[(s,x) for s in model.strategic for x in model.world]
    N=len(pairs)
    assert N==ns*nx
    actions=list(model.actions)
    feasible=[[actions.index(a) for a in model.feasible[s,x]] for s,x in pairs]
    core=list(receipt['core_indices'])
    witness=[options[0] for options in feasible]
    for item in receipt['stationary_witness_actions']:
        witness[item['state_index']]=actions.index(item['action'])
    region=list(problem.safe_indices)
    excluded=[i for i in region if i not in core]

    dim=f'({ns} * {nx})'
    def state_row(entries):return _fin_case('y',entries,N)
    args='sys safeRegion core witness receipt_checked'
    lines=[
        'import PermanssonResearch.ApplicationBridge.SafetyReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact finite almost-sure safety core; application source candidate only.',
        f'    Problem semantic SHA-256: {problem.identity["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Infeasible P/U entries are normalized Dirac extensions; witness controls',
        '    outside the core are filled with the first declared feasible action.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.SafetyReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'open PermanssonResearch.ReverseSolver.FiniteMonitor',
        'open PermanssonResearch.ReverseSolver.InfiniteSafety',
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
        f'def safeRegion : Finset (Fin {dim}) := {_finset(region,N)}',
        f'def core : Finset (Fin {dim}) := {_finset(core,N)}',
        f'def witness : Fin {dim} → Fin {na} := fun y => '
        f'{state_row([f"({a} : Fin {na})" for a in witness])}',
        '',
        '/-- Kernel evaluation of the executable checker: the reported core is the',
        '    finite pruning fixed point and every witness control closes it. -/',
        'theorem receipt_checked : checkInvariantCore sys safeRegion core witness = true := by',
        '  decide +kernel','',
        'theorem core_greatest_invariant :',
        '    invariantCore sys safeRegion = core ∧ core ⊆ safeRegion ∧',
        '      controlledInvariant sys core ∧',
        f'      ∀ T : Finset (Fin {dim}), T ⊆ safeRegion → controlledInvariant sys T → T ⊆ core :=',
        f'  checked_invariant_core_eq {args}','',
        f'theorem core_iff_almost_sure (y : Fin {dim}) :',
        '    y ∈ core ↔ ∃ σ : BehavioralPolicy sys, safetyProbability sys σ safeRegion y = 1 :=',
        f'  checked_core_iff_almostSureSafety {args} y','',
        f'theorem core_iff_value_one (y : Fin {dim}) :',
        '    y ∈ core ↔ limitValue sys safeRegion y = 1 :=',
        f'  (checked_infinite_safety_optimum {args}).1 y','',
    ]
    names=['options_exact','receipt_checked','core_greatest_invariant',
           'core_iff_almost_sure','core_iff_value_one']
    for y in core:
        name=f'almost_sure_safe_{y}'
        names.append(name)
        lines+=[f'theorem {name} :',
                f'    ∃ σ : BehavioralPolicy sys, safetyProbability sys σ safeRegion ({y} : Fin {N}) = 1 :=',
                f'  (core_iff_almost_sure ({y} : Fin {N})).mp (by decide)','']
    for y in excluded:
        name=f'not_almost_sure_{y}'
        names.append(name)
        lines+=[f'theorem {name} (σ : BehavioralPolicy sys) :',
                f'    safetyProbability sys σ safeRegion ({y} : Fin {N}) < 1 :=',
                f'  checked_outside_core_not_almost_sure {args} ({y} : Fin {N}) (by decide) σ','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('SAFETY_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':problem.identity,
        'model_semantic_identity':model.semantic_id(),
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,
                 'safe_region':region,'core':core,'excluded_from_core':excluded},
        'noncore_witness_fill':NONCORE_FILL,
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
    lean,metadata=emit_source(parse_safety_problem(problem),receipt)
    metadata['problem_bytes_sha256']=sha256(problem_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedSafetyCore.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedSafetyCore.lean'),
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
