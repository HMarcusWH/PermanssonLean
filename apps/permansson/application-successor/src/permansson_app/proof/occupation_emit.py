"""Checked finite occupation receipt -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent occupation checker are emitted. The
model is reflected as a `FiniteWorldInput` and the chain is its α/P/U-induced
matrix (`inducedMatrix`). The emitted theorems bind the bottom classes to the
computed bottom classes, every absorption weight to the actual probability of
eventually entering that class, every class law (via C11) to the actual
almost-sure occupation limit on the event that class is selected, the whole
law of the random occupation limit to the receipt's Dirac mixture, and each
mean law to its barycenter only. GR/PR and original-margin corollaries are not
claimed. Emission is never compiler replay, independent certification,
empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..errors import AppError
from ..finite_world import exact_result,parse_finite_world
from ..identity import canonical_bytes
from ..receipts.occupation import check_occupation
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.OccupationLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedOccupation'
MAX_SOURCE_BYTES=512*1024


def _by_class(classes:list[list[int]],columns:list[str],default:str)->str:
    result=default
    for c in range(len(classes)-1,-1,-1):
        result=f'(if C = class_{c} then {columns[c]} else {result})'
    return result


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('OCCUPATION_REIFY_INPUT','raw finite model and occupation receipt required')
    model=parse_finite_world(raw)
    checked=check_occupation(model,receipt)
    input_lines,(ns,nx,na),extensions=input_definition(model)
    N=ns*nx
    classes=receipt['bottom_classes']
    weights=[[exact_result(v,probability=True) for v in row] for row in receipt['absorption_weights']]
    laws=[]
    for group,raw_law in zip(classes,receipt['stationary_laws']):
        law=[Fraction(0)]*N
        for state,value in zip(group,raw_law):
            law[state]=exact_result(value,probability=True)
        laws.append(law)
    mean=[[exact_result(v,probability=True) for v in row] for row in receipt['expected_limit_laws']]

    dim=f'({ns} * {nx})'
    def column(values):return _fin_case('y',[rational_expr(v) for v in values],N)
    weight_body=_by_class(classes,[_fin_case('x',[rational_expr(weights[x][c]) for x in range(N)],N)
                                   for c in range(len(classes))],'(0 : ℚ)')
    law_body=_by_class(classes,[column(law) for law in laws],'(0 : ℚ)')
    mean_body=_fin_case('x',[column(row) for row in mean],N)
    class_names=', '.join(f'class_{c}' for c in range(len(classes)))
    lines=[
        'import PermanssonResearch.ApplicationBridge.OccupationReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact finite recurrent-class occupation receipt; application source candidate only.',
        f'    Model identity SHA-256: {receipt["model_semantic_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Infeasible P/U entries are normalized Dirac extensions. The realized limit',
        '    law is random (it depends on the class entered); the mean law is not it.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open MeasureTheory Filter',
        'open scoped Topology',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.OccupationReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.C10',
        'open PermanssonResearch.ReverseSolver.C11',
        'open PermanssonResearch.ReverseSolver.FiniteStrategicRealization',
        'open PermanssonResearch.MultipleLimit.FrozenObservedEvent',
        'open PermanssonResearch.MultipleLimit.CanonicalClassSelector',
        'open PermanssonResearch.MultipleLimit.FiniteStateOccupation',
        'open PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw',
        'attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        f'instance : NeZero {dim} := ⟨by norm_num⟩',
        f'def K : RationalMarkovMatrix {dim} := inducedMatrix input',
    ]
    for c,group in enumerate(classes):
        lines.append(f'def class_{c} : Finset (Fin {dim}) := {_finset(group,N)}')
    lines+=[
        f'def cert : DirichletCertificate {dim} where',
        f'  classes := {{{class_names}}}',
        f'  weight := fun C x => {weight_body}',
        f'def laws : Finset (Fin {dim}) → Fin {dim} → ℚ := fun C y => {law_body}',
        f'def mean : Fin {dim} → Fin {dim} → ℚ := fun x y => {mean_body}',
        '',
        '/-- Kernel evaluation: exact bottom classes, complete Dirichlet system (C10),',
        '    checked class stationary laws (C11) and mean laws as mixtures. -/',
        'theorem receipt_checked : checkJointClassReceipt K cert laws mean = true := by',
        '  decide +kernel','',
        'theorem dirichlet_checked : checkDirichlet K cert = true :=',
        '  (checkJointClassReceipt_sound K cert laws mean receipt_checked).1','',
        '/-- The listed classes are exactly the computed bottom classes of `K`. -/',
        'theorem classes_exact : cert.classes = bottomClasses K :=',
        '  checked_classes_exact K cert dirichlet_checked','',
    ]
    names=['receipt_checked','dirichlet_checked','classes_exact']
    for c in range(len(classes)):
        lines+=[f'theorem class_{c}_listed : class_{c} ∈ cert.classes := by',
                '  decide +kernel','',
                f'theorem class_{c}_stationary : checkClassStationary K (classCandidate laws class_{c}) = true :=',
                f'  checked_class_stationary K cert laws mean receipt_checked class_{c} class_{c}_listed','',
                f'/-- When class {c} is the selected recurrent class, the actual almost-sure',
                '    occupation limit is exactly the receipt\'s law for that class. -/',
                f'theorem random_limit_on_class_{c} : ∀ w : ℕ → PermanssonLean.JointState Unit (Fin {dim}),',
                f'    selectedRepresentative (realizedModel K).inducedKernel w ∈ decodedClass class_{c} →',
                '      physicalOccupationLimit (realizedModel K).inducedKernel w =',
                f'        certifiedProbability K (classCandidate laws class_{c}) class_{c}_stationary :=',
                f'  checked_random_limit_on_class K cert laws mean receipt_checked class_{c} class_{c}_listed','']
        names+=[f'class_{c}_listed',f'class_{c}_stationary',f'random_limit_on_class_{c}']
        for x in range(N):
            name=f'absorption_{c}_{x}'
            names.append(name)
            lines+=[f'/-- Actual probability of eventually entering class {c} from state {x}. -/',
                    f'theorem {name} :',
                    f'    ((realizedModel K).pathLaw (Measure.dirac (decode ({x} : Fin {N})))).real',
                    f'      (eventuallyObserved (fun y => decide (encode y ∈ class_{c})) true) =',
                    f'      (({rational_expr(weights[x][c])} : ℚ) : ℝ) := by',
                    f'  rw [checked_class_absorption_actual K cert dirichlet_checked class_{c} class_{c}_listed]',
                    f'  have hv : cert.weight class_{c} ({x} : Fin {N}) = {rational_expr(weights[x][c])} := by',
                    '    decide +kernel',
                    '  rw [hv]','']
    lines+=['/-- Almost-sure convergence of the empirical occupation from every start. -/',
            f'theorem occupation_limit : ∀ x : Fin {dim},',
            '    ∀ᵐ w ∂(realizedModel K).pathLaw (Measure.dirac (decode x)),',
            '      Tendsto (fun t : ℕ => empiricalOccupation w (t + 1) (Nat.succ_pos t)) atTop',
            '        (𝓝 (physicalOccupationLimit (realizedModel K).inducedKernel w)) :=',
            '  occupation_ae_limit K','',
            '/-- The whole law of the random occupation limit is the receipt\'s Dirac',
            '    mixture of class laws with the receipt\'s weights. -/',
            f'theorem random_limit_law : ∀ x : Fin {dim},',
            '    ((realizedModel K).pathLaw (Measure.dirac (decode x))).map',
            '        (physicalOccupationLimit (realizedModel K).inducedKernel) =',
            '      ∑ C ∈ cert.classes.attach,',
            '        ENNReal.ofReal (cert.weight C.1 x : ℝ) •',
            '          Measure.dirac (certifiedProbability K (classCandidate laws C.1)',
            '            (checked_class_stationary K cert laws mean receipt_checked C.1 C.2)) :=',
            '  random_limit_law_eq_receipt K cert laws mean receipt_checked','']
    names+=['occupation_limit','random_limit_law']
    lines+=['/-- Every mean law is only the barycenter of the random law: the mixture',
            '    of class laws weighted by actual eventual-entry probabilities. -/',
            f'theorem mean_mixture : ∀ x y : Fin {dim}, (mean x y : ℝ) = ∑ C ∈ bottomClasses K,',
            '    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real',
            '      (eventuallyObserved (fun z => decide (encode z ∈ C)) true) * (laws C y : ℝ) :=',
            '  checked_mean_mixture K cert laws mean receipt_checked','']
    names.append('mean_mixture')
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('OCCUPATION_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['model_semantic_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'bottom_classes':len(classes),
                 'interpretation':'RANDOM_CLASS_STATIONARY_LAW_NOT_ITS_MEAN',
                 'not_claimed':['gr_pr_recovery','c10_original_margin']},
        'p_u_infeasible_normalized_extensions':extensions,
        'lean_status':'NOT_EXECUTED',
        'source_emitted':True,
        'compiler_evidence_authenticated':False,
        'independent_math_certification':False,
        'empirical_identification':False,
        'application_release_authorized':False,
    }
    return text,out


def emit_files(model_file:Path,receipt_file:Path,out_dir:Path)->dict:
    model_raw,model=strict_read(model_file)
    receipt_raw,receipt=read_result(receipt_file)
    lean,metadata=emit_source(model,receipt)
    metadata['problem_bytes_sha256']=sha256(model_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedOccupation.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedOccupation.lean'),
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
