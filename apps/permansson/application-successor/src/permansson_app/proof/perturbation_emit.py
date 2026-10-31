"""Checked finite-horizon perturbation receipt -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent perturbation checker are emitted. The
baseline and alternative models are reflected as separate `FiniteWorldInput`s
and compared through their α/P/U-induced matrices. The emitted theorems bound
every row's actual one-step event TV by its half-L1 distance, identify both
initial-law event probabilities with actual region-survival probabilities and
bound their difference by the checked budget `min 1 (TV(μ, ν) + T δ)` using
the core Proposition 5.4. This is a finite-horizon comparison only: no
long-run, GR/PR or causal claim. Emission is never compiler replay,
independent certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.robustness import parse_perturbation
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.robustness import check_perturbation
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _finset, _nat_case, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.PerturbationLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedPerturbation'
MAX_HORIZON=6
MAX_SOURCE_BYTES=512*1024


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('PERTURBATION_REIFY_INPUT','raw perturbation problem and receipt required')
    problem=parse_perturbation(raw)
    checked=check_perturbation(problem,receipt)
    H=problem.horizon
    if not H<=MAX_HORIZON:
        raise AppError('PERTURBATION_REIFY_SCOPE',f'Lean perturbation reflection limited to 0..{MAX_HORIZON} transitions')
    base_lines,(ns,nx,na),base_ext=input_definition(problem.baseline,'base')
    alt_lines,dims,alt_ext=input_definition(problem.alternative,'alt')
    if dims!=(ns,nx,na):
        raise AppError('PERTURBATION_REIFY_SCOPE','alternative must share the baseline dimensions')
    N=ns*nx
    q=lambda key:exact_result(receipt[key],probability=True)
    rows=[exact_result(v,probability=True) for v in receipt['row_total_variations']]
    base=[[exact_result(v,probability=True) for v in row] for row in receipt['baseline_survival_rows']]
    alt=[[exact_result(v,probability=True) for v in row] for row in receipt['alternative_survival_rows']]
    delta,tv0,bound=q('maximum_row_tv'),q('initial_law_tv'),q('bound_at_horizon')
    pb,pa=q('baseline_event_probability'),q('alternative_event_probability')

    dim=f'({ns} * {nx})'
    def vector(values,var='y'):return _fin_case(var,[rational_expr(v) for v in values],N)
    def table(rows_):return _nat_case('t',[vector(r) for r in rows_],'(0 : ℚ)')
    lines=[
        'import PermanssonResearch.ApplicationBridge.QuantitativeReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact finite-horizon perturbation receipt; application source candidate only.',
        f'    Problem identity SHA-256: {receipt["problem_semantic_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Finite-horizon region-survival comparison of two declared chains; no long-run,',
        '    GR/PR or causal claim. Infeasible P/U entries are normalized Dirac extensions.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonLean.ProbabilitySupport',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.ExitReceipt',
        'open PermanssonResearch.ApplicationBridge.QuantitativeReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.FiniteStrategicRealization',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *base_lines,'',*alt_lines,'',
        f'def K : RationalMarkovMatrix {dim} := inducedMatrix base',
        f'def L : RationalMarkovMatrix {dim} := inducedMatrix alt',
        f'def region : Finset (Fin {dim}) := {_finset(list(problem.region),N)}',
        f'def horizon : ℕ := {H}',
        f'def μ : Fin {dim} → ℚ := fun y => {vector(problem.initial_baseline)}',
        f'def ν : Fin {dim} → ℚ := fun y => {vector(problem.initial_alternative)}',
        f'def rows : Fin {dim} → ℚ := fun y => {vector(rows)}',
        f'def δ : ℚ := {rational_expr(delta)}',
        f'def tv0 : ℚ := {rational_expr(tv0)}',
        f'def bound : ℚ := {rational_expr(bound)}',
        f'def baseTable : ℕ → Fin {dim} → ℚ := fun t y => {table(base)}',
        f'def altTable : ℕ → Fin {dim} → ℚ := fun t y => {table(alt)}',
        f'def pb : ℚ := {rational_expr(pb)}',
        f'def pa : ℚ := {rational_expr(pa)}',
        '',
        '/-- Kernel evaluation of row distances, laws, budget and both survival tables. -/',
        'theorem receipt_checked :',
        '    checkFiniteTVBudget K L region horizon μ ν rows δ tv0 bound baseTable altTable pb pa = true := by',
        '  decide +kernel','',
    ]
    args='K L region horizon μ ν rows δ tv0 bound baseTable altTable pb pa receipt_checked'
    mix=lambda law,M:(f'∑ y, ({law} y : ℝ) *\n'
                      f'        ((realizedModel {M}).pathLaw (Measure.dirac (decode y))).real (staysThrough region horizon)')
    lines+=[
        '/-- Actual initial-law region-survival probabilities of the two chains. -/',
        'theorem event_probabilities :',
        f'    (({rational_expr(pb)} : ℚ) : ℝ) = {mix("μ","K")} ∧',
        f'    (({rational_expr(pa)} : ℚ) : ℝ) = {mix("ν","L")} := by',
        f'  have h := checked_event_probabilities {args}',
        f'  have hb : pb = {rational_expr(pb)} := by decide +kernel',
        f'  have ha : pa = {rational_expr(pa)} := by decide +kernel',
        '  rw [hb, ha] at h',
        '  exact h','',
        '/-- The actual survival probabilities differ by at most the checked budget. -/',
        'theorem perturbation_bound :',
        f'    |{mix("μ","K")} -',
        f'      {mix("ν","L")}| ≤',
        f'      (({rational_expr(bound)} : ℚ) : ℝ) := by',
        f'  have h := checked_perturbation_bound {args}',
        f'  have hv : bound = {rational_expr(bound)} := by decide +kernel',
        '  rw [hv] at h',
        '  exact h','',
    ]
    names=['receipt_checked','event_probabilities','perturbation_bound']
    for y,v in enumerate(rows):
        name=f'row_event_tv_{y}'
        names.append(name)
        lines+=[f'/-- Actual one-step event TV of row {y} is at most its half-L1 distance. -/',
                f'theorem {name} :',
                f'    eventTotalVariation ((realizedModel K).inducedKernel (decode ({y} : Fin {N})))',
                f'      ((realizedModel L).inducedKernel (decode ({y} : Fin {N}))) ≤ (({rational_expr(v)} : ℚ) : ℝ) := by',
                f'  have h := checked_row_eventTV {args} ({y} : Fin {N})',
                f'  have hv : rows ({y} : Fin {N}) = {rational_expr(v)} := by decide +kernel',
                '  rw [hv] at h',
                '  exact h','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('PERTURBATION_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['problem_semantic_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'horizon':H,
                 'region':list(problem.region),
                 'interpretation':'FINITE_HORIZON_REGION_SURVIVAL_TV_BUDGET_ONLY'},
        'p_u_infeasible_normalized_extensions':{'base':base_ext,'alt':alt_ext},
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
    receipt_raw,receipt=read_result(receipt_file)
    lean,metadata=emit_source(problem,receipt)
    metadata['problem_bytes_sha256']=sha256(problem_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedPerturbation.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedPerturbation.lean'),
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
