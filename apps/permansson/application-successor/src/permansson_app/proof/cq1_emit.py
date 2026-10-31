"""Checked CQ-1 finite certificate receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent CQ-1 checker and report a finite
constitutive certificate are emitted. The baseline and the treated model are
reflected as `FiniteWorldInput`s; the treated one is proved to keep the
feasible actions and P (and α or U when only the other is declared). Their
α/P/U-induced matrices drive Research's realized typed model and its typed
admissible strategic intervention. Lean checks region-wide survival, the
comparison effects and the margin, constructs `FiniteConstitutiveCertificate`
and identifies the margin with the original constitutive margin. Emission is
never compiler replay, independent certification, empirical identification
or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.cq1 import parse_cq1
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.cq1 import check_cq1
from ..strict_json import strict_read
from .control_emit import _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT = 'Permansson.App.CQ1LeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedCQ1'
MAX_SOURCE_BYTES = 512 * 1024
MAX_HORIZON = 6


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('CQ1_REIFY_INPUT', 'raw CQ-1 request and receipt required')
    checked = check_cq1(raw, receipt)
    if receipt['certificate_status'] != 'FINITE_CONSTITUTIVE_CERTIFICATE':
        raise AppError('CQ1_REIFY_SCOPE', 'only a reported finite constitutive certificate is bound')
    base, treated, check, states, region, basin, comparison, prop, h, eta = parse_cq1(raw)
    if h > MAX_HORIZON:
        raise AppError('CQ1_REIFY_SCOPE', f'Lean CQ-1 reflection limited to horizon 0..{MAX_HORIZON}')
    base_lines, dims, base_ext = input_definition(base, 'base')
    treated_lines, tdims, treated_ext = input_definition(treated, 'treated')
    if dims != tdims:
        raise AppError('CQ1_REIFY_SCOPE', 'treated model must share dimensions')
    ns, nx, na = dims
    N = ns * nx
    assert list(states) == [(s, x) for s in base.strategic for x in base.world]
    dim = f'({ns} * {nx})'
    def fs(items):
        return _finset([states.index(y) for y in items], N)
    def idx(y):
        return f'({states.index(y)} : Fin {N})'
    kappa = exact_ratio(receipt['uniform_margin'])
    y1, y2 = comparison[0], comparison[1]
    El, Kl = rational_expr(eta), rational_expr(kappa)
    target = check['target']
    lines = [
        'import PermanssonResearch.ApplicationBridge.FiniteScoreReceipt',
        'import Mathlib.Tactic', '',
        '/-! Reified exact CQ-1 finite constitutive certificate; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        f'    Declared intervention target: {target}; property: stay in the property set at times',
        f'    0..{h}. Exact finite model only: no error-budget transport, Exact GR/PR or QSD.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonLean PermanssonLean.RegimeSpecification',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ApplicationBridge.FiniteScoreReceipt',
        'open PermanssonResearch.ConstitutiveQuasi',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.FiniteStrategicRealization',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0', '',
        *base_lines, '',
        *treated_lines, '',
        '/-- The treated model keeps the feasible actions and the world kernel P. -/',
        'theorem treated_held_fixed : HeldFixed base treated := by',
        '  unfold HeldFixed',
        '  simp only [base, treated]',
        '  decide +kernel', '',
    ]
    names = ['treated_held_fixed']
    if target == 'alpha':
        lines += ['theorem treated_update_held_fixed :',
                  '    ∀ s x a xp sp, treated.update s x a xp sp = base.update s x a xp sp := by',
                  '  simp only [base, treated]',
                  '  decide +kernel', '']
        names.append('treated_update_held_fixed')
    elif target == 'U':
        lines += ['theorem treated_alpha_held_fixed :',
                  '    ∀ s x a, treated.alpha s x a = base.alpha s x a := by',
                  '  simp only [base, treated]',
                  '  decide +kernel', '']
        names.append('treated_alpha_held_fixed')
    lines += [
        f'def K₀ : RationalMarkovMatrix {dim} := inducedMatrix base',
        f'def K₁ : RationalMarkovMatrix {dim} := inducedMatrix treated',
        f'def R : Finset (Fin {dim}) := {fs(region)}',
        f'def basin : Finset (Fin {dim}) := {fs(basin)}',
        f'def B₁ : Finset (Fin {dim}) := {fs(comparison)}',
        f'def Q : Finset (Fin {dim}) := {fs(prop)}',
        f'def η : ℚ := {El}',
        f'def κ : ℚ := {Kl}', '',
        '/-- Kernel evaluation: inclusions, region-wide persistence, margin and attainment. -/',
        'theorem receipt_checked :',
        f'    checkCQ1 K₀ K₁ R basin B₁ Q {h} η κ {idx(y1)} {idx(y2)} = true := by',
        '  decide +kernel', '',
        '/-- CQ-1: a finite constitutive certificate for the realized typed model with a',
        '    comparison set whose states are exactly `B₁`, and its exact margin. -/',
        'theorem finite_constitutive_certificate :',
        f'    ∃ C : ConstitutiveComparisonSet (realizedModel K₀) (spec R basin),',
        '      C.states = liftSet B₁ ∧',
        '      FiniteConstitutiveCertificate (realizedModel K₀) (spec R basin)',
        f'        (researchActionFamily K₀) C (rationalStrategicIntervention K₀ K₁) {h}',
        f'        (prefixScore Q {h}) (ENNReal.ofReal (({El} : ℚ) : ℝ)) (({Kl} : ℚ) : ℝ) ∧',
        '      constitutiveMargin (realizedModel K₀) (spec R basin) (researchActionFamily K₀)',
        f'        ((prefixScore Q {h}).toRegimeProperty {h}) C (rationalStrategicIntervention K₀ K₁) =',
        f'          (({Kl} : ℚ) : ℝ) := by',
        f'  have h := checked_finite_constitutive_certificate K₀ K₁ R basin B₁ Q {h} η κ',
        f'    {idx(y1)} {idx(y2)} receipt_checked',
        f'  have hη : η = {El} := by decide +kernel',
        f'  have hκ : κ = {Kl} := by decide +kernel',
        '  rw [hη, hκ] at h',
        '  exact h', '',
    ]
    names += ['receipt_checked', 'finite_constitutive_certificate']
    for row in receipt['region_survival']:
        y = tuple(row['state']); k = states.index(y); v = rational_expr(exact_ratio(row['survival']))
        name = f'region_survival_{k}'
        names.append(name)
        lines += [f'theorem {name} :',
                  f'    survivalProbability (realizedModel K₀) (spec R basin) (decode ({k} : Fin {N})) {h} =',
                  f'      ENNReal.ofReal (({v} : ℚ) : ℝ) := by',
                  '  rw [survivalProbability_eq]',
                  f'  have hv : survival K₀ R {h} ({k} : Fin {N}) = {v} := by decide +kernel',
                  '  rw [hv]', '']
    for row in receipt['comparison_effects']:
        y = tuple(row['state']); k = states.index(y)
        b = rational_expr(exact_ratio(row['baseline_property']))
        t = rational_expr(exact_ratio(row['intervened_property']))
        names += [f'baseline_property_{k}', f'intervened_property_{k}']
        lines += [f'theorem baseline_property_{k} :',
                  f'    baselinePropertyValue ((prefixScore Q {h}).toRegimeProperty {h}) (realizedModel K₀)',
                  f'      (decode ({k} : Fin {N})) = (({b} : ℚ) : ℝ) := by',
                  '  rw [baseline_value]',
                  f'  have hv : survival K₀ Q {h} ({k} : Fin {N}) = {b} := by decide +kernel',
                  '  rw [hv]', '',
                  f'theorem intervened_property_{k} :',
                  f'    intervenedPropertyValue ((prefixScore Q {h}).toRegimeProperty {h})',
                  f'      (rationalStrategicIntervention K₀ K₁).intervention (decode ({k} : Fin {N})) =',
                  f'        (({t} : ℚ) : ℝ) := by',
                  '  rw [intervened_value]',
                  f'  have hv : survival K₁ Q {h} ({k} : Fin {N}) = {t} := by decide +kernel',
                  '  rw [hv]', '']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('CQ1_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'ns': ns, 'nx': nx, 'na': na, 'joint_states': N, 'horizon': h,
                  'intervention_target': target,
                  'certificate': 'RESEARCH_FINITE_CONSTITUTIVE_CERTIFICATE_ON_REALIZED_TYPED_MODEL',
                  'property': 'PREFIX_SURVIVAL_IN_PROPERTY_SET',
                  'not_claimed': ['exact_GR', 'exact_PR', 'QSD', 'error_budget_transport',
                                  'terminal_scores']},
        'p_u_infeasible_normalized_extensions': {'base': base_ext, 'treated': treated_ext},
        'lean_status': 'NOT_EXECUTED',
        'source_emitted': True,
        'compiler_evidence_authenticated': False,
        'independent_math_certification': False,
        'empirical_identification': False,
        'application_release_authorized': False,
    }
    return text, out


def emit_files(request_file: Path, receipt_file: Path, out_dir: Path) -> dict:
    request_raw, request = strict_read(request_file)
    receipt_raw, receipt = strict_read(receipt_file)
    lean, metadata = emit_source(request, receipt)
    metadata['problem_bytes_sha256'] = sha256(request_raw).hexdigest()
    metadata['receipt_bytes_sha256'] = sha256(receipt_raw).hexdigest()
    destination = _new_dir(out_dir)
    (destination / 'ReifiedCQ1.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedCQ1.lean'),
            'metadata_file': str(destination / 'source_candidate.json'),
            'lean_status': 'NOT_EXECUTED', 'candidate_sha256': metadata['lean_source_sha256']}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request', type=Path)
    parser.add_argument('receipt', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        print(json.dumps(emit_files(args.request, args.receipt, args.output), sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok': False, 'error': {'code': exc.code, 'message': str(exc)}}, sort_keys=True),
              file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
