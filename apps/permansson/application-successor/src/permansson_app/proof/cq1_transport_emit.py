"""Checked CQ-1 transport receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent transport checker and report a
transported certificate are emitted. The certified baseline and treated
model and the approximate pair are reflected as `FiniteWorldInput`s; each is
proved to keep the certified baseline's feasible actions and P. Their
α/P/U-induced matrices drive Research's realized typed models. Lean decides
the CQ-1 checks and the row budgets with the remaining-margin condition, and
states the approximate pair's transported `FiniteConstitutiveCertificate`
with the literal persistence error and margin. Emission is never compiler
replay, independent certification, empirical identification or release
acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.cq1_transport import parse_transport
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.cq1_transport import check_cq1_transport
from ..strict_json import strict_read, read_result
from .control_emit import _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT = 'Permansson.App.CQ1TransportLeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedCQ1Transport'
MAX_SOURCE_BYTES = 512 * 1024
MAX_HORIZON = 6


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('CQ1_TRANSPORT_REIFY_INPUT', 'raw transport request and receipt required')
    checked = check_cq1_transport(raw, receipt)
    if receipt['transport_status'] != 'TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE':
        raise AppError('CQ1_TRANSPORT_REIFY_SCOPE', 'only a transported certificate is bound')
    (base, treated, check, states, region, basin, comparison, prop, h, eta), a0, a1 = parse_transport(raw)
    if h > MAX_HORIZON:
        raise AppError('CQ1_TRANSPORT_REIFY_SCOPE', f'Lean transport reflection limited to horizon 0..{MAX_HORIZON}')
    reflected = {}
    for name, model in (('base', base), ('treated', treated), ('approxBase', a0), ('approxTreated', a1)):
        reflected[name] = input_definition(model, name)
    if len({dims for _, dims, _ in reflected.values()}) != 1:
        raise AppError('CQ1_TRANSPORT_REIFY_SCOPE', 'all four models must share dimensions')
    ns, nx, na = reflected['base'][1]
    N = ns * nx
    dim = f'({ns} * {nx})'

    def fs(items):
        return _finset([states.index(y) for y in items], N)

    def idx(y):
        return f'({states.index(y)} : Fin {N})'

    cq1 = receipt['cq1_receipt']
    El, Kl = rational_expr(eta), rational_expr(exact_result(cq1['uniform_margin']))
    D0, DJ = rational_expr(exact_result(receipt['delta_baseline'])), rational_expr(exact_result(receipt['delta_intervention']))
    E0 = rational_expr(exact_result(receipt['envelope_baseline']))
    Ml = rational_expr(exact_result(receipt['transported_margin']))
    y1, y2 = comparison[0], comparison[1]
    lines = [
        'import PermanssonResearch.ApplicationBridge.CQ1TransportReceipt',
        'import Mathlib.Tactic', '',
        '/-! Reified exact CQ-1 certificate transport; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        f'    Declared intervention target: {check["target"]}; horizon {h}. The budgets are exact',
        '    row TV distances between declared models, not empirical error estimates.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonLean PermanssonLean.RegimeSpecification',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ApplicationBridge.FiniteScoreReceipt',
        'open PermanssonResearch.ApplicationBridge.CQ1TransportReceipt',
        'open PermanssonResearch.ConstitutiveQuasi',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.FiniteStrategicRealization',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0', '',
    ]
    names = []
    for name, (model_lines, _, _) in reflected.items():
        lines += [*model_lines, '']
        if name != 'base':
            theorem = f'{name}_held_fixed'
            names.append(theorem)
            lines += [f'/-- `{name}` keeps the certified baseline\'s feasible actions and P. -/',
                      f'theorem {theorem} : HeldFixed base {name} := by',
                      '  unfold HeldFixed',
                      f'  simp only [base, {name}]',
                      '  decide +kernel', '']
    lines += [
        f'def K₀ : RationalMarkovMatrix {dim} := inducedMatrix base',
        f'def K₁ : RationalMarkovMatrix {dim} := inducedMatrix treated',
        f'def A₀ : RationalMarkovMatrix {dim} := inducedMatrix approxBase',
        f'def A₁ : RationalMarkovMatrix {dim} := inducedMatrix approxTreated',
        f'def R : Finset (Fin {dim}) := {fs(region)}',
        f'def basin : Finset (Fin {dim}) := {fs(basin)}',
        f'def B₁ : Finset (Fin {dim}) := {fs(comparison)}',
        f'def Q : Finset (Fin {dim}) := {fs(prop)}',
        f'def η : ℚ := {El}',
        f'def κ : ℚ := {Kl}',
        f'def δ₀ : ℚ := {D0}',
        f'def δJ : ℚ := {DJ}', '',
        '/-- Kernel evaluation of the certified CQ-1 receipt. -/',
        'theorem receipt_checked :',
        f'    checkCQ1 K₀ K₁ R basin B₁ Q {h} η κ {idx(y1)} {idx(y2)} = true := by',
        '  decide +kernel', '',
        '/-- Kernel evaluation of the row budgets and the remaining-margin condition. -/',
        f'theorem transport_checked : checkTransport K₀ K₁ A₀ A₁ {h} κ δ₀ δJ = true := by',
        '  decide +kernel', '',
        '/-- The approximate realized pair carries a transported finite constitutive',
        '    certificate for the same specification and comparison states. -/',
        'theorem transported_certificate :',
        '    ∃ C : ConstitutiveComparisonSet (realizedModel K₀) (spec R basin),',
        '      C.states = liftSet B₁ ∧',
        '      (transportComparisonSet (realizedModel K₀) (realizedModel A₀) (spec R basin) C).states =',
        '        liftSet B₁ ∧',
        '      FiniteConstitutiveCertificate (realizedModel A₀) (spec R basin) (researchActionFamily A₀)',
        '        (transportComparisonSet (realizedModel K₀) (realizedModel A₀) (spec R basin) C)',
        f'        (rationalStrategicIntervention A₀ A₁) {h} (prefixScore Q {h})',
        f'        (clampedPersistenceError (ENNReal.ofReal (({El} : ℚ) : ℝ)) (({E0} : ℚ) : ℝ))',
        f'        (({Ml} : ℚ) : ℝ) := by',
        f'  have h := checked_transported_certificate K₀ K₁ A₀ A₁ R basin B₁ Q {h} η κ δ₀ δJ',
        f'    {idx(y1)} {idx(y2)} receipt_checked transport_checked',
        f'  have hm : κ - env δ₀ {h} - env δJ {h} = {Ml} := by decide +kernel',
        f'  have hη : η = {El} := by decide +kernel',
        f'  have he : env δ₀ {h} = {E0} := by decide +kernel',
        '  rw [hm, hη, he] at h',
        '  exact h', '',
        f'end {MODULE}', '',
    ]
    names += ['receipt_checked', 'transport_checked', 'transported_certificate']
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('CQ1_TRANSPORT_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'ns': ns, 'nx': nx, 'na': na, 'joint_states': N, 'horizon': h,
                  'intervention_target': check['target'],
                  'certificate': 'RESEARCH_TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE_ON_APPROXIMATE_REALIZED_MODEL',
                  'not_claimed': ['exact_GR', 'exact_PR', 'QSD', 'empirical_error_estimates']},
        'p_u_infeasible_normalized_extensions': {name: ext for name, (_, _, ext) in reflected.items()},
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
    receipt_raw, receipt = read_result(receipt_file)
    lean, metadata = emit_source(request, receipt)
    metadata['problem_bytes_sha256'] = sha256(request_raw).hexdigest()
    metadata['receipt_bytes_sha256'] = sha256(receipt_raw).hexdigest()
    destination = _new_dir(out_dir)
    (destination / 'ReifiedCQ1Transport.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedCQ1Transport.lean'),
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
