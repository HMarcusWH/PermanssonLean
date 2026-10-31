"""Checked risk-cap infeasibility receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent infeasibility checker are emitted.
The model is reflected as a `FiniteWorldInput`; the controlled rows are its
fixed-action P·U rows (`controlledMatrix`) and the admitted actions are
exactly the declared feasible ones, as in the flow bridge. The per-state risk
floors (the normalized Farkas ray) are literal rationals. Lean decides
`FloorChecks` and states that their initial-law total is the least risk mass
of every admissible real randomized one-step policy, attained, and that every
such policy exceeds the cap. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.risk_occupancy import parse_risk
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.risk_infeasibility import check_risk_infeasibility
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _finset, _new_dir, bound_system_lines
from .finite_emit import input_definition, rational_expr

FORMAT = 'Permansson.App.RiskInfeasibilityLeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedRiskInfeasibility'
MAX_SOURCE_BYTES = 256 * 1024


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('RISK_INFEASIBILITY_REIFY_INPUT', 'raw risk request and infeasibility receipt required')
    checked = check_risk_infeasibility(raw, receipt)
    q = parse_risk(raw)
    m = q.model
    input_lines, (ns, nx, na), extensions = input_definition(m)
    N = ns * nx
    states = list(q.states)
    if states != [(s, x) for s in m.strategic for x in m.world]:
        raise AppError('RISK_INFEASIBILITY_REIFY_SCOPE', 'joint states must follow the declared order')
    actions = list(m.actions)
    feasible = [[actions.index(a) for a in m.feasible[pair]] for pair in states]
    floors = [exact_result(v) for v in receipt['farkas_ray']['mass_multipliers']]
    total = exact_result(receipt['minimal_risk_probability'])
    dim = f'({ns} * {nx})'

    def vector(values):
        return _fin_case('y', [rational_expr(x) for x in values], N)

    lines = [
        'import PermanssonResearch.ApplicationBridge.FlowInfeasibilityReceipt',
        'import Mathlib.Tactic', '',
        '/-! Reified exact one-step risk-cap infeasibility receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    One transition, fully observed randomized Markov controls from the declared',
        '    initial law. The Farkas ray is checked, not assumed. P and U are fixed.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.FlowReceipt',
        'open PermanssonResearch.ApplicationBridge.FlowInfeasibilityReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0', '',
        *input_lines, '',
        *bound_system_lines(feasible, ns, nx, na),
        f'def rows : Fin {na} → RationalMarkovMatrix {dim} := fun a => controlledMatrix input a',
        f'def μ : Fin {dim} → ℚ := fun y => {vector(q.initial)}',
        f'def risk : Finset (Fin {dim}) := {_finset(list(q.risk_states), N)}',
        f'def cap : ℚ := {rational_expr(q.risk_cap)}',
        f'def v : Fin {dim} → ℚ := fun y => {vector(floors)}', '',
        '/-- Kernel evaluation: floors bound every admitted action, are attained, and exceed the cap. -/',
        'theorem receipt_checked : checkRiskFloors rows options μ risk cap v = true := by',
        '  decide +kernel', '',
        '/-- The least risk mass of every admissible real randomized policy, attained. -/',
        'theorem min_risk :',
        f'    (∀ π : Fin {dim} → Fin {na} → ℝ, Admissible options π →',
        f'      (({rational_expr(total)} : ℚ) : ℝ) ≤ riskMass rows μ risk π) ∧',
        f'    ∃ π : Fin {dim} → Fin {na} → ℝ, Admissible options π ∧',
        f'      riskMass rows μ risk π = (({rational_expr(total)} : ℚ) : ℝ) := by',
        '  have h := checked_min_risk rows options μ risk cap v receipt_checked',
        f'  have hv : (∑ y, v y * μ y) = {rational_expr(total)} := by decide +kernel',
        '  rw [hv] at h',
        '  exact h', '',
        '/-- Every admissible real randomized one-step policy exceeds the cap. -/',
        'theorem cap_infeasible :',
        f'    (∀ π : Fin {dim} → Fin {na} → ℝ, Admissible options π → (cap : ℝ) < riskMass rows μ risk π) ∧',
        f'    ¬ ∃ π : Fin {dim} → Fin {na} → ℝ, Admissible options π ∧ riskMass rows μ risk π ≤ cap :=',
        '  checked_cap_infeasible rows options μ risk cap v receipt_checked', '',
        f'end {MODULE}', '',
    ]
    names = ['options_exact', 'receipt_checked', 'min_risk', 'cap_infeasible']
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('RISK_INFEASIBILITY_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'ns': ns, 'nx': nx, 'na': na, 'joint_states': N,
                  'interpretation': 'EVERY_ADMISSIBLE_ONE_STEP_POLICY_EXCEEDS_THE_CAP',
                  'not_claimed': ['multi_stage_occupancy', 'private_information', 'empirical_identification']},
        'p_u_infeasible_normalized_extensions': extensions,
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
    (destination / 'ReifiedRiskInfeasibility.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedRiskInfeasibility.lean'),
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
