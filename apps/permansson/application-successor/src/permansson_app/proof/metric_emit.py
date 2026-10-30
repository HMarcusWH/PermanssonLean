"""Checked finite metric contraction receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent metric checker and report a strict W1
contraction are emitted. The baseline and perturbed models are reflected as
`FiniteWorldInput`s and their α/P/U-induced matrices are the two Markov
kernels on the declared finite metric space. Every transport certificate of
the receipt is emitted as literal data: couplings for all ordered row pairs
(the reverse pair is the transpose and the diagonal pair keeps the row in
place), per-row defect couplings, both invariant laws, and the invariant
coupling with its potential. Lean checks them, proves Research's
`IsW1Contraction`, assembles `ContractivePerturbation` for the A3 bound and
identifies the exact invariant-law distance. Emission is never compiler
replay, independent certification, empirical identification or release
acceptance.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.metric import parse_metric
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.metric import check_metric
from ..strict_json import strict_read
from .control_emit import _fin_case, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT = 'Permansson.App.MetricLeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedMetric'
MAX_SOURCE_BYTES = 768 * 1024


def _matrix(rows):
    return [[exact_ratio(v) for v in row] for row in rows]


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('METRIC_REIFY_INPUT', 'raw metric request and receipt required')
    checked = check_metric(raw, receipt)
    if receipt['contraction_status'] != 'STRICT_W1_CONTRACTION':
        raise AppError('METRIC_REIFY_SCOPE', 'only a strict W1 contraction is bound')
    base, pert, states, d = parse_metric(raw)
    base_lines, dims, base_ext = input_definition(base, 'base')
    pert_lines, pdims, pert_ext = input_definition(pert, 'pert')
    if dims != pdims:
        raise AppError('METRIC_REIFY_SCOPE', 'perturbed model must share dimensions')
    ns, nx, na = dims
    N = ns * nx
    assert len(states) == N
    K = _matrix(receipt['baseline_kernel'])
    zero = Fraction(0)
    pair = {}
    for cert in receipt['row_pair_transport']:
        x, y = states.index(tuple(cert['a'])), states.index(tuple(cert['b']))
        C = _matrix(cert['coupling'])
        pair[x, y] = C
        pair[y, x] = [[C[j][i] for j in range(N)] for i in range(N)]
    for x in range(N):
        pair[x, x] = [[K[x][i] if i == j else zero for j in range(N)] for i in range(N)]
    defect = [_matrix(c['coupling']) for c in receipt['row_defects']]
    inv = receipt['invariant_transport']
    rho = exact_ratio(receipt['contraction_factor'])
    delta = exact_ratio(receipt['defect'])
    w = exact_ratio(inv['w1'])
    pi = [exact_ratio(v) for v in receipt['invariant_law']]
    pit = [exact_ratio(v) for v in receipt['perturbed_invariant_law']]
    dim = f'({ns} * {nx})'

    def vec(values, var):
        return _fin_case(var, [rational_expr(v) for v in values], N)

    def mat(rows, a, b):
        return _fin_case(a, [vec(row, b) for row in rows], N)

    cpair = _fin_case('x', [_fin_case('y', [mat(pair[x, y], 'i', 'j') for y in range(N)], N)
                            for x in range(N)], N)
    cdef = _fin_case('y', [mat(defect[y], 'i', 'j') for y in range(N)], N)
    Rl, Dl, Wl = rational_expr(rho), rational_expr(delta), rational_expr(w)
    lines = [
        'import PermanssonResearch.ApplicationBridge.MetricReceipt',
        'import PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'import Mathlib.Tactic', '',
        '/-! Reified exact finite metric contraction receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Kernels are the α/P/U-induced matrices on the declared finite metric space.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open MeasureTheory ProbabilityTheory',
        'open PermanssonResearch.Probability',
        'open PermanssonResearch.Perturbation',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MetricReceipt',
        'open PermanssonResearch.ReverseSolver',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0', '',
        *base_lines, '',
        *pert_lines, '',
        f'def K : RationalMarkovMatrix {dim} := inducedMatrix base',
        f'def Kt : RationalMarkovMatrix {dim} := inducedMatrix pert',
        f'def dm : Fin {dim} → Fin {dim} → ℚ := fun i j => {mat(d, "i", "j")}', '',
        '/-- The declared distances form a metric. -/',
        'theorem metric_checked : IsFiniteMetric dm := by',
        '  decide +kernel', '',
        'instance : Fact (IsFiniteMetric dm) := ⟨metric_checked⟩', '',
        f'def ρ : ℚ := {Rl}',
        f'def δ : ℚ := {Dl}',
        f'def w : ℚ := {Wl}',
        f'def Cpair : Fin {dim} → Fin {dim} → Fin {dim} → Fin {dim} → ℚ := fun x y i j => {cpair}',
        f'def Cdef : Fin {dim} → Fin {dim} → Fin {dim} → ℚ := fun y i j => {cdef}',
        f'def π : Fin {dim} → ℚ := fun i => {vec(pi, "i")}',
        f'def πt : Fin {dim} → ℚ := fun i => {vec(pit, "i")}',
        f'def Cinv : Fin {dim} → Fin {dim} → ℚ := fun i j => {mat(_matrix(inv["coupling"]), "i", "j")}',
        f'def f : Fin {dim} → ℚ := fun i => {vec([exact_ratio(v) for v in inv["potential"]], "i")}', '',
        '/-- Kernel evaluation: metric, couplings, invariance, potential and contraction. -/',
        'theorem receipt_checked : checkMetricReceipt dm K Kt ρ δ w Cpair Cdef π πt Cinv f = true := by',
        '  decide +kernel', '',
        '/-- The baseline kernel is a W1 contraction against every pair of probability laws. -/',
        f'theorem row_contraction : IsW1Contraction (kernel dm K) (({Rl} : ℚ) : ℝ) := by',
        '  have h := checked_row_contraction K Kt ρ δ w Cpair Cdef π πt Cinv f receipt_checked',
        f'  have hρ : ρ = {Rl} := by decide +kernel',
        '  rw [hρ] at h',
        '  exact h', '',
        '/-- A3 invariant-law perturbation bound from `ContractivePerturbation`. -/',
        'theorem invariant_metric_bound :',
        '    ∃ (hπ : IsProb π) (hπt : IsProb πt),',
        '      kernel dm K ∘ₘ law dm π hπ = law dm π hπ ∧ kernel dm Kt ∘ₘ law dm πt hπt = law dm πt hπt ∧',
        f'      W1DualLE (law dm π hπ) (law dm πt hπt) ((({Dl} : ℚ) : ℝ) / (1 - (({Rl} : ℚ) : ℝ))) := by',
        '  have h := checked_invariant_metric_bound K Kt ρ δ w Cpair Cdef π πt Cinv f receipt_checked',
        f'  have hρ : ρ = {Rl} := by decide +kernel',
        f'  have hδ : δ = {Dl} := by decide +kernel',
        '  rw [hρ, hδ] at h',
        '  exact h', '',
        '/-- The invariant laws are exactly at dual Kantorovich–Rubinstein distance `w`. -/',
        'theorem exact_invariant_transport :',
        '    ∃ (hπ : IsProb π) (hπt : IsProb πt),',
        f'      W1DualLE (law dm π hπ) (law dm πt hπt) (({Wl} : ℚ) : ℝ) ∧',
        f'      ∀ c : ℝ, W1DualLE (law dm π hπ) (law dm πt hπt) c → (({Wl} : ℚ) : ℝ) ≤ c := by',
        '  have h := finite_transport_certificate_sound K Kt ρ δ w Cpair Cdef π πt Cinv f receipt_checked',
        f'  have hw : w = {Wl} := by decide +kernel',
        '  rw [hw] at h',
        '  exact h', '',
        f'end {MODULE}', '',
    ]
    names = ['metric_checked', 'receipt_checked', 'row_contraction', 'invariant_metric_bound',
             'exact_invariant_transport']
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('METRIC_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'ns': ns, 'nx': nx, 'na': na, 'joint_states': N,
                  'space': 'DECLARED_FINITE_METRIC_ON_JOINT_STATES',
                  'conclusions': ['IsW1Contraction', 'ContractivePerturbation_A3_bound',
                                  'exact_dual_KR_distance_of_invariant_laws'],
                  'not_claimed': ['Polish_moment_invariance', 'occupation_margin_transport',
                                  'perturbed_contraction', 'empirical_metric']},
        'p_u_infeasible_normalized_extensions': {'base': base_ext, 'pert': pert_ext},
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
    (destination / 'ReifiedMetric.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedMetric.lean'),
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
