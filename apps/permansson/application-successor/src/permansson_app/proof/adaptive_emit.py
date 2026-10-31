"""Checked adaptive admitted-block receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent adaptive checker are emitted. The
baseline and every admitted block are reflected as `FiniteWorldInput`s with
the grammar bridge's per-block theorems (feasibility and P held fixed, exactly
the declared α/U patch rows). The blocks become the controls of
`AdaptiveBlockReceipt.blockSystem`, the region flag is `regionMonitor`, and
the reported Bellman table is a literal rational table. Lean decides the
table checks and states, for every start state, that the adaptive value
bounds every real full-history behavioral block controller on the actual
trace law and is attained. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.adaptive import parse_adaptive
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.adaptive import check_adaptive
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition, rational_expr
from .grammar_emit import block_definitions

FORMAT = 'Permansson.App.AdaptiveLeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedAdaptive'
MAX_HORIZON = 6
MAX_SOURCE_BYTES = 512 * 1024


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('ADAPTIVE_REIFY_INPUT', 'raw adaptive request and receipt required')
    checked = check_adaptive(raw, receipt)
    g = parse_adaptive(raw)
    if g.horizon > MAX_HORIZON:
        raise AppError('ADAPTIVE_REIFY_SCOPE', f'Lean adaptive reflection limited to horizon 0..{MAX_HORIZON}')
    base_lines, (ns, nx, na), base_ext = input_definition(g.baseline, 'base')
    N, k, H = ns * nx, len(g.blocks), g.horizon
    block_src, names, block_ext = block_definitions(g, ns, nx, na)
    dim = f'({ns} * {nx})'

    def layer(cells):
        return _fin_case('y', [f'(if s then {rational_expr(exact_result(alive))} else '
                               f'{rational_expr(exact_result(dead))})' for dead, alive in cells], N)

    table = ''.join(f'(if r = {r} then {layer(cells)} else ' for r, cells in enumerate(receipt['monitor_table'])) \
        + '(0 : ℚ)' + ')' * (H + 1)
    members = _fin_case('i', [f'inducedMatrix block_{i}' for i in range(k)], k) if k > 1 else 'inducedMatrix block_0'
    labels = ['{' + ', '.join(b) + '}' for b in g.blocks]
    lines = [
        'import PermanssonResearch.ApplicationBridge.AdaptiveBlockReceipt',
        'import Mathlib.Tactic', '',
        '/-! Reified exact adaptive admitted-block receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        f'    Controls (admitted blocks, in order): {"; ".join(labels)}. P is held fixed.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ApplicationBridge.AdaptiveBlockReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.ControlledKernel',
        'open PermanssonResearch.ReverseSolver.FiniteMonitor',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0', '',
        *base_lines, '',
        *block_src,
        f'def members : Fin {k} → RationalMarkovMatrix {dim} := fun {"i" if k > 1 else "_i"} => {members}',
        f'def sys : FiniteControlSystem (Fin {k}) {dim} := blockSystem (inducedMatrix base) members (by decide) (by decide)',
        f'def region : Finset (Fin {dim}) := {_finset(list(g.region), N)}',
        f'def M : Monitor (Fin {k}) {dim} Bool := regionMonitor region {"true" if g.value_type == "survival_horizon" else "false"}',
        f'def horizon : ℕ := {H}',
        f'def table : ℕ → Fin {dim} → Bool → ℚ := fun r y s => {table}', '',
        '/-- Kernel evaluation: the table starts at the reward and every layer is the',
        '    max over admitted blocks of the previous one. -/',
        'theorem receipt_checked : checkMonitorTable sys M horizon table = true := by',
        '  decide +kernel', '',
    ]
    names.append('receipt_checked')
    for y, value in zip(g.comparison, receipt['adaptive_values']):
        name = f'adaptive_optimal_{y}'
        names.append(name)
        v = rational_expr(exact_result(value))
        lines += [
            f'/-- From joint state {y}: no full-history behavioral block controller exceeds the',
            '    adaptive value on the actual trace law, and one attains it. -/',
            f'theorem {name} :',
            f'    (∀ σ : BehavioralPolicy sys, traceExpectation sys M σ horizon 0 (({y} : Fin {N}), [])',
            f'      ({y} : Fin {N}) (M.initial ({y} : Fin {N})) ≤ (({v} : ℚ) : ℝ)) ∧',
            f'    (∃ σ : BehavioralPolicy sys, traceExpectation sys M σ horizon 0 (({y} : Fin {N}), [])',
            f'      ({y} : Fin {N}) (M.initial ({y} : Fin {N})) = (({v} : ℚ) : ℝ)) := by',
            f'  have h := checked_adaptive_optimal sys M horizon table receipt_checked ({y} : Fin {N})',
            f'  have hv : table horizon ({y} : Fin {N}) (M.initial ({y} : Fin {N})) = {v} := by decide +kernel',
            '  rw [hv] at h',
            '  exact h', '']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('ADAPTIVE_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'ns': ns, 'nx': nx, 'na': na, 'joint_states': N, 'blocks': [list(b) for b in g.blocks],
                  'horizon': H, 'value_type': g.value_type,
                  'policy_class': 'FULL_HISTORY_BEHAVIORAL_OVER_DECLARED_BLOCKS',
                  'not_claimed': ['frozen_block_comparison', 'overlap_model_atom_certificate',
                                  'downward_closure', 'empirical_identification']},
        'p_u_infeasible_normalized_extensions': {'base': base_ext, **block_ext},
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
    (destination / 'ReifiedAdaptive.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedAdaptive.lean'),
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
