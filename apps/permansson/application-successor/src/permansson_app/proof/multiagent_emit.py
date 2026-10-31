"""Checked two-player protocol receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent multi-agent checker are emitted. The
canonical player, common-update and world tables become literal rational
tables in the encoded order of `MultiAgentReceipt`; Lean checks every row is
stochastic and that the receipt's baseline, closed-loop and open-loop joint
matrices are the product-protocol rows, then states that Research's assembled
`FiniteProduct.Generator` models have exactly those rows and the binary
path-law transport. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.multiagent import parse_multiagent
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.multiagent import check_multiagent
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _new_dir
from .finite_emit import rational_expr

FORMAT = 'Permansson.App.MultiAgentLeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedMultiAgent'
MAX_SOURCE_BYTES = 768 * 1024


def _nest(table, variables, dims):
    """Nested `_fin_case` over a nested list whose leaves are Fractions."""
    if not variables:
        return rational_expr(table)
    return _fin_case(variables[0], [_nest(t, variables[1:], dims[1:]) for t in table], dims[0])


def _binders(names, dims):
    """Lambda binders; a coordinate of dimension one is never referenced."""
    return ' '.join(n if d > 1 else '_' + n for n, d in zip(names, dims))


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('MULTIAGENT_REIFY_INPUT', 'raw multi-agent request and receipt required')
    checked = check_multiagent(raw, receipt)
    lab, (k0, k, nx, m), ps, common, world, i, repl, anchors = parse_multiagent(raw)
    N, M = k0 * k * k * nx, m * m
    dims = f'{k0} {k} {nx} {m}'

    def player(name, p):
        act, upd = p
        return [f'def {name} : Player {dims} :=',
                f'  ⟨fun {_binders("ya", [N, m])} => {_nest(act, ["y", "a"], [N, m])},',
                f'   fun {_binders("yaxs", [N, M, nx, k])} => {_nest(upd, ["y", "a", "x", "s"], [N, M, nx, k])}⟩']

    def matrix(name, rows):
        values = [[exact_result(v) for v in row] for row in rows]
        return f'def {name} : Fin (NJ {k0} {k} {nx}) → Fin (NJ {k0} {k} {nx}) → ℚ := fun y z => ' + \
            _nest(values, ['y', 'z'], [N, N])

    lines = [
        'import PermanssonResearch.ApplicationBridge.MultiAgentReceipt',
        'import Mathlib.Tactic', '',
        '/-! Reified exact two-player protocol receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        f'    Treated player {i}; physical P is never changed by a protocol.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open MeasureTheory ProbabilityTheory',
        'open PermanssonLean',
        'open PermanssonResearch.MultiAgent',
        'open PermanssonResearch.MultiAgent.FiniteProduct',
        'open PermanssonResearch.ApplicationBridge.MultiAgentReceipt',
        'set_option autoImplicit false',
        'set_option maxRecDepth 16384',
        'set_option maxHeartbeats 0', '',
        *player('p0', ps[0]), *player('p1', ps[1]), *player('r', repl),
        *player('anchor0', anchors[0]), *player('anchor1', anchors[1]), '',
        f'def ps : Fin 2 → Player {dims} := fun j => if j = 0 then p0 else p1',
        f'def anchor : Fin 2 → Player {dims} := fun j => if j = 0 then anchor0 else anchor1',
        f'def c : Shared {dims} :=',
        f'  ⟨fun {_binders("yaxs", [N, M, nx, k0])} => {_nest(common, ["y", "a", "x", "s"], [N, M, nx, k0])},',
        f'   fun {_binders("yax", [N, M, nx])} => {_nest(world, ["y", "a", "x"], [N, M, nx])}⟩',
        f'def i : Fin 2 := {i}',
        matrix('K', receipt['baseline_kernel']),
        matrix('Kc', receipt['closed_loop_kernel']),
        matrix('Ko', receipt['open_loop_kernel']), '',
        '/-- Kernel evaluation: stochastic rows and the three declared joint matrices. -/',
        'theorem receipt_checked : checkFiniteMultiAgentProtocol ps c i r anchor K Kc Ko = true := by',
        '  decide +kernel', '',
        'theorem hps : ∀ j, (ps j).OK := players_ok ps c i r anchor K Kc Ko receipt_checked',
        'theorem hc : c.OK := shared_ok ps c i r anchor K Kc Ko receipt_checked',
        'theorem hr : r.OK := replacement_ok ps c i r anchor K Kc Ko receipt_checked',
        'theorem ha : ∀ j, (anchor j).OK := anchor_ok ps c i r anchor K Kc Ko receipt_checked', '',
        '/-- The assembled baseline, closed-loop and open-loop models have the declared rows. -/',
        'theorem protocol_kernels :',
        f'    (∀ y z : JS {k0} {k} {nx}, ((generator ps hps c hc).toModel (world c hc)).inducedKernel y {{z}} =',
        '      ENNReal.ofReal (K (encState y) (encState z))) ∧',
        f'    (∀ y z : JS {k0} {k} {nx}, ((MeasurableProduct.closedLoop (generator ps hps c hc) i (mech r hr i)).toModel',
        '      (world c hc)).inducedKernel y {z} = ENNReal.ofReal (Kc (encState y) (encState z))) ∧',
        f'    (∀ y z : JS {k0} {k} {nx}, ((MeasurableProduct.openLoop (generator ps hps c hc) i (mech r hr i)',
        '      (fun j => mech (anchor j) (ha j) j)).toModel (world c hc)).inducedKernel y {z} =',
        '        ENNReal.ofReal (Ko (encState y) (encState z))) :=',
        '  checked_protocol_kernels ps c i r anchor K Kc Ko hps hc hr ha receipt_checked', '',
        '/-- Binary reduction: compressed path laws and binary atoms. -/',
        f'theorem marked_path_transport (μ : Measure (JS {k0} {k} {nx})) [IsProbabilityMeasure μ] :',
        '    (((generator ps hps c hc).toModel (world c hc)).pathLaw μ).map Two.compression.pathMap =',
        '      ((Two.binary (generator ps hps c hc)).toModel (Two.physical (world c hc))).pathLaw',
        '        (μ.map Two.state) ∧',
        f'    ∀ y z : JS {k0} {k} {nx},',
        '      ((Two.binary (generator ps hps c hc)).toModel (Two.physical (world c hc))).inducedKernel',
        '        (Two.state y) {Two.state z} = ENNReal.ofReal (K (encState y) (encState z)) :=',
        '  checked_marked_path_transport ps c i r anchor K Kc Ko hps hc hr ha receipt_checked μ', '',
        f'end {MODULE}', '',
    ]
    names = ['receipt_checked', 'hps', 'hc', 'hr', 'ha', 'protocol_kernels', 'marked_path_transport']
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('MULTIAGENT_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'common': k0, 'private': k, 'world': nx, 'actions': m, 'joint_states': N,
                  'treated_player': i,
                  'generic_research_closures': ['matched_closed_loop_original_margin',
                                                'matched_open_loop_original_margin'],
                  'not_claimed': ['asymmetric_player_types', 'mediated_or_correlated_actions',
                                  'private_clocks', 'empirical_game_identification']},
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
    (destination / 'ReifiedMultiAgent.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedMultiAgent.lean'),
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
