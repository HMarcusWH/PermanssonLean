"""Checked private-stage saddle receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent private-stage checker are emitted.
The payoff table, both mixtures, the value and the pure-control value become
literal rationals; Lean decides the two-sided saddle and pure-control checks
of `PrivateStageReceipt` and states that the value is the greatest private
value over every real mixed controller, the actual stage-law saddle, that
Research's executable `solvePrivateStage` returns exactly that value, and the
pure-control and revealed-control values. Emission is never compiler replay,
independent certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.private_stage import parse_private_stage
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.private_stage import check_private_stage
from ..strict_json import strict_read
from .control_emit import _fin_case, _new_dir
from .finite_emit import rational_expr

FORMAT = 'Permansson.App.PrivateStageLeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedPrivateStage'
MAX_SOURCE_BYTES = 64 * 1024


def _vector(variable, values):
    exprs = [rational_expr(v) for v in values]
    if len(exprs) == 1:
        return f'fun _{variable} => {exprs[0]}'
    return f'fun {variable} => {_fin_case(variable, exprs, len(exprs))}'


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('PRIVATE_STAGE_REIFY_INPUT', 'raw private-stage request and receipt required')
    checked = check_private_stage(raw, receipt)
    controls, nature, Q = parse_private_stage(raw)
    nc, nt = len(controls), len(nature)
    rows = [_fin_case('c', [rational_expr(x) for x in row], nc) if nc > 1 else rational_expr(row[0])
            for row in Q]
    binders = ('t' if nt > 1 else '_t') + ' ' + ('c' if nc > 1 else '_c')
    table = rows[0] if nt == 1 else _fin_case('t', rows, nt)
    p = [exact_result(v) for v in receipt['controller_mixture']]
    q = [exact_result(v) for v in receipt['nature_mixture']]
    lines = [
        'import PermanssonResearch.ApplicationBridge.PrivateStageReceipt',
        'import Mathlib.Tactic', '',
        '/-! Reified exact private-stage saddle receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        f'    Controls (Fin {nc}): {", ".join(controls)}; nature (Fin {nt}): {", ".join(nature)}.',
        '    Nature sees the mixture, not the realized control.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open PermanssonResearch.ActionTrace',
        'open PermanssonResearch.ReverseSolver.PrivateControlStage',
        'open PermanssonResearch.ApplicationBridge.PrivateStageReceipt',
        'set_option autoImplicit false', '',
        f'def Q : Fin {nt} → Fin {nc} → ℚ := fun {binders} => {table}',
        f'def p : Fin {nc} → ℚ := {_vector("c", p)}',
        f'def q : Fin {nt} → ℚ := {_vector("t", q)}',
        f'def v : ℚ := {rational_expr(exact_result(receipt["value"]))}',
        f'def r : ℚ := {rational_expr(exact_result(receipt["pure_control_value"]))}', '',
        '/-- Kernel evaluation: both saddle sides and the pure-control value. -/',
        'theorem receipt_checked : checkPrivateStage Q p q v r = true := by',
        '  decide +kernel', '',
        'theorem hs : SaddleChecks Q p q v := (checkPrivateStage_sound Q p q v r receipt_checked).1',
        'theorem hp : PureChecks Q r := (checkPrivateStage_sound Q p q v r receipt_checked).2', '',
        '/-- `v` is the greatest private value over all real mixed controllers, attained by `p`. -/',
        'theorem value_greatest :',
        '    privateValue Q (controllerRow Q p q v hs) = (v : ℝ) ∧',
        '    IsGreatest (Set.range (privateValue Q)) (v : ℝ) :=',
        '  checked_isGreatest Q p q v hs', '',
        '/-- Actual stage-law saddle against every real nature row and every real controller. -/',
        'theorem private_saddle :',
        f'    (∀ η : Row (Fin {nt}), (v : ℝ) ≤',
        '      (stageLaw (controllerRow Q p q v hs) η).expect (fun a => (Q a.1 a.2 : ℝ))) ∧',
        f'    (∀ p\' : Row (Fin {nc}),',
        '      (stageLaw p\' (natureRow Q p q v hs)).expect (fun a => (Q a.1 a.2 : ℝ)) ≤ v) :=',
        '  checked_private_saddle Q p q v hs', '',
        '/-- Research\'s executable rational private-stage solver returns `v`. -/',
        'theorem solver_value : (solvePrivateStage Q).map (fun x => x none) = some v :=',
        '  checked_solver_value Q p q v hs', '',
        '/-- Pure controls under private timing are worth exactly `r`. -/',
        'theorem pure_controls :',
        '    (∀ c, privateValue Q (Row.pure c) ≤ (r : ℝ)) ∧ ∃ c, privateValue Q (Row.pure c) = (r : ℝ) :=',
        '  checked_pure_controls Q r hp', '',
        '/-- Revealed-control experiment: nature observing the realized control holds every',
        '    controller to `r`, and some pure control earns `r`. -/',
        'theorem revealed_control :',
        f'    (∃ f : Fin {nc} → Fin {nt}, ∀ p\' : Row (Fin {nc}),',
        '      (p\'.map (fun c => (f c, c))).expect (fun a => (Q a.1 a.2 : ℝ)) ≤ r) ∧',
        f'    ∃ c, ∀ f : Fin {nc} → Fin {nt},',
        '      (r : ℝ) ≤ ((Row.pure c).map (fun c => (f c, c))).expect (fun a => (Q a.1 a.2 : ℝ)) :=',
        '  checked_revealed_control Q r hp', '',
        f'end {MODULE}', '',
    ]
    names = ['receipt_checked', 'hs', 'hp', 'value_greatest', 'private_saddle', 'solver_value',
             'pure_controls', 'revealed_control']
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('PRIVATE_STAGE_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'controls': nc, 'nature': nt,
                  'timing': 'NATURE_SEES_MIXTURE_NOT_REALIZED_CONTROL',
                  'research_solver': 'solvePrivateStage value identified, solver not evaluated',
                  'not_claimed': ['multi_stage_private_games', 'committed_nature',
                                  'learning', 'empirical_identification']},
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
    (destination / 'ReifiedPrivateStage.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedPrivateStage.lean'),
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
