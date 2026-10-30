"""Checked rational algebra witness receipt -> source-bound Lean *candidate*.

Only receipts that pass the independent algebra checker are emitted, and only
when their premises hold (a seam receipt whose seam equations fail is
refused). Matrices and vectors are emitted as literal rationals; Lean decides
the witness identities on the rationals and states Research's specialized
conclusions for the cast real objects. Any strategic reading still needs the
separately supplied feature or operator identification. Emission is never
compiler replay, independent certification, empirical identification or
release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.algebra import check_algebra
from ..strict_json import strict_read
from .control_emit import _new_dir
from .finite_emit import rational_expr

FORMAT = 'Permansson.App.AlgebraLeanSourceCandidate.v1'
MODULE = 'PermanssonResearch.ApplicationBridge.ReifiedAlgebra'
MAX_SOURCE_BYTES = 256 * 1024


def _q(text):
    return rational_expr(exact_ratio(text))


def _mat(rows):
    return '!![' + '; '.join(', '.join(_q(v) for v in row) for row in rows) + ']'


def _vec(row):
    return '![' + ', '.join(_q(v) for v in row) + ']'


def emit_source(raw: dict, receipt: dict) -> tuple[str, dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('ALGEBRA_REIFY_INPUT', 'raw algebra request and receipt required')
    checked = check_algebra(raw, receipt)
    profile = receipt['profile']
    head = [
        'import PermanssonResearch.ApplicationBridge.RationalAlgebraReceipt',
        'import Mathlib.Tactic', '',
        f'/-! Reified exact rational algebra witness ({profile}); application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Feature or operator identification with a strategic source is NOT established.',
        '    A compiler result and independent review are NOT asserted. -/', '',
        f'namespace {MODULE}',
        'open Matrix',
        'open scoped InnerProductSpace',
        'open PermanssonResearch.Specialized',
        'open PermanssonResearch.ApplicationBridge.RationalAlgebraReceipt',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0', '',
    ]
    body = []
    names = []
    if profile == 'seam':
        if receipt['status'] == 'SEAM_PREMISES_FAIL':
            raise AppError('ALGEBRA_REIFY_SCOPE', 'seam premises fail; nothing to bind')
        n = len(receipt['H'])
        p = receipt['pivot']
        body += [f'def H : Matrix (Fin {n}) (Fin {n}) ℚ := {_mat(receipt["H"])}',
                 f'def p : Fin {n} := {p}', '',
                 'theorem seam_checked : checkSeam H p = true := by',
                 '  decide +kernel', '',
                 '/-- Vanishing seam equations bound the real rank by two. -/',
                 'theorem seam_rank : (rm H).rank ≤ 2 :=',
                 '  checked_seam_rank H p seam_checked', '']
        names += ['seam_checked', 'seam_rank']
        if receipt['common_mode'] is not None:
            delta = _q(receipt['common_mode'])
            body += [f'def δ : ℚ := {delta}', '',
                     'theorem diagonal_checked : decide (Matrix.diag H = fun _ => δ) = true := by',
                     '  decide +kernel', '',
                     '/-- Common mode: constant entries, rank at most one, quadratic δ (Σ v)². -/',
                     'theorem common_mode :',
                     '    (∀ i j, rm H i j = ((δ : ℚ) : ℝ)) ∧ (rm H).rank ≤ 1 ∧',
                     f'      ∀ v : Fin {n} → ℝ, quadratic (rm H) v = ((δ : ℚ) : ℝ) * (∑ i, v i) ^ 2 :=',
                     '  checked_common_mode H p δ seam_checked diagonal_checked', '']
            names += ['diagonal_checked', 'common_mode']
    elif profile == 'schur':
        n, m = len(receipt['H']), len(receipt['C'])
        w = receipt['psd_witness']
        body += [f'def H : Matrix (Fin {n}) (Fin {n}) ℚ := {_mat(receipt["H"])}',
                 f'def L : Matrix (Fin {n}) (Fin {n}) ℚ := {_mat(w["L"])}',
                 f'def d : Fin {n} → ℚ := {_vec(w["d"])}',
                 f'def B : Matrix (Fin {n}) (Fin {m}) ℚ := {_mat(receipt["B"])}',
                 f'def X : Matrix (Fin {n}) (Fin {m}) ℚ := {_mat(receipt["X"])}',
                 f'def C : Matrix (Fin {m}) (Fin {m}) ℚ := {_mat(receipt["C"])}',
                 f'def S : Matrix (Fin {m}) (Fin {m}) ℚ := {_mat(receipt["shell_complement"])}',
                 f'def ell : ℚ := {_q(receipt["ell"])}', '',
                 'theorem schur_checked : checkSchur H L d B X C S ell = true := by',
                 '  decide +kernel', '',
                 '/-- H is positive semidefinite, the shell complement is S, the block determinant',
                 '    factorizes through it and the shell equations reduce to S w = 0. -/',
                 'theorem shell_complement :',
                 '    (rm H).PosSemidef ∧ shellComplement (rm H) (rm B) (rm C) ((ell : ℚ) : ℝ) = rm S ∧',
                 '    (Matrix.fromBlocks (negativeShift (rm H) ((ell : ℚ) : ℝ)) (rm B) (rm B)ᵀ',
                 '        (negativeShift (rm C) ((ell : ℚ) : ℝ))).det =',
                 '      (negativeShift (rm H) ((ell : ℚ) : ℝ)).det * (rm S).det ∧',
                 f'    ∀ (v : Fin {n} → ℝ) (w : Fin {m} → ℝ),',
                 '      ((negativeShift (rm H) ((ell : ℚ) : ℝ)) *ᵥ v + rm B *ᵥ w = 0 ∧',
                 '        (rm B)ᵀ *ᵥ v + (negativeShift (rm C) ((ell : ℚ) : ℝ)) *ᵥ w = 0) ↔',
                 '      (v = -((negativeShift (rm H) ((ell : ℚ) : ℝ))⁻¹ *ᵥ (rm B *ᵥ w)) ∧ rm S *ᵥ w = 0) :=',
                 '  checked_schur H L d B X C S ell schur_checked', '']
        names += ['schur_checked', 'shell_complement']
    elif profile == 'singular':
        n = len(receipt['H'])
        w = receipt['psd_witness']
        body += [f'def H : Matrix (Fin {n}) (Fin {n}) ℚ := {_mat(receipt["H"])}',
                 f'def L : Matrix (Fin {n}) (Fin {n}) ℚ := {_mat(w["L"])}',
                 f'def d : Fin {n} → ℚ := {_vec(w["d"])}',
                 f'def b : Fin {n} → ℚ := {_vec(receipt["b"])}', '']
        if receipt['compatible']:
            g = _q(receipt['gap'])
            body += [f'def x : Fin {n} → ℚ := {_vec(receipt["preimage"])}',
                     f'def c : ℚ := {_q(receipt["c"])}',
                     f'def g : ℚ := {g}', '',
                     'theorem compatible_checked : checkCompatible H L d b x c g = true := by',
                     '  decide +kernel', '',
                     '/-- Nonnegativity of the bordered form is exactly 0 ≤ g, and every',
                     '    preimage of b has response c − g. -/',
                     'theorem bordered_form :',
                     '    ((∀ v t, 0 ≤ singularBlockForm (op H) (ev b) ((c : ℚ) : ℝ) v t) ↔ 0 ≤ ((g : ℚ) : ℝ)) ∧',
                     '    ∀ y, op H y = ev b → ⟪ev b, y⟫_ℝ = ((c : ℚ) : ℝ) - ((g : ℚ) : ℝ) :=',
                     '  checked_compatible H L d b x c g compatible_checked', '']
            names += ['compatible_checked', 'bordered_form']
            if exact_ratio(receipt['gap']) >= 0:
                body += ['theorem bordered_sign : ∀ v t, 0 ≤ singularBlockForm (op H) (ev b) ((c : ℚ) : ℝ) v t :=',
                         '  bordered_form.1.mpr (by norm_num [g])', '']
            else:
                body += ['theorem bordered_sign : ∃ v t, singularBlockForm (op H) (ev b) ((c : ℚ) : ℝ) v t < 0 := by',
                         '  by_contra hall',
                         '  have hnn : ∀ v t, 0 ≤ singularBlockForm (op H) (ev b) ((c : ℚ) : ℝ) v t :=',
                         '    fun v t => not_lt.mp (fun hlt => hall ⟨v, t, hlt⟩)',
                         '  have := bordered_form.1.mp hnn',
                         '  norm_num [g] at this', '']
            names.append('bordered_sign')
        else:
            body += [f'def z : Fin {n} → ℚ := {_vec(receipt["kernel_witness"])}', '',
                     'theorem incompatible_checked : checkIncompatible H L d b z = true := by',
                     '  decide +kernel', '',
                     '/-- b has no preimage and the bordered form is negative somewhere, for every c. -/',
                     'theorem no_preimage_negative_direction (c : ℝ) :',
                     '    (¬ ∃ x, op H x = ev b) ∧ ∃ v, singularBlockForm (op H) (ev b) c v 1 < 0 :=',
                     '  checked_incompatible H L d b z incompatible_checked c', '']
            names += ['incompatible_checked', 'no_preimage_negative_direction']
    else:
        if receipt['status'] != 'POSITIVE_GAP_SEPARATION':
            raise AppError('ALGEBRA_REIFY_SCOPE', 'zero Gram gap; nothing to bind')
        n = len(receipt['x'])
        body += [f'def x : Fin {n} → ℚ := {_vec(receipt["x"])}',
                 f'def y : Fin {n} → ℚ := {_vec(receipt["y"])}',
                 f'def w : Fin {n} → ℚ := {_vec(receipt["witness"])}',
                 f'def c : ℚ := {_q(receipt["c"])}',
                 f'def gap : ℚ := {_q(receipt["gap"])}',
                 f'def τ : ℚ := {_q(receipt["threshold"])}', '',
                 'theorem gram_checked : checkGram x y w c gap τ = true := by',
                 '  decide +kernel', '',
                 '/-- The Gram witness is w; the signed form on it is −c·gap², negative under',
                 '    every operator perturbation of norm below τ. -/',
                 'theorem gram_separation :',
                 '    gramWitness (ev x) (ev y) = ev w ∧ gramGap (ev x) (ev y) = ((gap : ℚ) : ℝ) ∧',
                 '    ((c : ℚ) : ℝ) * (⟪ev x, ev w⟫_ℝ ^ 2 - ⟪ev y, ev w⟫_ℝ ^ 2) =',
                 '      -((c : ℚ) : ℝ) * ((gap : ℚ) : ℝ) ^ 2 ∧',
                 f'    ∀ T : EuclideanSpace ℝ (Fin {n}) →L[ℝ] EuclideanSpace ℝ (Fin {n}), ‖T‖ < ((τ : ℚ) : ℝ) →',
                 '      ((c : ℚ) : ℝ) * (⟪ev x, ev w⟫_ℝ ^ 2 - ⟪ev y, ev w⟫_ℝ ^ 2) + ⟪ev w, T (ev w)⟫_ℝ < 0 :=',
                 '  checked_gram x y w c gap τ gram_checked', '']
        names += ['gram_checked', 'gram_separation']
    lines = head + body + [f'end {MODULE}', ''] + [f'#print axioms {MODULE}.{n}' for n in names] + ['']
    text = '\n'.join(lines)
    if len(text.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('ALGEBRA_REIFY_SCOPE', 'generated Lean source exceeds byte limit')
    out = {
        'format': FORMAT,
        'problem_semantic_identity': receipt['request_identity'],
        'receipt_sha256': checked['receipt_sha256'],
        'theorem_names': names,
        'theorem_qualified_names': [MODULE + '.' + n for n in names],
        'theorem_module': MODULE,
        'lean_source_sha256': sha256(text.encode('utf-8')).hexdigest(),
        'scope': {'profile': profile, 'witness_status': receipt['status'],
                  'feature_identification': 'NOT_ESTABLISHED_EXPLICIT_PREMISE',
                  'not_claimed': ['strategic_conclusion_without_feature_identification',
                                  'infinite_dimensional_or_complex_objects']},
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
    (destination / 'ReifiedAlgebra.lean').write_bytes(lean.encode('utf-8'))
    (destination / 'source_candidate.json').write_bytes(canonical_bytes(metadata) + b'\n')
    return {'format': FORMAT, 'source_file': str(destination / 'ReifiedAlgebra.lean'),
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
