"""Pinned-Lean replay of checked rational real-algebra witness receipts.

Rational matrices and vectors are cast into real matrices and the Euclidean
space; Lean decides the witness identities on the rationals and states
Research's specialized seam, shell Schur, singular-compatibility and Gram
conclusions for the cast objects. A pass proves bounded instance theorem
elaboration with an audited axiom set, not a feature identification with a
strategic source, provenance or release.
"""
from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.algebra import propose_algebra
from permansson_app.proof.algebra_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedAlgebra.lean"
R = "Permansson.App.RationalAlgebraRequest.v1"
CASES = {
    "seam": {"format": R, "profile": "seam", "H": [["2", "1", "1"], ["1", "0", "0"], ["1", "0", "0"]], "pivot": 1},
    "common": {"format": R, "profile": "seam", "H": [["3", "3"], ["3", "3"]], "pivot": 0},
    "schur": {"format": R, "profile": "schur", "H": [["2", "1"], ["1", "2"]], "B": [["1"], ["0"]],
              "C": [["1"]], "ell": "-1"},
    "compatible_negative": {"format": R, "profile": "singular", "H": [["1", "1"], ["1", "1"]],
                            "b": ["2", "2"], "c": "3"},
    "compatible_nonnegative": {"format": R, "profile": "singular", "H": [["1", "1"], ["1", "1"]],
                               "b": ["2", "2"], "c": "5"},
    "incompatible": {"format": R, "profile": "singular", "H": [["1", "1"], ["1", "1"]], "b": ["1", "0"], "c": "3"},
    "gram": {"format": R, "profile": "gram", "x": ["1", "0", "0"], "y": ["1", "1", "0"], "c": "2"},
}


def _q(n: int, d: int) -> str:
    return f"(({n} : ℚ) / ({d} : ℚ))"


class AlgebraLeanReplay(unittest.TestCase):
    _cache: dict[str, str] = {}

    def _code(self, name: str) -> str:
        if name not in AlgebraLeanReplay._cache:
            raw = CASES[name]
            code, meta = emit_source(raw, propose_algebra(raw))
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            AlgebraLeanReplay._cache[name] = code
        return AlgebraLeanReplay._cache[name]

    def test_every_profile_replays_with_audited_axioms(self):
        for name in CASES:
            with self.subTest(name=name):
                self._code(name)

    def test_asymmetric_seam_matrix_rejected(self):
        code = self._code("seam")
        changed = change_line(code, "def H ", "(2 : ℚ), (1 : ℚ), (1 : ℚ); (1 : ℚ)",
                              "(2 : ℚ), (1 : ℚ), (1 : ℚ); (2 : ℚ)")
        assert_semantic_rejection(self, code, changed, "seam_checked", FILENAME)

    def test_wrong_common_mode_rejected(self):
        code = self._code("common")
        changed = change_line(code, "def δ ", "(3 : ℚ)", "(2 : ℚ)")
        assert_semantic_rejection(self, code, changed, "diagonal_checked", FILENAME)

    def test_wrong_shell_complement_rejected(self):
        code = self._code("schur")
        changed = change_line(code, "def S ", _q(13, 8), _q(3, 2))
        assert_semantic_rejection(self, code, changed, "schur_checked", FILENAME)

    def test_negative_psd_pivot_rejected(self):
        code = self._code("schur")
        changed = change_line(code, "def d ", "![(2 : ℚ),", "![(-2 : ℚ),")
        assert_semantic_rejection(self, code, changed, "schur_checked", FILENAME)

    def test_nonnegative_shift_rejected(self):
        code = self._code("schur")
        changed = change_line(code, "def ell ", "(-1 : ℚ)", "(1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "schur_checked", FILENAME)

    def test_wrong_bordered_gap_rejected(self):
        code = self._code("compatible_negative")
        changed = change_line(code, "def g ", "(-1 : ℚ)", "(1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "compatible_checked", FILENAME)

    def test_false_preimage_rejected(self):
        code = self._code("compatible_negative")
        changed = change_line(code, "def x ", "![(2 : ℚ), (0 : ℚ)]", "![(1 : ℚ), (0 : ℚ)]")
        assert_semantic_rejection(self, code, changed, "compatible_checked", FILENAME)

    def test_kernel_witness_outside_kernel_rejected(self):
        code = self._code("incompatible")
        changed = change_line(code, "def z ", "(-1 : ℚ)", "(1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "incompatible_checked", FILENAME)

    def test_overstated_gram_threshold_rejected(self):
        code = self._code("gram")
        changed = change_line(code, "def τ ", "(2 : ℚ)", "(3 : ℚ)")
        assert_semantic_rejection(self, code, changed, "gram_checked", FILENAME)

    def test_wrong_gram_witness_rejected(self):
        code = self._code("gram")
        changed = change_line(code, "def w ", "![(0 : ℚ), (1 : ℚ), (0 : ℚ)]", "![(1 : ℚ), (1 : ℚ), (0 : ℚ)]")
        assert_semantic_rejection(self, code, changed, "gram_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
