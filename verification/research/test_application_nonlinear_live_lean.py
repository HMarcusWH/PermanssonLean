"""Pinned-Lean replay of checked nonlinear classwise occupation objectives.

The policies are every declared feasible deterministic stationary action map
of the reflected alpha/P/U model (`boundControlSystem`, P and U fixed). Lean
evaluates the exact C10/C11 class arithmetic for all of them; listed values
are proved to be expected Boolean scores of the actual random occupation
limit and the optimum maximal over the whole class. A pass proves bounded
instance theorem elaboration with an audited axiom set, not optimality over
randomized or history-dependent policies, provenance, identification or
release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.nonlinear import propose_nonlinear
from permansson_app.proof.nonlinear_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedNonlinear.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/nonlinear.v1.json"
TWO_COPIES = APP / "tests/fixtures/nonlinear_two_copies.v1.json"
FN = "Fin (1 * 2) → Fin 2"


def _replay(test: unittest.TestCase, path: Path):
    raw = json.loads(path.read_text(encoding="utf-8"))
    receipt = propose_nonlinear(raw)
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class NonlinearLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if NonlinearLeanReplay._cache is None:
            NonlinearLeanReplay._cache = _replay(self, EXAMPLE)
        return NonlinearLeanReplay._cache

    def test_packaged_request_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["attaining_policy_indices"], [3])
        self.assertIn("stationary_optimum", meta["theorem_names"])

    def test_sixteen_policy_two_copy_request_replays(self):
        _, meta, receipt = _replay(self, TWO_COPIES)
        self.assertEqual(meta["scope"]["policies"], 16)
        self.assertEqual(receipt["optimum_value"], "5/6")

    def test_functional_of_expectation_substitution_rejected(self):
        code, _, _ = self._positive()
        # stay/stay mixes two absorbing classes: E[F] = 1/2, but F(E[p]) = 5/6.
        changed = change_line(code, "def values ",
                              f"(if f = (![0, 0] : {FN}) then ((1 : ℚ) / (2 : ℚ))",
                              f"(if f = (![0, 0] : {FN}) then ((5 : ℚ) / (6 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_overclaimed_tie_set_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def tied ", f"{{(![1, 1] : {FN})}}",
                              f"{{(![1, 1] : {FN}), (![1, 0] : {FN})}}")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_optimum_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def optimum ", "((5 : ℚ) / (6 : ℚ))", "(1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_changed_descriptor_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def h ", "({1} : Finset (Fin 2))", "({0} : Finset (Fin 2))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_receipt_for_different_world_kernel_rejected(self):
        code, _, _ = self._positive()
        # `flip` at `left` keeps a normalized row but stops switching.
        changed = change_line(
            code, "  world := ",
            "(if xp = (0 : Fin 2) then (0 : ℚ) else (1 : ℚ))) else (if a = (0 : Fin 2)",
            "(if xp = (0 : Fin 2) then (1 : ℚ) else (0 : ℚ))) else (if a = (0 : Fin 2)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
