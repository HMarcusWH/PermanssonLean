"""Pinned-Lean replay of checked rectangular-vs-committed nature receipts.

Nature models are reflected inputs proved to change only P. Lean checks the
optimized rectangular value table, the fixed policy's rectangular table and
its table under every committed model, and transfers Research's chronological
saddle theorem to each. A pass proves bounded instance theorem elaboration
with an audited axiom set, not committed-game or private-stage optimality,
provenance, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.robust_nature import propose_nature
from permansson_app.proof.robust_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)
from test_application_perturbation_live_lean import _def_line

FILENAME = "ReifiedRobustNature.lean"
FIXTURE = APP / "tests/fixtures/robust_nature_two_models.v1.json"
HALF = "((1 : ℚ) / (2 : ℚ))"
QUARTER = "((1 : ℚ) / (4 : ℚ))"


def _replay(test: unittest.TestCase, **changes):
    raw = dict(json.loads(FIXTURE.read_text(encoding="utf-8")), **changes)
    receipt = propose_nature(raw)
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class RobustLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if RobustLeanReplay._cache is None:
            RobustLeanReplay._cache = _replay(self)
        return RobustLeanReplay._cache

    def test_fixture_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["comparison"]["rectangular_optimized"], ["4/9", "4/9"])
        self.assertIn("rectangular_le_committed", meta["theorem_names"])

    def test_one_step_variant_replays(self):
        _, _, receipt = _replay(self, horizon=1)
        self.assertEqual(receipt["horizon"], 1)

    def test_false_optimized_value_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def gameTable ",
                              "(if r = 2 then (if y = (0 : Fin 2) then ((4 : ℚ) / (9 : ℚ))",
                              f"(if r = 2 then (if y = (0 : Fin 2) then {HALF}")
        assert_semantic_rejection(self, code, changed, "game_checked", FILENAME)

    def test_rectangular_value_replaced_by_committed_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def fixedTable ", f"else {QUARTER}) else (0 : ℚ))))",
                              f"else {HALF}) else (0 : ℚ))))")
        assert_semantic_rejection(self, code, changed, "fixed_checked", FILENAME)

    def test_swapped_committed_models_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def natureMatrix ",
                              "then controlledMatrix nature_0 c else controlledMatrix nature_1 c",
                              "then controlledMatrix nature_1 c else controlledMatrix nature_0 c")
        assert_semantic_rejection(self, code, changed, "committed_0_checked", FILENAME)

    def test_nature_model_changing_strategic_alpha_rejected(self):
        code, _, _ = self._positive()
        changed = _def_line(code, "nature_0", "  alpha := ",
                            "(if x = (0 : Fin 2) then (if a = (0 : Fin 2) then (1 : ℚ) else (0 : ℚ))",
                            "(if x = (0 : Fin 2) then (if a = (0 : Fin 2) then (0 : ℚ) else (1 : ℚ))")
        assert_semantic_rejection(self, code, changed, "nature_0_held_fixed", FILENAME)


if __name__ == "__main__":
    unittest.main()
