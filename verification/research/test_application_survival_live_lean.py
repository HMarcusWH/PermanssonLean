"""Pinned-Lean replay of checked killed-kernel survival comparisons.

Both complete survival tables are checked against the induced matrices of
their own reflected inputs; the treated model is proved to hold P,
feasibility and the undeclared generator fixed; horizon effects are stated as
differences of canonical-law survival probabilities. A pass proves bounded
instance theorem elaboration with an audited axiom set, not invariance,
GR/PR status, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.finite_survival import propose_finite_survival
from permansson_app.proof.survival_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)
from test_application_menu_live_lean import _member_line

FILENAME = "ReifiedSurvival.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/finite_survival.v1.json"


class SurvivalLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if SurvivalLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            receipt = propose_finite_survival(raw)
            code, meta = emit_source(raw, receipt)
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            SurvivalLeanReplay._cache = (code, meta, receipt)
        return SurvivalLeanReplay._cache

    def test_packaged_comparison_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(meta["scope"]["comparison_states"], [0, 2])
        self.assertEqual(receipt["finite_effect_signs"], ["negative", "negative"])
        self.assertIn("horizon_effect_0", meta["theorem_names"])

    def test_false_table_entry_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def baselineTable ", "(if y = (0 : Fin 4) then ((1 : ℚ) / (4 : ℚ))",
                              "(if y = (0 : Fin 4) then ((1 : ℚ) / (3 : ℚ))")
        assert_semantic_rejection(self, code, changed, "baseline_table_checked", FILENAME)

    def test_false_region_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def region ", "({0, 2} : Finset (Fin 4))", "({0} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "baseline_table_checked", FILENAME)

    def test_treated_model_changing_undeclared_generator_rejected(self):
        code, _, _ = self._positive()
        # `treated` declares an alpha intervention; a normalized but different
        # U row must break the U-held-fixed proof.
        lines = code.replace("def treated ", "def member_1 ", 1)
        changed = _member_line(lines, 1, "  update := ",
                               "then (1 : ℚ) else (0 : ℚ))", "then (0 : ℚ) else (1 : ℚ))")
        changed = changed.replace("def member_1 ", "def treated ", 1)
        assert_semantic_rejection(self, code, changed, "treated_update_held_fixed", FILENAME)


if __name__ == "__main__":
    unittest.main()
