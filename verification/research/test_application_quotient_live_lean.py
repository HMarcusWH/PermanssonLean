"""Pinned-Lean replay of checked exact typed quotients bound to alpha/P/U.

Every profile (baseline and each declared intervention) is a reflected input
whose induced matrix is checked to lump strongly onto its reported coarse
matrix along the reflected projection; interventions hold feasibility, P and
the undeclared generator fixed. Fine and coarse survival values are actual
path-law probabilities and agree. A pass proves bounded instance theorem
elaboration with an audited axiom set, not a coarse alpha/P/U decomposition,
GR/PR status, provenance, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.quotients import propose_quotient
from permansson_app.proof.quotient_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)
from test_application_perturbation_live_lean import _def_line

FILENAME = "ReifiedQuotient.lean"
FIXTURE = APP / "tests/fixtures/quotient_geometric_exit.v1.json"
PACKAGED = APP / "src/permansson_app/data/examples/quotient.v1.json"
TWO_THIRDS_ROW = "(if d = (0 : Fin 2) then ((2 : ℚ) / (3 : ℚ)) else ((1 : ℚ) / (3 : ℚ)))"


def _replay(test: unittest.TestCase, path: Path, **changes):
    raw = dict(json.loads(path.read_text(encoding="utf-8")), **changes)
    receipt = propose_quotient(raw)
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class QuotientLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if QuotientLeanReplay._cache is None:
            QuotientLeanReplay._cache = _replay(self, FIXTURE)
        return QuotientLeanReplay._cache

    def test_geometric_fixture_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["profiles"][0]["fine_values"], ["8/27", "8/27"])
        self.assertIn("transport_1", meta["theorem_names"])

    def test_packaged_exit_variant_replays(self):
        _, meta, receipt = _replay(self, PACKAGED, value_type="exit_by_horizon", horizon=3)
        self.assertEqual(meta["scope"]["profiles"], ["baseline", "alpha_all", "update_state"])
        self.assertEqual(receipt["profiles"][1]["fine_values"], ["1", "1"])

    def test_non_lumping_coarse_matrix_rejected(self):
        code, _, _ = self._positive()
        # Still stochastic, but not the aggregate of the fine rows.
        changed = _def_line(code, "Q_0", "  entry := ", TWO_THIRDS_ROW,
                            "(if d = (0 : Fin 2) then ((1 : ℚ) / (2 : ℚ)) else ((1 : ℚ) / (2 : ℚ)))")
        assert_semantic_rejection(self, code, changed, "profile_0_checked", FILENAME)

    def test_region_not_union_of_fibers_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def region ", "({0, 2} : Finset (Fin 4))", "({0} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "profile_0_checked", FILENAME)

    def test_false_fine_value_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def fine_0 ", "(if y = (0 : Fin 4) then ((8 : ℚ) / (27 : ℚ))",
                              "(if y = (0 : Fin 4) then ((1 : ℚ) / (3 : ℚ))")
        assert_semantic_rejection(self, code, changed, "profile_0_checked", FILENAME)

    def test_projection_merging_fibers_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def proj ", "(if y = (2 : Fin 4) then (0 : Fin 2)",
                              "(if y = (2 : Fin 4) then (1 : Fin 2)")
        assert_semantic_rejection(self, code, changed, "profile_0_checked", FILENAME)

    def test_intervention_changing_world_kernel_rejected(self):
        code, _, _ = self._positive()
        changed = _def_line(
            code, "member_0", "  world := ",
            "(if s = (0 : Fin 2) then (if x = (0 : Fin 2) then (if xp = (0 : Fin 2) then "
            "((2 : ℚ) / (3 : ℚ)) else ((1 : ℚ) / (3 : ℚ)))",
            "(if s = (0 : Fin 2) then (if x = (0 : Fin 2) then (if xp = (0 : Fin 2) then "
            "((1 : ℚ) / (3 : ℚ)) else ((2 : ℚ) / (3 : ℚ)))")
        assert_semantic_rejection(self, code, changed, "member_0_held_fixed", FILENAME)


if __name__ == "__main__":
    unittest.main()
