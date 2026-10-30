"""Pinned-Lean replay of checked first-exit routing receipts bound to alpha/P/U.

The chain is the induced matrix of the reflected source model. Survival,
cumulative first exit per destination, eventual first exit per destination
and never-exit mass are proved to be probabilities of events of the actual
infinite path law; eventual routing goes through a kernel-checked Dirichlet
certificate of the exit-stopped chain. A pass proves bounded instance
theorem elaboration with an audited axiom set, not a restart law, switch
retention, GR/PR status, provenance, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.exit import compute_exit, parse_region
from permansson_app.finite_world import parse_finite_world
from permansson_app.proof.exit_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedExit.lean"
EXAMPLES = APP / "src/permansson_app/data/examples"
FIXTURES = APP / "tests/fixtures"
SPLIT = FIXTURES / "occupation_transient_split.v1.json"
CASES = {
    "packaged": (EXAMPLES / "finite_world.v1.model.json", EXAMPLES / "finite_region.v1.json"),
    "origin": (SPLIT, FIXTURES / "occupation_transient_split.region_origin.v1.json"),
    "closed": (SPLIT, FIXTURES / "occupation_transient_split.region_closed_class.v1.json"),
}
HALF = "((1 : ℚ) / (2 : ℚ))"


class ExitLeanReplay(unittest.TestCase):
    _cache: dict[str, tuple[str, dict, dict]] = {}

    def _positive(self, name: str):
        if name not in ExitLeanReplay._cache:
            model_path, region_path = CASES[name]
            raw = json.loads(model_path.read_text(encoding="utf-8"))
            region = json.loads(region_path.read_text(encoding="utf-8"))
            model = parse_finite_world(raw)
            receipt = compute_exit(model, parse_region(region, model))
            code, meta = emit_source(raw, region, receipt)
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            ExitLeanReplay._cache[name] = (code, meta, receipt)
        return ExitLeanReplay._cache[name]

    def test_packaged_single_destination_replays(self):
        _, meta, receipt = self._positive("packaged")
        self.assertEqual(receipt["rows"][0]["eventual_exit_by_destination"], ["0", "0", "1"])
        self.assertIn("eventual_exit_0_3", meta["theorem_names"])

    def test_two_destination_routing_replays(self):
        _, meta, receipt = self._positive("origin")
        self.assertEqual(receipt["rows"][0]["eventual_exit_by_destination"], ["1/2", "0", "1/2"])
        self.assertIn("exit_within_horizon_0_1", meta["theorem_names"])

    def test_inside_closed_class_never_exit_replays(self):
        _, meta, receipt = self._positive("closed")
        self.assertEqual([row["never_exit"] for row in receipt["rows"]], ["1/2", "1", "1"])
        self.assertEqual(meta["scope"]["stopped_chain_classes"], [[1, 2], [3]])

    def test_renormalized_routing_rejected(self):
        code, _, _ = self._positive("closed")
        # Conditioning on exit would report 1 instead of the subprobability 1/2.
        changed = change_line(code, "def eventual ",
                              f"(if d = (2 : Fin 4) then (0 : ℚ) else {HALF}))) else (if x = (1 : Fin 4)",
                              "(if d = (2 : Fin 4) then (0 : ℚ) else (1 : ℚ)))) else (if x = (1 : Fin 4)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_dropped_never_exit_mass_rejected(self):
        code, _, _ = self._positive("closed")
        changed = change_line(code, "def never ", f"(if x = (0 : Fin 4) then {HALF}",
                              "(if x = (0 : Fin 4) then (0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_survival_entry_rejected(self):
        code, _, _ = self._positive("closed")
        changed = change_line(code, "def survival ", "then ((2 : ℚ) / (3 : ℚ))", f"then {HALF}")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_wrong_stopped_class_rejected(self):
        code, _, _ = self._positive("closed")
        changed = change_line(code, "def class_0 ", "({1, 2} : Finset (Fin 4))", "({1} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_wrong_exit_index_rejected(self):
        code, _, _ = self._positive("packaged")
        changed = change_line(
            code, "def eventual ",
            "(if d = (1 : Fin 4) then (0 : ℚ) else (if d = (2 : Fin 4) then (0 : ℚ) else (1 : ℚ)))",
            "(if d = (1 : Fin 4) then (1 : ℚ) else (if d = (2 : Fin 4) then (0 : ℚ) else (0 : ℚ)))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_step_entry_rejected(self):
        code, _, _ = self._positive("origin")
        changed = change_line(
            code, "def steps ",
            "(if s = 0 then (if x = (0 : Fin 4) then (if d = (0 : Fin 4) then (0 : ℚ) else "
            "(if d = (1 : Fin 4) then ((1 : ℚ) / (3 : ℚ))",
            "(if s = 0 then (if x = (0 : Fin 4) then (if d = (0 : Fin 4) then (0 : ℚ) else "
            "(if d = (1 : Fin 4) then ((2 : ℚ) / (3 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
