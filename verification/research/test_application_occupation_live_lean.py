"""Pinned-Lean replay of checked finite occupation receipts bound to alpha/P/U.

The chain is the induced matrix of the reflected source model. The listed
classes are proved to be exactly the computed bottom classes, every weight the
actual probability of eventually entering that class, every class law the
actual almost-sure occupation limit when that class is selected, the whole
random-limit law the receipt's Dirac mixture, and every mean law only its
barycenter. A pass proves bounded instance theorem elaboration with an audited
axiom set, not GR/PR recovery, provenance, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.occupation import compute_occupation
from permansson_app.finite_world import parse_finite_world
from permansson_app.proof.occupation_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedOccupation.lean"
SPLIT = APP / "tests/fixtures/occupation_transient_split.v1.json"
EXAMPLE = APP / "src/permansson_app/data/examples/finite_world.v1.model.json"
HALF = "((1 : ℚ) / (2 : ℚ))"


def _replay(test: unittest.TestCase, path: Path):
    raw = json.loads(path.read_text(encoding="utf-8"))
    receipt = compute_occupation(parse_finite_world(raw))
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class OccupationLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if OccupationLeanReplay._cache is None:
            OccupationLeanReplay._cache = _replay(self, SPLIT)
        return OccupationLeanReplay._cache

    def test_transient_split_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["bottom_classes"], [[1, 2], [3]])
        self.assertEqual(receipt["absorption_weights"][0], ["1/2", "1/2"])
        for name in ("absorption_1_0", "random_limit_on_class_0", "random_limit_law",
                     "occupation_limit", "mean_mixture"):
            self.assertIn(name, meta["theorem_names"])

    def test_packaged_model_replays(self):
        _, meta, receipt = _replay(self, EXAMPLE)
        self.assertEqual(meta["scope"]["bottom_classes"], len(receipt["bottom_classes"]))

    def test_false_absorption_weight_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "  weight := ",
                              f"(if x = (0 : Fin 4) then {HALF} else (if x = (1 : Fin 4) then (1 : ℚ)",
                              "(if x = (0 : Fin 4) then ((1 : ℚ) / (3 : ℚ)) else (if x = (1 : Fin 4) then (1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_missing_bottom_class_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "  classes := ", "{class_0, class_1}", "{class_0}")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_wrong_class_membership_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def class_1 ", "({3} : Finset (Fin 4))", "({2, 3} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_noninvariant_class_law_rejected(self):
        code, _, _ = self._positive()
        # Still a positive probability vector on {1, 2}, but the class is a
        # 2-cycle, so only the uniform law is invariant.
        changed = change_line(code, "def laws ",
                              f"then {HALF} else (if y = (2 : Fin 4) then {HALF}",
                              "then ((1 : ℚ) / (3 : ℚ)) else (if y = (2 : Fin 4) then ((2 : ℚ) / (3 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_mean_law_confused_with_realized_class_law_rejected(self):
        code, _, _ = self._positive()
        # From the transient state the realized limit law is class 0's or
        # class 1's law at random; reporting class 0's law as the mean fails.
        quarter = "((1 : ℚ) / (4 : ℚ))"
        changed = change_line(code, "def mean ",
                              f"then {quarter} else (if y = (2 : Fin 4) then {quarter} else {HALF})",
                              f"then {HALF} else (if y = (2 : Fin 4) then {HALF} else (0 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_receipt_for_different_source_rejected(self):
        code, _, _ = self._positive()
        # A normalized but different U row: the transient split becomes 1/4 : 3/4.
        changed = change_line(code, "  update := ", f"then {HALF} else {HALF}",
                              "then ((1 : ℚ) / (4 : ℚ)) else ((3 : ℚ) / (4 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
