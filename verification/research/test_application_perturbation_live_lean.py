"""Pinned-Lean replay of checked finite-horizon perturbation (TV budget) receipts.

Baseline and alternative are separately reflected alpha/P/U models. Lean
proves every row's actual one-step event TV is at most its half-L1 distance,
identifies both initial-law event probabilities with actual region-survival
probabilities and bounds their difference by `min 1 (TV(mu, nu) + T delta)`
via the core Proposition 5.4. A pass proves bounded instance theorem
elaboration with an audited axiom set, not a long-run, GR/PR or causal
statement, provenance, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.robustness import parse_perturbation, propose_perturbation
from permansson_app.proof.perturbation_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedPerturbation.lean"
FIXTURE = APP / "tests/fixtures/perturbation_transient_split.v1.json"
HALF = "((1 : ℚ) / (2 : ℚ))"


def _def_line(code: str, name: str, prefix: str, old: str, new: str) -> str:
    """Change `prefix` inside `def <name>` only (field names repeat per input)."""
    lines = code.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(f"def {name} "))
    index = next(i for i in range(start, len(lines)) if lines[i].startswith(prefix))
    if lines[index].count(old) != 1:
        raise AssertionError("mutation fragment must occur exactly once: " + old)
    lines[index] = lines[index].replace(old, new)
    return "\n".join(lines) + "\n"


class PerturbationLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if PerturbationLeanReplay._cache is None:
            raw = json.loads(FIXTURE.read_text(encoding="utf-8"))
            receipt = propose_perturbation(parse_perturbation(raw))
            code, meta = emit_source(raw, receipt)
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            PerturbationLeanReplay._cache = (code, meta, receipt)
        return PerturbationLeanReplay._cache

    def test_fixture_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["bound_at_horizon"], "3/4")
        self.assertEqual(receipt["observed_abs_difference"], "265/1728")
        self.assertIn("perturbation_bound", meta["theorem_names"])

    def test_understated_row_distance_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def rows ", "((1 : ℚ) / (6 : ℚ))", "((1 : ℚ) / (12 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_understated_budget_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def bound ", "((3 : ℚ) / (4 : ℚ))", HALF)
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_dropped_initial_law_term_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def tv0 ", "((1 : ℚ) / (4 : ℚ))", "(0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_event_probability_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def pb ", "((14 : ℚ) / (27 : ℚ))", HALF)
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_alternative_world_row_change_rejected(self):
        code, _, _ = self._positive()
        # Restoring the baseline P row in the alternative removes the
        # perturbation, so the checked row distance 1/6 becomes false.
        changed = _def_line(code, "alt", "  world := ",
                            f"(if xp = (0 : Fin 2) then {HALF} else {HALF})",
                            "(if xp = (0 : Fin 2) then ((1 : ℚ) / (3 : ℚ)) else ((2 : ℚ) / (3 : ℚ)))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
