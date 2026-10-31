"""Pinned-Lean replay of checked frozen intervention menus bound to alpha/P/U.

Each listed member is the induced matrix of its own reflected input; held
fixed P/feasibility and the undeclared generator are proved against the
baseline, values are canonical path-law probabilities and the tie set is
exactly the listed optima. A pass proves bounded instance theorem elaboration
with an audited axiom set, not optimality outside the menu, provenance,
identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.menu import propose_menu
from permansson_app.proof.menu_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedMenu.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/finite_menu.v1.json"


def _member_line(code: str, member: int, prefix: str, old: str, new: str) -> str:
    """Change `prefix` inside `def member_<member>` only (names repeat per input)."""
    lines = code.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(f"def member_{member} "))
    index = next(i for i in range(start, len(lines)) if lines[i].startswith(prefix))
    if lines[index].count(old) < 1:
        raise AssertionError("mutation fragment absent: " + old)
    lines[index] = lines[index].replace(old, new, 1)
    return "\n".join(lines) + "\n"


class MenuLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if MenuLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            receipt = propose_menu(raw)
            code, meta = emit_source(raw, receipt)
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            MenuLeanReplay._cache = (code, meta, receipt)
        return MenuLeanReplay._cache

    def test_packaged_menu_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(meta["scope"]["members"], 2)
        self.assertEqual(receipt["attaining_ids"], ["untreated"])
        self.assertIn("member_1_update_held_fixed", meta["theorem_names"])

    def test_exit_objective_with_max_direction_replays(self):
        raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
        raw = dict(raw, value_type="exit_by_horizon", direction="max")
        receipt = propose_menu(raw)
        code, meta = emit_source(raw, receipt)
        exitcode, log = compile_source(code, FILENAME)
        self.assertEqual(exitcode, 0, log[-9000:])
        audited_axioms(log, meta["theorem_qualified_names"])
        self.assertEqual(receipt["attaining_ids"], ["untreated"])

    def test_false_member_value_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def values ", "else (1 : ℚ))", "else ((9 : ℚ) / (10 : ℚ)))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_overclaimed_tie_set_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def tied ", "({0} : Finset (Fin 2))", "({0, 1} : Finset (Fin 2))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_non_optimal_member_selected_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def tied ", "({0} : Finset (Fin 2))", "({1} : Finset (Fin 2))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_reversed_direction_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def maximize ", ":= false", ":= true")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_member_that_changes_held_fixed_generator_rejected(self):
        code, _, _ = self._positive()
        # `treated` declares an alpha intervention. Swapping its first U row
        # (s0,x0,a0,xp0) from [1,0] to [0,1] keeps the member a valid
        # normalized input, so only the U-held-fixed obligation may fail
        # (values that depend on the changed row may fail downstream).
        changed = _member_line(code, 1, "  update := ",
                               "then (1 : ℚ) else (0 : ℚ))", "then (0 : ℚ) else (1 : ℚ))")
        assert_semantic_rejection(self, code, changed, "member_1_update_held_fixed", FILENAME)

if __name__ == "__main__":
    unittest.main()
