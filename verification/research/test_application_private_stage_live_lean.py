"""Pinned-Lean replay of checked one-stage private-control saddle receipts.

The payoff table, both mixtures, the value and the pure-control value become
literal rationals; Lean decides the two-sided saddle and pure-control checks,
then states that the value is the greatest private value over all real mixed
controllers, the actual stage-law saddle, that Research's `solvePrivateStage`
returns that value, and the pure-control and revealed-control values. A pass
proves bounded instance theorem elaboration with an audited axiom set, not
multi-stage private games, empirical identification, provenance or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.private_stage import propose_private_stage
from permansson_app.proof.private_stage_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedPrivateStage.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/private_stage.v1.json"


def _game(controls, nature, payoff):
    return {"format": "Permansson.App.PrivateStageRequest.v1",
            "labels": {"controls": controls, "nature": nature}, "payoff": payoff}


EXTRA = {
    "singleton": _game(["a"], ["x"], [["-5/3"]]),
    "one_parameter": _game(["a", "b", "c"], ["x"], [["1", "-2", "3"]]),
    "four_by_four": _game(["a", "b", "c", "d"], ["w", "x", "y", "z"],
                          [["1", "-2", "3", "0"], ["-1", "2", "-3", "1"],
                           ["2", "1", "0", "-1"], ["0", "0", "1", "2"]]),
}


def _replay(case, raw):
    code, meta = emit_source(raw, propose_private_stage(raw))
    case.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    case.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code


class PrivateStageLeanReplay(unittest.TestCase):
    _cache: str | None = None

    def _code(self) -> str:
        if PrivateStageLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            PrivateStageLeanReplay._cache = _replay(self, raw)
        return PrivateStageLeanReplay._cache

    def test_example_replays_with_audited_axioms(self):
        self.assertIn("theorem solver_value", self._code())

    def test_other_shapes_replay(self):
        for name, raw in EXTRA.items():
            with self.subTest(name=name):
                self.assertIn("theorem revealed_control", _replay(self, raw))

    def test_overstated_value_rejected(self):
        code = self._code()
        changed = change_line(code, "def v ", "(1 : ℚ)", "((11 : ℚ) / (10 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_understated_value_rejected(self):
        # The controller still guarantees 1/2, but nature's mixture holds calm only to 1.
        code = self._code()
        changed = change_line(code, "def v ", "(1 : ℚ)", "((1 : ℚ) / (2 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_pure_controller_mixture_rejected(self):
        code = self._code()
        changed = change_line(code, "def p ", "then ((1 : ℚ) / (2 : ℚ)) else (if c = (1 : Fin 3) then ((1 : ℚ) / (2 : ℚ))",
                              "then (1 : ℚ) else (if c = (1 : Fin 3) then (0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_non_holding_nature_mixture_rejected(self):
        code = self._code()
        changed = change_line(code, "def q ", "((3 : ℚ) / (5 : ℚ)) else ((2 : ℚ) / (5 : ℚ))",
                              "((1 : ℚ) / (2 : ℚ)) else ((1 : ℚ) / (2 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_overstated_pure_value_rejected(self):
        code = self._code()
        changed = change_line(code, "def r ", "((1 : ℚ) / (2 : ℚ))", "(1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_changed_payoff_rejected(self):
        # boost against dry from -1 to 0: nature's mixture then holds boost only to 8/5.
        code = self._code()
        changed = change_line(code, "def Q ", "then (-1 : ℚ)", "then (0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
