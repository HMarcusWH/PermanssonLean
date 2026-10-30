"""Pinned-Lean replay of checked retryable residence values bound to alpha/P/U.

The reflected control system is `boundControlSystem` over the exact source
input; each per-start value is evaluated by Lean's layer-wise optimal
residence table and inherits the behavioral-history optimality theorem. A
pass proves bounded instance theorem elaboration with an audited axiom set,
not external provenance, identification or release.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.residence import solve_residence
from permansson_app.proof.control_emit import _fin_case
from permansson_app.proof.finite_emit import rational_expr
from permansson_app.proof.residence_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedResidence.lean"


def residence_problem(dwell: int = 1, deadline: int = 2) -> dict:
    """2x2 joint space; `push` randomizes the strategic state and favours the
    target world, `wait` holds it; `push` is infeasible at (s1, x0)."""
    S, X = ["s0", "s1"], ["x0", "x1"]
    feasible = {(s, x): ["wait", "push"] for s in S for x in X}
    feasible["s1", "x0"] = ["wait"]
    alpha = {(s, x): {"wait": "1/2", "push": "1/2"} for s in S for x in X}
    alpha["s1", "x0"] = {"wait": "1", "push": "0"}
    P = {}
    for s in S:
        for x in X:
            P[s, x, "wait"] = {"x0": "1", "x1": "0"} if x == "x0" else {"x0": "1/2", "x1": "1/2"}
            P[s, x, "push"] = {"x0": "1/3", "x1": "2/3"}

    def U(s, a):
        return {"s0": "1/2", "s1": "1/2"} if a == "push" else {s: "1", ("s1" if s == "s0" else "s0"): "0"}

    model = {
        "format": "Permansson.App.FiniteStrategicWorld.v1",
        "states": {"strategic": S, "world": X, "actions": ["wait", "push"]},
        "feasible": [{"s": s, "x": x, "actions": feasible[s, x]} for s in S for x in X],
        "alpha": [{"s": s, "x": x, "weights": alpha[s, x]} for s in S for x in X],
        "P": [{"s": s, "x": x, "a": a, "weights": P[s, x, a]}
              for s in S for x in X for a in feasible[s, x]],
        "U": [{"s": s, "x": x, "a": a, "xp": xp, "weights": U(s, a)}
              for s in S for x in X for a in feasible[s, x] for xp in X],
    }
    return {"format": "Permansson.App.FiniteResidenceRequest.v1", "model": model,
            "target": [{"strategic": "s0", "world": "x1"}, {"strategic": "s1", "world": "x1"}],
            "danger": [], "mode": "retryable", "deadline": deadline,
            "deadline_semantics": "entry_by", "dwell_transitions": dwell,
            "initial_law": [{"state": [s, x], "mass": "1/4"} for s in S for x in X]}


class ResidenceLeanReplay(unittest.TestCase):
    _cache: dict = {}

    def _positive(self, dwell: int = 1, deadline: int = 2):
        key = (dwell, deadline)
        if key not in ResidenceLeanReplay._cache:
            raw = residence_problem(dwell, deadline)
            code, meta = emit_source(raw, solve_residence(raw))
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            ResidenceLeanReplay._cache[key] = (code, meta, solve_residence(raw))
        return ResidenceLeanReplay._cache[key]

    def test_short_and_long_horizons_replay_with_audited_axioms(self):
        for dwell, deadline in ((1, 2), (2, 4)):
            with self.subTest(dwell=dwell, deadline=deadline):
                _, meta, receipt = self._positive(dwell, deadline)
                self.assertEqual(meta["scope"]["horizon"], dwell + deadline)
                self.assertEqual(len(meta["theorem_names"]), 2 + len(receipt["probability_by_initial_state"]))

    def test_false_start_value_rejected(self):
        code, _, receipt = self._positive()
        values = [rational_expr(Fraction(v)) for v in receipt["probability_by_initial_state"]]
        bad = list(values)
        bad[0] = rational_expr(Fraction(receipt["probability_by_initial_state"][0]) + Fraction(1, 81))
        changed = change_line(code, "def values ", _fin_case("y", values, 4), _fin_case("y", bad, 4))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_wrong_dwell_or_entry_deadline_rejected(self):
        code, _, _ = self._positive()
        for prefix, old, new in (("def dwell ", ":= 1", ":= 2"), ("def latest ", ":= 2", ":= 1")):
            with self.subTest(prefix=prefix):
                changed = change_line(code, prefix, old, new)
                assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_target_set_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def targetSet ", "({1, 3} : Finset (Fin 4))", "({1} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_admitting_infeasible_action_breaks_source_binding(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def options ",
                              "(if y = (2 : Fin 4) then ({0} : Finset (Fin 2))",
                              "(if y = (2 : Fin 4) then ({0, 1} : Finset (Fin 2))")
        assert_semantic_rejection(self, code, changed, "options_exact", FILENAME)


if __name__ == "__main__":
    unittest.main()
