"""Pinned-Lean replay of checked finite almost-sure safety cores bound to alpha/P/U.

The reflected control system is `boundControlSystem` over the exact source
input; the instance theorems inherit the infinite-horizon path-law safety
characterization. A pass proves bounded instance theorem elaboration with an
audited axiom set, not external provenance, identification or release.
"""
from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.safety import parse_safety_problem, propose_safety_core
from permansson_app.proof.control_emit import _fin_case
from permansson_app.proof.safety_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedSafetyCore.lean"


def safety_problem() -> dict:
    """Safe region {0,1,2} of a 2x2 joint space. State 2 leaks under every
    action, state 1 can only move to 2, state 0 can stay: the pruning chain is
    {0,1,2} -> {0,1} -> {0}."""
    S, X = ["s0", "s1"], ["x0", "x1"]
    feasible = {("s0", "x0"): ["stay", "risky"], ("s0", "x1"): ["risky"],
                ("s1", "x0"): ["stay", "risky"], ("s1", "x1"): ["stay"]}
    alpha = {("s0", "x0"): {"stay": "1/2", "risky": "1/2"},
             ("s0", "x1"): {"stay": "0", "risky": "1"},
             ("s1", "x0"): {"stay": "1", "risky": "0"},
             ("s1", "x1"): {"stay": "1", "risky": "0"}}
    P = {("s0", "x0", "stay"): {"x0": "1", "x1": "0"},
         ("s0", "x0", "risky"): {"x0": "1/2", "x1": "1/2"},
         ("s0", "x1", "risky"): {"x0": "1", "x1": "0"},
         ("s1", "x0", "stay"): {"x0": "0", "x1": "1"},
         ("s1", "x0", "risky"): {"x0": "1/2", "x1": "1/2"},
         ("s1", "x1", "stay"): {"x0": "0", "x1": "1"}}

    def U(s, x, a):
        if (s, x, a) == ("s0", "x0", "risky"):
            return {"s0": "1/2", "s1": "1/2"}
        if (s, x, a) == ("s0", "x1", "risky"):
            return {"s0": "0", "s1": "1"}
        return {s: "1", ("s1" if s == "s0" else "s0"): "0"}

    model = {
        "format": "Permansson.App.FiniteStrategicWorld.v1",
        "states": {"strategic": S, "world": X, "actions": ["stay", "risky"]},
        "feasible": [{"s": s, "x": x, "actions": feasible[s, x]} for s in S for x in X],
        "alpha": [{"s": s, "x": x, "weights": alpha[s, x]} for s in S for x in X],
        "P": [{"s": s, "x": x, "a": a, "weights": P[s, x, a]}
              for s in S for x in X for a in feasible[s, x]],
        "U": [{"s": s, "x": x, "a": a, "xp": xp, "weights": U(s, x, a)}
              for s in S for x in X for a in feasible[s, x] for xp in X],
    }
    return {"format": "Permansson.App.FiniteSafetyCore.v1", "model": model,
            "safe": [{"strategic": "s0", "world": "x0"}, {"strategic": "s0", "world": "x1"},
                     {"strategic": "s1", "world": "x0"}]}


class SafetyCoreLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict] | None = None

    def _positive(self):
        if SafetyCoreLeanReplay._cache is None:
            problem = parse_safety_problem(safety_problem())
            code, meta = emit_source(problem, propose_safety_core(problem))
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            SafetyCoreLeanReplay._cache = (code, meta)
        return SafetyCoreLeanReplay._cache

    def test_two_step_pruning_core_replays_with_audited_axioms(self):
        _, meta = self._positive()
        self.assertEqual(meta["scope"]["core"], [0])
        self.assertEqual(meta["scope"]["excluded_from_core"], [1, 2])
        self.assertIn("not_almost_sure_1", meta["theorem_names"])
        self.assertIn("almost_sure_safe_0", meta["theorem_names"])

    def test_overclaimed_core_rejected(self):
        code, _ = self._positive()
        changed = change_line(code, "def core ", "({0} : Finset (Fin 4))", "({0, 1} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_underclaimed_core_rejected(self):
        code, _ = self._positive()
        changed = change_line(code, "def core ", "({0} : Finset (Fin 4))", "(∅ : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_leaking_witness_rejected(self):
        code, _ = self._positive()
        good = _fin_case("y", ["(0 : Fin 2)", "(1 : Fin 2)", "(0 : Fin 2)", "(0 : Fin 2)"], 4)
        bad = _fin_case("y", ["(1 : Fin 2)", "(1 : Fin 2)", "(0 : Fin 2)", "(0 : Fin 2)"], 4)
        changed = change_line(code, "def witness ", good, bad)
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_safe_region_rejected(self):
        code, _ = self._positive()
        changed = change_line(code, "def safeRegion ", "({0, 1, 2} : Finset (Fin 4))",
                              "({0, 1, 2, 3} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_admitting_infeasible_action_breaks_source_binding(self):
        code, _ = self._positive()
        changed = change_line(code, "def options ",
                              "(if y = (1 : Fin 4) then ({1} : Finset (Fin 2))",
                              "(if y = (1 : Fin 4) then ({0, 1} : Finset (Fin 2))")
        assert_semantic_rejection(self, code, changed, "options_exact", FILENAME)


if __name__ == "__main__":
    unittest.main()
