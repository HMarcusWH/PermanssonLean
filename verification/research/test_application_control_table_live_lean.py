"""Pinned-Lean replay of checked finite Bellman control tables bound to alpha/P/U.

Generated source reflects the exact rational source model; the Lean control
system is built from it by `boundControlSystem`. These tests run after the
canonical Research library build. A pass proves bounded instance theorem
elaboration with an audited axiom set; it does NOT authenticate external
provenance, identify a causal mechanism, or approve a release.
"""
from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.hitting import parse_hitting_problem, propose_bellman
from permansson_app.proof.control_emit import _fin_case, emit_source
from permansson_app.proof.finite_emit import rational_expr
from fractions import Fraction
from test_application_lp_bridge_live_lean import _audited_axioms

EXAMPLE = APP / "src/permansson_app/data/examples/control_hitting.v1.json"


def rich_problem() -> dict:
    """Two strategic and two world states with an infeasible action, a
    forbidden state, a tie at one remaining transition and a strictly
    suboptimal feasible action from two remaining transitions on."""
    S, X = ["s0", "s1"], ["x0", "x1"]
    feasible = {("s0", "x0"): ["safe", "risky"], ("s0", "x1"): ["safe"],
                ("s1", "x0"): ["risky"], ("s1", "x1"): ["safe", "risky"]}
    alpha = {("s0", "x0"): {"safe": "1/2", "risky": "1/2"},
             ("s0", "x1"): {"safe": "1", "risky": "0"},
             ("s1", "x0"): {"safe": "0", "risky": "1"},
             ("s1", "x1"): {"safe": "1", "risky": "0"}}
    P = {("s0", "x0", "safe"): {"x0": "1/2", "x1": "1/2"},
         ("s0", "x0", "risky"): {"x0": "0", "x1": "1"},
         ("s0", "x1", "safe"): {"x0": "0", "x1": "1"},
         ("s1", "x0", "risky"): {"x0": "0", "x1": "1"},
         ("s1", "x1", "safe"): {"x0": "0", "x1": "1"},
         ("s1", "x1", "risky"): {"x0": "1", "x1": "0"}}

    def U(s, x, a):
        if (s, x, a) == ("s0", "x0", "risky"):
            return {"s0": "1/2", "s1": "1/2"}
        if (s, x, a) == ("s1", "x0", "risky"):
            return {"s0": "1/3", "s1": "2/3"}
        return {s: "1", ("s1" if s == "s0" else "s0"): "0"}

    model = {
        "format": "Permansson.App.FiniteStrategicWorld.v1",
        "states": {"strategic": S, "world": X, "actions": ["safe", "risky"]},
        "feasible": [{"s": s, "x": x, "actions": feasible[s, x]} for s in S for x in X],
        "alpha": [{"s": s, "x": x, "weights": alpha[s, x]} for s in S for x in X],
        "P": [{"s": s, "x": x, "a": a, "weights": P[s, x, a]}
              for s in S for x in X for a in feasible[s, x]],
        "U": [{"s": s, "x": x, "a": a, "xp": xp, "weights": U(s, x, a)}
              for s in S for x in X for a in feasible[s, x] for xp in X],
    }
    return {"format": "Permansson.App.FiniteHittingControl.v1", "model": model,
            "goal": [{"strategic": "s0", "world": "x1"}],
            "forbidden": [{"strategic": "s1", "world": "x1"}], "horizon": 3}


def _emit(raw: dict):
    problem = parse_hitting_problem(raw)
    receipt = propose_bellman(problem)
    return emit_source(problem, receipt), receipt


def _compile(code: str):
    if shutil.which("lake") is None or not (ROOT / ".lake").is_dir():
        raise AssertionError("Real pinned Research Lean compiler required; no skip/stub")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake", prefix="app-control-") as td:
        source = Path(td) / "ReifiedControlTable.lean"
        source.write_text(code, encoding="utf-8")
        process = subprocess.run(
            ["lake", "env", "lean", str(source)], cwd=ROOT,
            capture_output=True, text=True, timeout=450)
    result = process.stdout + "\n" + process.stderr
    if len(result) > 250000:
        raise AssertionError("unbounded Lean compiler output")
    return process.returncode, result


def _change_line(code: str, prefix: str, old: str, new: str) -> str:
    lines = code.splitlines()
    locations = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    if len(locations) != 1:
        raise AssertionError("missing/ambiguous control-source mutation target " + prefix)
    before = lines[locations[0]]
    if before.count(old) != 1:
        raise AssertionError("mutation fragment must occur exactly once: " + old)
    lines[locations[0]] = before.replace(old, new)
    return "\n".join(lines) + "\n"


class ControlTableLeanReplay(unittest.TestCase):
    _positive_cache: dict[str, tuple[str, dict]] = {}

    def _positive(self, key: str, raw: dict):
        if key not in self._positive_cache:
            (code, meta), _ = _emit(raw)
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            self.assertFalse(meta["compiler_evidence_authenticated"])
            exitcode, log = _compile(code)
            self.assertEqual(exitcode, 0, log[-9000:])
            _audited_axioms(log, meta["theorem_qualified_names"])
            self._positive_cache[key] = (code, meta)
        return self._positive_cache[key]

    def _negative(self, original: str, changed: str, theorem: str):
        # Only a mutation of a source that compiled on the same pinned
        # compiler is a discriminating semantic mutation.
        self.assertNotEqual(sha256(original.encode()).digest(), sha256(changed.encode()).digest())
        lhs, rhs = original.splitlines(), changed.splitlines()
        self.assertEqual(len(lhs), len(rhs))
        self.assertEqual(sum(a != b for a, b in zip(lhs, rhs)), 1,
                         "mutation must change exactly one source line")
        exitcode, log = _compile(changed)
        self.assertNotEqual(exitcode, 0, "false control table was accepted")
        lower = log.lower()
        for forbidden in ("unknown module", "unknown identifier", "failed to import",
                          "unexpected token", "syntax error", "out of memory",
                          "maximum number of heartbeats", "failed to synthesize",
                          "type mismatch", "timed out", "timeout"):
            self.assertNotIn(forbidden, lower, "unrelated compiler failure: " + forbidden)
        errors = [int(m.group(1)) for m in re.finditer(
            r"ReifiedControlTable\.lean:(\d+):\d+: error", log)]
        self.assertTrue(errors, "no source-anchored Lean error:\n" + log[-3000:])
        # Each theorem block runs from its `theorem` line to the next blank
        # line. The false obligation must fail inside the targeted theorem;
        # downstream instance theorems may also fail, but no definition,
        # import or syntax position may.
        blocks = {}
        for i, line in enumerate(rhs, 1):
            if line.startswith("theorem "):
                name = line.split()[1]
                end = next((j for j in range(i, len(rhs) + 1) if not rhs[j - 1].strip()), len(rhs))
                blocks[name] = (i, end)
        start, end = blocks[theorem]
        self.assertTrue(any(start <= err <= end for err in errors),
                        f"no error at falsified {theorem}@{start}: {errors}\n" + log[-3000:])
        self.assertTrue(all(any(a <= err <= b for a, b in blocks.values()) for err in errors),
                        f"error outside theorem proofs: {errors}\n" + log[-3000:])

    def test_packaged_example_replays_with_audited_axioms(self):
        _, meta = self._positive("example", json.loads(EXAMPLE.read_text(encoding="utf-8")))
        self.assertEqual(meta["scope"], {"ns": 1, "nx": 2, "na": 2, "joint_states": 2, "horizon": 3})

    def test_partial_feasibility_forbidden_state_and_joint_order_replay(self):
        _, meta = self._positive("rich", rich_problem())
        self.assertEqual(meta["scope"]["joint_states"], 4)
        self.assertEqual(len(meta["p_u_infeasible_normalized_extensions"]), 2)

    def test_false_value_rejected_at_checker(self):
        code, _ = self._positive("rich", rich_problem())
        changed = _change_line(code, "def values ", rational_expr(Fraction(7, 8)),
                               rational_expr(Fraction(8, 9)))
        self._negative(code, changed, "receipt_checked")

    def test_strictly_suboptimal_feasible_action_rejected(self):
        code, _ = self._positive("rich", rich_problem())
        # chosen t=1 (two remaining transitions): safe is strictly optimal at
        # state 0; replace it with the admitted but worse risky action.
        row = _fin_case("y", ["(0 : Fin 2)", "(0 : Fin 2)", "(1 : Fin 2)", "(0 : Fin 2)"], 4)
        bad = _fin_case("y", ["(1 : Fin 2)", "(0 : Fin 2)", "(1 : Fin 2)", "(0 : Fin 2)"], 4)
        changed = _change_line(code, "def chosen ", f"(if t = 1 then {row}", f"(if t = 1 then {bad}")
        self._negative(code, changed, "receipt_checked")

    def test_infeasible_selected_action_rejected(self):
        code, _ = self._positive("rich", rich_problem())
        row = _fin_case("y", ["(0 : Fin 2)", "(0 : Fin 2)", "(1 : Fin 2)", "(0 : Fin 2)"], 4)
        bad = _fin_case("y", ["(0 : Fin 2)", "(0 : Fin 2)", "(0 : Fin 2)", "(0 : Fin 2)"], 4)
        changed = _change_line(code, "def chosen ", f"(if t = 0 then {row}", f"(if t = 0 then {bad}")
        self._negative(code, changed, "receipt_checked")

    def test_false_terminal_event_rejected(self):
        code, _ = self._positive("rich", rich_problem())
        changed = _change_line(code, "  goal := ", "({1} : Finset (Fin 4))",
                               "({0, 1} : Finset (Fin 4))")
        self._negative(code, changed, "receipt_checked")

    def test_reversed_time_direction_rejected(self):
        code, _ = self._positive("rich", rich_problem())
        rows = [["0", "1", "0", "0"], ["1/2", "1", "1/3", "0"],
                ["3/4", "1", "1/3", "0"], ["7/8", "1", "1/3", "0"]]
        text = [_fin_case("y", [rational_expr(Fraction(v)) for v in r], 4) for r in rows]
        original = f"(if t = 1 then {text[1]} else (if t = 2 then {text[2]} else (if t = 3 then {text[3]}"
        swapped = f"(if t = 1 then {text[3]} else (if t = 2 then {text[2]} else (if t = 3 then {text[1]}"
        changed = _change_line(code, "def values ", original, swapped)
        self._negative(code, changed, "receipt_checked")

    def test_admitting_infeasible_action_breaks_source_binding(self):
        code, _ = self._positive("rich", rich_problem())
        changed = _change_line(code, "def options ",
                               "(if y = (2 : Fin 4) then ({1} : Finset (Fin 2))",
                               "(if y = (2 : Fin 4) then ({0, 1} : Finset (Fin 2))")
        self._negative(code, changed, "options_exact")


if __name__ == "__main__":
    unittest.main()
