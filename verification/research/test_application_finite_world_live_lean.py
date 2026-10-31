"""Pinned-Lean S03 finite-world source reification: real instance proofs and mutations.

All generated source comes from the exact rational alpha/P/U input. These tests
must execute after the canonical Research library build. They do NOT authenticate
external JSON provenance, identify a causal mechanism, or award GR/PR status.
"""
from __future__ import annotations

from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.finite_world import parse_finite_world
from permansson_app.proof.finite_emit import emit_source
from test_application_lp_bridge_live_lean import _audited_axioms
from application_bridge_replay import run_bounded

EXAMPLE = APP / "src/permansson_app/data/examples/finite_world.v1.model.json"
MODULE = "PermanssonResearch.ApplicationBridge.ReifiedFiniteWorld"


def _raw():
    return json.loads(EXAMPLE.read_text(encoding="utf-8"))


def _canonical():
    return emit_source(parse_finite_world(_raw()))


def _with_infeasible():
    raw = deepcopy(_raw())
    row = next(r for r in raw["feasible"] if r["s"] == "s0" and r["x"] == "x0")
    row["actions"] = ["stay"]
    weights = next(r for r in raw["alpha"] if r["s"] == "s0" and r["x"] == "x0")["weights"]
    weights["stay"], weights["switch"] = "1", "0"
    raw["P"] = [r for r in raw["P"]
                if not (r["s"] == "s0" and r["x"] == "x0" and r["a"] == "switch")]
    raw["U"] = [r for r in raw["U"]
                if not (r["s"] == "s0" and r["x"] == "x0" and r["a"] == "switch")]
    return emit_source(parse_finite_world(raw))


def _compile(code: str):
    if shutil.which("lake") is None or not (ROOT / ".lake").is_dir():
        raise AssertionError("Real pinned Research Lean compiler required; no skip/stub")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake", prefix="app-finite-") as td:
        source = Path(td) / "ReifiedFiniteWorld.lean"
        source.write_text(code, encoding="utf-8")
        returncode, result = run_bounded(["lake", "env", "lean", str(source)], ROOT, 450)
    if len(result) > 250000:
        raise AssertionError("unbounded Lean compiler output")
    return returncode, result


def _change_line(code: str, prefix: str, replacement: str):
    lines = code.splitlines()
    locations = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    if len(locations) != 1:
        raise AssertionError("missing/ambiguous finite-source mutation target " + prefix)
    before = lines[locations[0]]
    if before == replacement:
        raise AssertionError("mutation has not changed the source")
    lines[locations[0]] = replacement
    result = "\n".join(lines) + "\n"
    if len(result.splitlines()) != len(code.splitlines()):
        raise AssertionError("mutation changed source line count")
    return result


class FiniteWorldSourceCompiler(unittest.TestCase):
    def _positive(self, generated):
        code, meta = generated
        self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
        self.assertFalse(meta["independent_axiom_audit"])
        self.assertFalse(meta["release_authorized"])
        self.assertEqual(sha256(code.encode("utf-8")).hexdigest(),
                         meta["lean_source_sha256"])
        self.assertEqual(len(meta["theorem_names"]),
                         1 + meta["number_of_induced_atoms"])
        exitcode, log = _compile(code)
        self.assertEqual(exitcode, 0, log[-9000:])
        expected = [MODULE + "." + name for name in meta["theorem_names"]]
        self.assertEqual(set(_audited_axioms(log, expected)), set(expected))
        return code, meta

    def _negative(self, original, changed, expected_field):
        source, meta = self._positive(original)
        self.assertNotEqual(source, changed)
        self.assertEqual(
            sum(a != b for a, b in zip(source.splitlines(), changed.splitlines())), 1)
        exitcode, log = _compile(changed)
        self.assertNotEqual(exitcode, 0, "false finite source compiled")
        low = log.lower()
        for unrelated in ("unknown module", "unknown identifier", "failed to import",
                          "unexpected token", "parser error", "out of memory",
                          "timed out", "timeout", "failed to synthesize"):
            self.assertNotIn(unrelated, low, "unrelated rejection: " + unrelated)
        self.assertIn("error:", low, log[-4000:])
        # The first-order failure must be source-local to the falsified
        # primitive proof or induced atom, never just a later unrelated error.
        marker = (expected_field if expected_field.startswith("theorem ")
                  else "  " + expected_field + " := ")
        targets = [i for i, line in enumerate(changed.splitlines(), 1)
                   if line.startswith(marker)]
        self.assertEqual(len(targets), 1, "missing/ambiguous obligation")
        errors = [int(m.group(1)) for m in re.finditer(
            r"ReifiedFiniteWorld\.lean:(\d+):\d+: error:", log)]
        self.assertTrue(errors, "no source-anchored Lean error: " + log[-4000:])
        self.assertTrue(any(0 <= err - targets[0] <= 7 for err in errors),
                        "false source did not fail at its claimed obligation: " + log[-4000:])

    def test_actual_joint_atoms_and_axioms(self):
        _, meta = self._positive(_canonical())
        self.assertEqual(meta["number_of_induced_atoms"], 16)
        self.assertEqual(len(meta["theorem_names"]), 17)

    def test_actual_infeasible_action_normalized_extensions(self):
        _, meta = self._positive(_with_infeasible())
        self.assertEqual(len(meta["p_u_infeasible_normalized_extensions"]), 1)

    def test_forged_feasibility_breaks_input_proof(self):
        source, _ = _canonical()
        changed = _change_line(source, "  feasible := ",
                               "  feasible := fun s x a => False")
        self._negative(_canonical(), changed, "alpha_zero_of_infeasible")

    def test_forged_alpha_breaks_row_normalization(self):
        source, _ = _canonical()
        changed = _change_line(source, "  alpha := ",
                               "  alpha := fun s x a => (0 : ℚ)")
        self._negative(_canonical(), changed, "alpha_sum_one")

    def test_forged_world_transition_breaks_row_normalization(self):
        source, _ = _canonical()
        changed = _change_line(source, "  world := ",
                               "  world := fun s x a xp => (0 : ℚ)")
        self._negative(_canonical(), changed, "world_sum_one")

    def test_forged_strategic_update_breaks_row_normalization(self):
        source, _ = _canonical()
        changed = _change_line(source, "  update := ",
                               "  update := fun s x a xp sp => (0 : ℚ)")
        self._negative(_canonical(), changed, "update_sum_one")

    def test_false_induced_atom_is_not_provable(self):
        source, _ = _canonical()
        lines = source.splitlines()
        pos = next(i for i, line in enumerate(lines)
                   if line.startswith("theorem atom_0_0 "))
        self.assertTrue(lines[pos+3].lstrip().endswith(":= by decide +kernel"))
        lines[pos+3] = "      (7 : ℚ) := by decide +kernel"
        changed = "\n".join(lines) + "\n"
        self._negative(_canonical(), changed, "theorem atom_0_0 ")


if __name__ == "__main__":
    unittest.main()
