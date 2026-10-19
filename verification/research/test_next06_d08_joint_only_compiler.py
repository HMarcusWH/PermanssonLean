"""NEXT-06/D-08: actual original-margin and forbidden-singleton compiler fixture."""
import subprocess
import tempfile
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "PermanssonResearch/GrammarRobust/JointOnlyCertifiedFixture.lean"

CONTROL = """import PermanssonResearch.GrammarRobust.JointOnlyCertifiedFixture
open PermanssonResearch.GrammarRobust
open PermanssonResearch.GrammarRobust.BooleanModel
open PermanssonResearch.GrammarRobust.BooleanEffects
open PermanssonLean
open PermanssonLean.RegimeSpecification

theorem original_or_singleton_control :
    blockMargin baseline bank fine actionBlock spec
      (propertyAtOne orP) comparison = (0 : ℝ) := by
  exact or_singleton_margins_zero.1
"""


class JointOnlyCompilerAcceptance(unittest.TestCase):
    def compiler(self, source: str):
        with tempfile.TemporaryDirectory(prefix="d08-lean-") as tmp:
            path = Path(tmp) / "JointOnlySemantic.lean"
            path.write_text(source, encoding="utf-8")
            try:
                return subprocess.run(
                    ["lake", "env", "lean", str(path)],
                    cwd=ROOT, capture_output=True, text=True,
                    timeout=240, check=False)
            except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
                self.fail("real pinned Lean compiler required: " + str(exc))

    def test_actual_original_margin_control_and_false_mutant(self):
        self.assertTrue(SOURCE.is_file(), "no source module")
        positive = self.compiler(CONTROL)
        self.assertEqual(positive.returncode, 0, positive.stdout + positive.stderr)
        anchor = "= (0 : ℝ) := by"
        self.assertEqual(CONTROL.count(anchor), 1)
        mutant = CONTROL.replace(anchor, "= (1 : ℝ) := by")
        negative = self.compiler(mutant)
        output = negative.stdout + negative.stderr
        self.assertNotEqual(negative.returncode, 0,
                            "mathematically false singleton OR margin compiled")
        self.assertIn("error:", output)
        self.assertTrue("type mismatch" in output.lower() or
                        "unsolved goals" in output.lower(),
                        "mutant was rejected for something other than its proof:\n"
                        + output[-4500:])
        for bad in ("unknown identifier", "unknown module", "unexpected token",
                    "no such file", "out of memory", "maximum heartbeat"):
            self.assertNotIn(bad, output.lower())


if __name__ == "__main__":
    unittest.main()
