"""NEXT-06.1: actual pinned Lean checks of the native kernel theorem.

Neither an absent compiler nor a parser failure counts as a semantic mutant.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MODULE = ROOT / "PermanssonResearch/ReverseSolver/NonlinearPeriodThreeRealization.lean"
MODULE_IMPORT = "PermanssonResearch.ReverseSolver.NonlinearPeriodThreeRealization"
NEGATIVE_BAD = re.compile(r"unknown (module|identifier|constant|tactic)|file not found|"
                          r"failed to import|unexpected token|parser error|out of memory|"
                          r"maximum heartbeat|timed out|object file|failed to synthesize",
                          re.I)


class Next06LeanKernel(unittest.TestCase):
    def test_compiled_signatures_axioms_and_false_atom(self):
        self.assertTrue(MODULE.is_file())
        self.assertIsNotNone(shutil.which("lake"), "pinned lake executable required")
        source = MODULE.read_text(encoding="utf-8")
        start = "theorem phase_aware_cycle :"
        self.assertIn(start, source)

        probe = ("import " + MODULE_IMPORT + "\n"
                 "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"
                 "#check period_three_matrix_eq_induced\n"
                 "#check phase_aware_cycle\n"
                 "#check period_three_world_fixed\n"
                 "#check phase_aware_not_phase_blind\n"
                 "#print axioms period_three_matrix_eq_induced\n"
                 "#print axioms phase_aware_cycle\n"
                 "#print axioms phase_aware_not_phase_blind\n")
        with tempfile.TemporaryDirectory(prefix="next06_", dir=ROOT / ".lake") as tmp:
            path = Path(tmp) / "NativeProbe.lean"
            path.write_text(probe, encoding="utf-8")
            success = subprocess.run(["lake", "env", "lean", str(path)],
                                     cwd=ROOT, capture_output=True, text=True,
                                     timeout=600)
            output = success.stdout + success.stderr
            self.assertEqual(success.returncode, 0, output)
            self.assertNotIn("sorryAx", output)
            for name in ("period_three_matrix_eq_induced", "phase_aware_cycle",
                         "phase_aware_not_phase_blind"):
                self.assertIn(name, output)

            # Leave all syntax/imports in place; reverse one correct conclusion.
            mutant = probe + (
                "example : nextState phaseAwarePolicy start = (2, true) := by\n"
                "  exact phase_aware_cycle.1\n")
            bad = Path(tmp) / "FalseButWellTypedCycle.lean"
            bad.write_text(mutant, encoding="utf-8")
            run = subprocess.run(["lake", "env", "lean", str(bad)],
                                 cwd=ROOT, capture_output=True, text=True,
                                 timeout=600)
            fail = run.stdout + run.stderr
            self.assertNotEqual(run.returncode, 0, "false cycle theorem passed")
            self.assertIsNone(NEGATIVE_BAD.search(fail), fail)
            self.assertTrue("type mismatch" in fail.lower()
                            or "application type mismatch" in fail.lower()
                            or "unsolved goals" in fail.lower(), fail)


if __name__ == "__main__":
    unittest.main()
