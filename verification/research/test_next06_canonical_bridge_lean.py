"""P-06.2 substage: genuine native deterministic kernel and canonical limit.

The original typed path law must remain the source of the a.s. occupation
theorem. Direct Lean proofs, no external source assumptions or canned tables.
"""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MODULE = "PermanssonResearch.ReverseSolver.NonlinearPeriodThreeCanonical"
SOURCE = ROOT / "PermanssonResearch/ReverseSolver/NonlinearPeriodThreeCanonical.lean"
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}


class NativeCanonicalCompiler(unittest.TestCase):
    def test_actual_native_occupation_statement_and_axioms(self):
        self.assertTrue(SOURCE.is_file())
        self.assertIsNotNone(shutil.which("lake"), "pinned Lean 4.34.0 required")
        probe = (
            f"import {MODULE}\n"
            "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"
            "#check native_inducedKernel_eq_deterministic\n"
            "#check native_actual_occupation_ae_limit\n"
            "#print axioms native_inducedKernel_eq_deterministic\n"
            "#print axioms native_actual_occupation_ae_limit\n"
        )
        with tempfile.TemporaryDirectory(prefix="next06canon_", dir=ROOT/".lake") as tmp:
            f = Path(tmp)/"CanonicalProbe.lean"
            f.write_text(probe, encoding="utf-8")
            cp = subprocess.run(["lake", "env", "lean", str(f)], cwd=ROOT,
                                text=True, capture_output=True, timeout=600)
            msg = cp.stdout+cp.stderr
            self.assertEqual(cp.returncode, 0, msg)
            self.assertNotIn("sorryAx", msg)
            self.assertIn("native_actual_occupation_ae_limit", msg)
            for axlist in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", msg):
                self.assertLessEqual(set(x.strip() for x in axlist.split(",") if x.strip()),
                                     ALLOWED, msg)

    def test_wrong_native_next_row_semantically_rejected(self):
        self.assertIsNotNone(shutil.which("lake"), "pinned Lean required")
        probe = (
            f"import {MODULE}\n"
            "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"
            "example : nextState phaseAwarePolicy start = (2, true) := by\n"
            "  exact phase_aware_cycle.1\n"
        )
        with tempfile.TemporaryDirectory(prefix="next06wrong_",dir=ROOT/".lake") as tmp:
            f=Path(tmp)/"WrongNextRow.lean"
            f.write_text(probe,encoding="utf8")
            cp=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                text=True,capture_output=True,timeout=600)
            msg=cp.stdout+cp.stderr
            self.assertNotEqual(cp.returncode,0,"wrong phase transition compiled")
            self.assertFalse(re.search("unknown module|file not found|failed to import|"
                  "unexpected token|parser error|out of memory|maximum heartbeat|"
                  "timed out",msg,re.I),msg)
            self.assertTrue("type mismatch" in msg.lower()
                 or "unsolved goals" in msg.lower(),msg)


if __name__ == "__main__":
    unittest.main()
