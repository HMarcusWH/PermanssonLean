"""NEXT-04.1: check actual imported marginal bridge with the pinned Lean."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
MODULE="PermanssonResearch.Quotient.DiscountedCanonicalBridge"
SOURCE=ROOT / "PermanssonResearch/Quotient/DiscountedCanonicalBridge.lean"


class NativeMarginalBridge(unittest.TestCase):
    def test_canonical_marginal_compiles_and_axioms(self):
        self.assertIsNotNone(shutil.which("lake"),"pinned Lean/Lake required")
        self.assertTrue(SOURCE.is_file())
        probe=(
            "import "+MODULE+"\n"
            "open PermanssonResearch.Quotient.DiscountedCanonicalBridge\n"
            "#check canonical_measure_marginal_evolution\n"
            "#check canonical_nth_marginal_eq_evolution\n"
            "#check canonical_point_start_zero\n"
            "#print axioms canonical_nth_marginal_eq_evolution\n"
            "#print axioms canonical_point_start_zero\n")
        with tempfile.TemporaryDirectory(prefix="next04_",dir=ROOT/".lake") as tmp:
            p=Path(tmp)/"CanonicalProbe.lean"
            p.write_text(probe,encoding="utf8")
            cp=subprocess.run(["lake","env","lean",str(p)],cwd=ROOT,
                              capture_output=True,text=True,timeout=600)
            message=cp.stdout+cp.stderr
            self.assertEqual(cp.returncode,0,message)
            self.assertNotIn("sorryAx",message)
            self.assertIn("canonical_nth_marginal_eq_evolution",message)


if __name__=="__main__":
    unittest.main()
