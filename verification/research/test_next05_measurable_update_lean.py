"""Source-bound compiler/axiom signature check for P-05 measurable update."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
PATH=ROOT/"PermanssonResearch/MultiAgent/MeasurableProductTwoUpdate.lean"
IMPORT="PermanssonResearch.MultiAgent.MeasurableProductTwoUpdate"


class MeasurableUpdateLean(unittest.TestCase):
    def test_actual_update_pushforward_and_axioms(self):
        self.assertTrue(PATH.is_file())
        self.assertIsNotNone(shutil.which("lake"),"real pinned Lean required")
        probe=("import "+IMPORT+"\n"
               "open PermanssonResearch.MultiAgent.MeasurableProduct.Two\n"
               "#check update_map_two\n"
               "#check world_pullback_two\n"
               "#check common_update_pullback_two\n"
               "#check private_update_pullback_two\n"
               "#print axioms update_map_two\n"
               "#print axioms world_pullback_two\n")
        with tempfile.TemporaryDirectory(prefix="next05upd_",dir=ROOT/".lake") as t:
            f=Path(t)/"UpdateProbe.lean"
            f.write_text(probe,encoding="utf-8")
            result=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                capture_output=True,text=True,timeout=600)
            output=result.stdout+result.stderr
            self.assertEqual(result.returncode,0,output)
            self.assertNotIn("sorryAx",output)
            self.assertIn("update_map_two",output)


if __name__=="__main__":
    unittest.main()
