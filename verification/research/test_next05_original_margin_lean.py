"""Actual source-bound complete law and full-B1 compiler receipts for NEXT-05.2."""
import pathlib,re,shutil,subprocess,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
MOD="PermanssonResearch.MultiAgent.MeasurableProductTwoMargin"
NAMES=("pushInitial_dirac_two","pullbackWholePathProperty",
       "baseline_whole_path_property_two","intervention_whole_path_property_two",
       "original_margin_transport_two")
class Compiler(unittest.TestCase):
    def test_full_original_margin_types_and_axioms(self):
        self.assertTrue(shutil.which("lake"),"Lean compiler unavailable")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as d:
            f=pathlib.Path(d)/"MarginProbe.lean"
            f.write_text("import "+MOD+"\n"+
             "open PermanssonResearch.MultiAgent.MeasurableProduct.Two\n"+
             "\n".join("#check "+n+"\n#print axioms "+n for n in NAMES)+"\n")
            p=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                             capture_output=True,text=True,timeout=600)
            out=p.stdout+p.stderr
            self.assertEqual(p.returncode,0,out)
            for n in NAMES: self.assertIn(n,out)
            for ax in re.findall(r"depends on axioms:\\s*\\[([^\\]]*)\\]",out):
                self.assertLessEqual({x.strip() for x in ax.split(",") if x.strip()},
                 {"propext","Quot.sound","Classical.choice"},out)
            self.assertNotIn("sorryAx",out)
if __name__=="__main__":unittest.main()
