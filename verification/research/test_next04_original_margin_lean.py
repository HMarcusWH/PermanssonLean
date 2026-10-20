"""Real Lean build and transitive axiom test for the new original-margin bridge."""
import pathlib,shutil,subprocess,tempfile,re,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
NAMES=("discountedWholePathProperty","projectedDiscountedProperty",
       "coarseOutputProfile","discounted_original_margin_abs_le",
       "discounted_original_margin_positive_of_gap",
       "discounted_reported_margin_abs_le","exact_thirteen_fortyfive_budget")
class Tests(unittest.TestCase):
    def test_compiler_and_axioms(self):
        self.assertTrue(shutil.which("lake"),"Lean/Lake unavailable")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as d:
            f=pathlib.Path(d)/"Marginal.lean"
            f.write_text("import PermanssonResearch.Quotient.DiscountedOriginalMarginExamples\n"+
              "open PermanssonResearch.Quotient.DiscountedOriginalMargin\n"+
              "\n".join("#check "+s+"\n#print axioms "+s for s in NAMES)+"\n")
            run=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                               capture_output=True,text=True,timeout=600)
            out=run.stdout+run.stderr
            self.assertEqual(run.returncode,0,out)
            for n in NAMES: self.assertIn(n,out)
            for axioms in re.findall(r"depends on axioms:\\s*\\[([^\\]]*)\\]",out):
                self.assertLessEqual({x.strip() for x in axioms.split(",") if x.strip()},
                                     {"propext","Quot.sound","Classical.choice"},out)
            self.assertNotIn("sorryAx",out)
if __name__=="__main__":unittest.main()
