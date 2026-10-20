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
            axiom_sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out)
            self.assertGreaterEqual(len(axiom_sets), 1, "missing axiom audit records: "+out)
            for axioms in axiom_sets:
                self.assertLessEqual({x.strip() for x in axioms.split(",") if x.strip()},
                                     {"propext","Quot.sound","Classical.choice"},out)
            self.assertNotIn("sorryAx",out)
    def test_wrong_discounted_certificate_is_semantically_rejected(self):
        self.assertTrue(shutil.which("lake"),"Lean/Lake unavailable")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as d:
            f=pathlib.Path(d)/"WrongBudget.lean"
            f.write_text("import PermanssonResearch.Quotient.DiscountedOriginalMarginExamples\n"+
                "open PermanssonResearch.Quotient.DiscountedOriginalMargin\n"+
                "example : (∑' n : ℕ, (1-(1/3:ℝ))*(1/3:ℝ)^n*"+
                "(1-(1-(1/5:ℝ))*(1-(1/4:ℝ))^n)) = (14/45:ℝ) := by\n"+
                "  exact exact_thirteen_fortyfive_budget\n")
            p=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                             text=True,capture_output=True,timeout=600)
            out=p.stdout+p.stderr
            self.assertNotEqual(p.returncode,0,"false budget accepted")
            self.assertFalse(re.search("unknown module|failed to import|parser error|"+
                "out of memory|timed out|maximum heartbeat",out,re.I),out)
            self.assertTrue("type mismatch" in out.lower() or
                            "unsolved goals" in out.lower(),out)

if __name__=="__main__":unittest.main()
