"""Actual pinned Lean/compiler/axiom acceptance for final P-04/P-05 source."""
import pathlib,re,shutil,subprocess,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
ALLOW={"propext","Classical.choice","Quot.sound"}

def check_module(testcase,module,namespace,declarations):
    testcase.assertIsNotNone(shutil.which("lake"),"required pinned Lean compiler unavailable")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake") as temp:
        path=pathlib.Path(temp)/"ProofReceipt.lean"
        path.write_text("import "+module+"\nopen "+namespace+"\n"+
           "\n".join("#check "+name+"\n#print axioms "+name for name in declarations)+"\n")
        p=subprocess.run(["lake","env","lean",str(path)],cwd=ROOT,
            capture_output=True,text=True,timeout=900)
        out=p.stdout+p.stderr
        testcase.assertEqual(p.returncode,0,out)
        for name in declarations: testcase.assertIn(name,out)
        sets=re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out)
        testcase.assertGreater(len(sets),0,"missing compiler axiom records\n"+out)
        for s in sets:
            testcase.assertLessEqual({a.strip() for a in s.split(",") if a.strip()},ALLOW,out)
        testcase.assertNotIn("sorryAx",out)
    return True

class Final04CompilerTests(unittest.TestCase):
    def test_canonical_source_and_full_margin(self):
        check_module(self,
          "PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure",
          "PermanssonResearch.Quotient.DiscountedCanonicalSourceWitness\n"+
          "open PermanssonResearch.Quotient.DiscountedCanonicalMarginClosure",
          ("canonical_discounted_output_error","point_witness_output",
           "actual_canonical_discounted_original_margin"))
    def test_actual_kernel_witness_examples_and_axioms(self):
        check_module(self,
          "PermanssonResearch.Quotient.DiscountedCanonicalWitnessExamples",
          "PermanssonResearch.Quotient.DiscountedCanonicalWitnessExamples\n"
          "open PermanssonResearch.Quotient.DiscountedCanonicalWitnessExamples.SourceBoundExactWitness",
          ("correct_frozen_discounted_budget", "wrong_frozen_discounted_budget",
           "exactKernelPointWitness", "exactKernelPointWitness_retained_one",
           "identity_canonical_full_path"))

if __name__=="__main__":unittest.main()
