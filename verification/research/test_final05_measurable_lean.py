"""Source-bound matched two-player closed/open-loop Lean theorem verification."""
import pathlib,re,shutil,subprocess,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
NAMES=("matchedBinaryClosed","matchedBinaryOpen","matched_closed_kernel_two",
  "matched_open_kernel_two","matched_closed_loop_original_margin",
  "matched_open_loop_original_margin","matched_closed_loop_all_initial_paths",
  "matched_open_loop_all_initial_paths")

class MatchedCompiler(unittest.TestCase):
    def test_full_original_margin_compiler_axioms(self):
        self.assertTrue(shutil.which("lake"),"Lean required")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as temp:
            src=pathlib.Path(temp)/"Matched.lean"
            src.write_text("import PermanssonResearch.MultiAgent.MeasurableProductTwoOriginalMarginClosure\n"
               "open PermanssonResearch.MultiAgent.MeasurableProduct.Two\n"+
               "\n".join("#check "+n+"\n#print axioms "+n for n in NAMES)+"\n")
            p=subprocess.run(["lake","env","lean",str(src)],cwd=ROOT,
                 capture_output=True,text=True,timeout=900)
            output=p.stdout+p.stderr
            self.assertEqual(p.returncode,0,output)
            for n in NAMES:self.assertIn(n,output)
            sets=re.findall(r"depends on axioms:\s*\[([^\]]*)\]",output)
            self.assertTrue(sets,output)
            for a in sets:
                self.assertLessEqual({s.strip() for s in a.split(",") if s.strip()},
                                     {"propext","Quot.sound","Classical.choice"})
            self.assertNotIn("sorryAx",output)
if __name__=="__main__":unittest.main()
