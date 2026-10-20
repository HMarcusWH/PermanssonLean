"""Pinned Lean compiler checks for NEXT-05.2. No soft skips."""
import pathlib,re,shutil,subprocess,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
MODULE="PermanssonResearch.MultiAgent.MeasurableProductTwoPathLaw"
NAMES=("closed_loop_application","open_loop_application","closed_loop_kernel_two",
       "open_loop_kernel_two","path_law_map_two","closed_loop_path_law_two",
       "open_loop_path_law_two")
class Tests(unittest.TestCase):
    def test_compiler_and_axioms(self):
        self.assertTrue(shutil.which("lake"),"required Lean unavailable")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as d:
            f=pathlib.Path(d)/"Test.lean"
            f.write_text("import "+MODULE+"\nopen PermanssonResearch.MultiAgent.MeasurableProduct.Two\n"+
                         "\n".join("#check "+n+"\n#print axioms "+n for n in NAMES)+"\n")
            p=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                              capture_output=True,text=True,timeout=600)
            out=p.stdout+p.stderr
            self.assertEqual(p.returncode,0,out)
            for n in NAMES:self.assertIn(n,out)
            for s in re.findall(r"depends on axioms:\\s*\\[([^\\]]*)\\]",out):
                self.assertLessEqual({x.strip() for x in s.split(",") if x.strip()},
                                     {"propext","Quot.sound","Classical.choice"},out)
            self.assertNotIn("sorryAx",out)
if __name__=="__main__":unittest.main()
