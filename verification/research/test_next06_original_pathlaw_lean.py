"""Real original canonical path-law Dirac/occupation expectation compiler receipt."""
import pathlib,subprocess,tempfile,shutil,re,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
NAMES=("nativeOrbit_eq_detOrbit","native_pathLaw_dirac",
       "nativeNonlinearPathScore","nativeExpectedNonlinearScore",
       "native_expected_score_eq_actual_orbit")
class Check(unittest.TestCase):
    def test_original_pathlaw_compiles_and_axioms(self):
        self.assertTrue(shutil.which("lake"),"Lean required")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as d:
            p=pathlib.Path(d)/"NativePath.lean"
            p.write_text("import PermanssonResearch.ReverseSolver.NonlinearPeriodThreePathLaw\n"+
              "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"+
              "\n".join("#check "+n+"\n#print axioms "+n for n in NAMES)+"\n")
            c=subprocess.run(["lake","env","lean",str(p)],cwd=ROOT,
             text=True,capture_output=True,timeout=600)
            out=c.stdout+c.stderr
            self.assertEqual(c.returncode,0,out)
            for n in NAMES:self.assertIn(n,out)
            axiom_sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out)
            self.assertGreaterEqual(len(axiom_sets), 1, "missing axiom audit records: "+out)
            for ax in axiom_sets:
                self.assertLessEqual({s.strip() for s in ax.split(",") if s.strip()},
                     {"propext","Classical.choice","Quot.sound"},out)
if __name__=="__main__":unittest.main()
