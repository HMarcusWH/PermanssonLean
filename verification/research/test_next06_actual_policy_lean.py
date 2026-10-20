"""Lean compiler/axiom scope check for native nonlinear boundary."""
import pathlib,shutil,subprocess,tempfile,re,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
NAMES=("boolean_probability_score_of_true_mass","boolean_rational_score_bounds",
"classwise_barycenter_invalid","native_phase_blind_world_eq",
"native_phase_blind_tail_score_le_five_sixths","native_period_three_share",
"native_phase_aware_strictly_beats_phase_blind_finite_orbits","no_universal_strict_score_gap")
class Tests(unittest.TestCase):
    def test_compiler_and_transitive_axioms(self):
        self.assertTrue(shutil.which("lake"),"Lean/Lake unavailable")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as d:
            f=pathlib.Path(d)/"Native.lean"
            f.write_text("import PermanssonResearch.ReverseSolver.NonlinearPolicyClassComparison\n"+
              "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"+
              "\n".join("#check "+s+"\n#print axioms "+s for s in NAMES)+"\n")
            p=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                            capture_output=True,text=True,timeout=600)
            out=p.stdout+p.stderr
            self.assertEqual(p.returncode,0,out)
            for n in NAMES:self.assertIn(n,out)
            for ax in re.findall(r"depends on axioms:\\s*\\[([^\\]]*)\\]",out):
                self.assertLessEqual({x.strip() for x in ax.split(",") if x.strip()},
                                    {"propext","Quot.sound","Classical.choice"},out)
            self.assertNotIn("sorryAx",out)
if __name__=="__main__":unittest.main()
