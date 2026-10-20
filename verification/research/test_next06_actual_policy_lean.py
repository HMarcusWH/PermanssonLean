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
            axiom_sets = re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out)
            self.assertGreaterEqual(len(axiom_sets), 1, "missing axiom audit records: "+out)
            for ax in axiom_sets:
                self.assertLessEqual({x.strip() for x in ax.split(",") if x.strip()},
                                    {"propext","Quot.sound","Classical.choice"},out)
            self.assertNotIn("sorryAx",out)
    def test_false_native_nonlinear_score_is_rejected(self):
        self.assertTrue(shutil.which("lake"),"Pinned Lean required")
        with tempfile.TemporaryDirectory(dir=ROOT/".lake") as d:
            f=pathlib.Path(d)/"FalseScore.lean"
            f.write_text("import PermanssonResearch.ReverseSolver.NonlinearPolicyClassComparison\n"+
             "open PermanssonResearch.ReverseSolver.NonlinearPeriodThree\n"+
             "example : booleanRationalScore (1/2) = (1:ℚ) := by\n"+
             "  exact classwise_barycenter_invalid.2\n")
            p=subprocess.run(["lake","env","lean",str(f)],cwd=ROOT,
                             capture_output=True,text=True,timeout=600)
            out=p.stdout+p.stderr
            self.assertNotEqual(p.returncode,0,"false nonlinear score accepted")
            self.assertFalse(re.search("unknown module|failed to import|parser error|"+
              "out of memory|timed out|maximum heartbeat",out,re.I),out)
            self.assertTrue("type mismatch" in out.lower() or
                            "unsolved goals" in out.lower(),out)

if __name__=="__main__":unittest.main()
