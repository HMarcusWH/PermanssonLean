"""Proof-level native recurrent-class and original occupation source receipts."""
import pathlib
import re
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
MOD = "PermanssonResearch.ReverseSolver.NonlinearPeriodThreeClassGeometry"
NS = "PermanssonResearch.ReverseSolver.NonlinearPeriodThree"
CLAIMS = (
    "reachedCycle_mem",
    "native_cycle_positive_edge",
    "reachedCycle_closed",
    "native_cycle_two_way_one",
    "native_cycle_two_way_two",
    "reachedCycle_eq_communicatingClass",
    "reachedCycle_recurrent",
    "native_phase_orbit_in_reachedCycle",
    "native_selected_communicatingClass",
    "native_actual_occupation_equals_reached_stationary",
    "phase_aware_invariant_weights",
    "phase_aware_invariant_physical_true_mass",
    "native_phase_aware_actual_true_mass",
)

def compile_lean(code):
    if not shutil.which("lake"):
        raise AssertionError("pinned Lean compiler required, never skip")
    with tempfile.TemporaryDirectory(dir=ROOT/".lake") as folder:
        file=pathlib.Path(folder)/"NativeClass.lean"
        file.write_text(f"import {MOD}\nopen {NS}\n"+code+"\n")
        p=subprocess.run(["lake","env","lean",str(file)],cwd=ROOT,
                         capture_output=True,text=True,timeout=900)
    return p.returncode,p.stdout+p.stderr

class NativeThreeCycleClassProof(unittest.TestCase):
    def test_real_native_class_source_signatures_and_axioms(self):
        rc,out=compile_lean("\n".join("#check "+n+"\n#print axioms "+n for n in CLAIMS))
        self.assertEqual(rc,0,out)
        for name in CLAIMS:self.assertIn(name,out)
        found=re.findall(r"depends on axioms:\s*\[([^\]]*)\]",out)
        self.assertTrue(found,out)
        for a in found:
            self.assertLessEqual({x.strip() for x in a.split(",") if x.strip()},
                                 {"propext","Classical.choice","Quot.sound"},out)

    def test_false_transition_arc_rejected_semantically(self):
        rc,out=compile_lean(
            "example : nextState phaseAwarePolicy (canonicalCycleState 0) = "
            "canonicalCycleState 2 := by\n"
            "  exact native_cycle_successor (0 : Phase)\n")
        self.assertNotEqual(rc,0,"false native phase transition accepted")
        self.assertNotRegex(out.lower(),
            r"unknown module|unknown identifier|parser error|failed to import|out of memory|timed out")
        self.assertRegex(out.lower(),r"type mismatch|unsolved goals|application type mismatch")

if __name__=="__main__":
    unittest.main()
