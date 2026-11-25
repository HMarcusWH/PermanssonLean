"""Real pinned-Lean static receipt replay, no mock compiler and no skip."""
import unittest
from test_approx_equilibrium import fixture, dominant, candidate
from verification.research.approx_equilibrium.lean_emit import emit, emit_discounted
from application_bridge_replay import compile_source, audited_axioms, assert_semantic_rejection

class ExactEquilibriumLeanTests(unittest.TestCase):
    def test_static_replay_and_semantic_negative(self):
        raw=fixture("matching"); code=emit(raw,candidate(raw))
        rc,log=compile_source(code,"AEStatic.lean")
        self.assertEqual(rc,0,log[-6000:])
        audited_axioms(log,["ApproxEquilibriumReplay.checked"])
        # Flip only the checked theorem, not the definitions or imports.
        mutant=code.replace("= true := by","= false := by")
        # Separate the axiom print from the theorem for the source-anchored harness.
        assert_semantic_rejection(self,code,mutant,"checked","AEMutation.lean")
    def test_above_threshold_replay(self):
        raw=dominant("1/4");raw["epsilon"]="1/5"
        code=emit(raw,candidate(raw));rc,log=compile_source(code,"AEAbove.lean")
        self.assertEqual(rc,0,log[-6000:])
        audited_axioms(log,["ApproxEquilibriumReplay.checked"])

    def test_x1_both_players_discounted_replay(self):
        raw=fixture("x1");code=emit_discounted(raw,candidate(raw))
        rc,log=compile_source(code,"AEDiscounted.lean")
        self.assertEqual(rc,0,log[-6000:])
        audited_axioms(log,["ApproxDiscountedReplay.checked0","ApproxDiscountedReplay.checked1"])
        # Alter only the claimed continuation value; the zero-residual theorem must fail.
        mutant=code.replace("value := ![(-121 / 211 : ℚ), (-81 / 211 : ℚ)]",
                            "value := ![(0 / 1 : ℚ), (-81 / 211 : ℚ)]",1)
        assert_semantic_rejection(self,code,mutant,"checked0","AEDiscountedMutation.lean")

if __name__=="__main__":unittest.main()
