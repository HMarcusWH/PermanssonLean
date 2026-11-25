"""Pinned real compiler replay of literal receipts and theorem conclusions."""
import re
import unittest
from test_approx_equilibrium import fixture, dominant, asymmetric, candidate
from verification.research.approx_equilibrium.lean_emit import (
    emit, emit_discounted, emit_kite, emit_transport_fixture)
from application_bridge_replay import compile_source, audited_axioms, assert_semantic_rejection

def expected_axioms(code):
    namespace=re.search(r"(?m)^namespace (\w+)$",code).group(1)
    names=re.findall(r"(?m)^#print axioms ([A-Za-z0-9_.]+)$",code)
    return [name if "." in name else namespace+"."+name for name in names]

class ExactEquilibriumLeanTests(unittest.TestCase):
    def replay(self,code,filename):
        rc,log=compile_source(code,filename)
        self.assertEqual(rc,0,log[-10000:])
        self.assertNotIn("sorryAx",log)
        audited_axioms(log,expected_axioms(code))

    def test_AE_T46_static_conclusion(self):
        raw=fixture("matching")
        self.replay(emit(raw,candidate(raw)),"AEStatic.lean")
        raw=dominant("1/4");raw["epsilon"]="1/5"
        self.replay(emit(raw,candidate(raw)),"AEAbove.lean")

    def test_AE_T47_static_semantic_negative(self):
        raw=fixture("matching")
        code=emit(raw,candidate(raw),conclusions=False)
        self.replay(code,"AEStaticCheckOnly.lean")
        mutant=code.replace("= true := by","= false := by",1)
        assert_semantic_rejection(self,code,mutant,"checked","AEMutation.lean")

    def test_kite_exact_conversion(self):
        for name in ("ROW","COLUMN","UNCHANGED","OUTSIDE"):
            if name=="ROW":
                raw=fixture("kite")
            elif name=="COLUMN":
                raw=fixture("kite");raw.update(R=[["0","0"],["0","0"]],
                    C=[["1","0"],["1","0"]],x=["1","0"],y=["3/4","1/4"])
            elif name=="UNCHANGED":
                raw=fixture("matching");raw.update(kind="kite",epsilon="1/5")
            else:
                raw=fixture("kite");raw["x"]=["1/2","1/2"]
            self.replay(emit_kite(raw,candidate(raw)),"AEKite"+name+".lean")

    def test_x1_both_players_discounted_replay(self):
        raw=fixture("x1")
        self.replay(emit_discounted(raw,candidate(raw),x1_source=True),"AEX1.lean")

    def test_asymmetric_discounted_conclusion_and_mutation(self):
        raw=asymmetric()
        self.replay(emit_discounted(raw,candidate(raw)),"AEAsymmetric.lean")
        code=emit_discounted(raw,candidate(raw),conclusions=False)
        self.replay(code,"AEAsymmetricCheckOnly.lean")
        # The verified player-two residual is exactly 1. Change it to 0,
        # retaining well-formed definitions and all other proof obligations.
        old="theorem checked1 : checkDiscounted model1 (1 / 2 : ℚ) (1 / 1 : ℚ)"
        new="theorem checked1 : checkDiscounted model1 (1 / 2 : ℚ) (0 / 1 : ℚ)"
        self.assertEqual(code.count(old),1)
        assert_semantic_rejection(self,code,code.replace(old,new,1),"checked1","AEDiscountedMutation.lean")

    def test_AE_T48_sharp_original_transport(self):
        raw=fixture("transport")
        self.replay(emit_transport_fixture(raw,candidate(raw)),"AETransport.lean")

if __name__=="__main__":unittest.main()
