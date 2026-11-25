"""Pinned real compiler replay of literal receipts and theorem conclusions.

The audit inventory below is owned by the tests, never by the emitter.
"""
import re
import unittest
from test_approx_equilibrium import fixture, dominant, asymmetric, candidate
from verification.research.approx_equilibrium.lean_emit import (
    emit, emit_discounted, emit_kite, emit_transport_fixture)
from application_bridge_replay import compile_source, audited_axioms, assert_semantic_rejection

STATIC = "ApproxEquilibriumReplay."
KITE = "ApproxKiteReplay."
DISCOUNTED = "ApproxDiscountedReplay."
TRANSPORT = "ApproxTransportReplay."
BRIDGE = "PermanssonResearch.ApplicationBridge.EquilibriumReceipt."
EXAMPLES = "PermanssonResearch.ApproxEquilibrium.Examples."

STATIC_TARGETS = tuple(STATIC+n for n in (
    "checked", "checkedRow", "exactRow", "checkedColumn", "exactColumn", "actual"))
KITE_BEFORE = tuple(KITE+n for n in (
    "checkedBeforeRow", "exactBeforeRow", "checkedBeforeColumn", "exactBeforeColumn"))
KITE_CONVERTED = KITE_BEFORE + tuple(KITE+n for n in (
    "checked", "actual", "checkedAfterRow", "exactAfterRow", "checkedAfterColumn", "exactAfterColumn"))
KITE_OUTSIDE = KITE_BEFORE + (KITE+"outside",)
DISCOUNTED_TARGETS = tuple(DISCOUNTED+n for n in (
    "checked0", "outputs0", "actual0", "checked1", "outputs1", "actual1"))
X1_TARGETS = DISCOUNTED_TARGETS + (
    DISCOUNTED+"sourceTables", BRIDGE+"x1_reduced_actual_Q_first",
    BRIDGE+"x1_reduced_actual_Q_second")
TRANSPORT_TARGETS = tuple(TRANSPORT+n for n in (
    "literal_inputs", "actual_margin", "actual_bound", "numeric_bound")) + tuple(EXAMPLES+n for n in (
    "original_margin_transport", "transport_instance", "dominant_regret_action_error",
    "dominant_original_margin_transport", "both_budgets_necessary", "actual_survival",
    "forever_zero_zero", "forever_leak_zero", "forever_coordination_exit",
    "no_vanishing_regret_modulus", "dominant_discounted_exact", "trace_stateLaw_actual"))


def verify_emitted_inventory(code, expected):
    """Check emitted audit targets against an independent exact inventory."""
    ns=re.search(r"(?m)^namespace (\w+)$",code)
    if not ns:
        raise AssertionError("missing generated namespace")
    names=re.findall(r"(?m)^#print axioms ([A-Za-z0-9_.]+)$",code)
    observed=[name if "." in name else ns.group(1)+"."+name for name in names]
    if sorted(observed)!=sorted(expected) or len(observed)!=len(set(observed)):
        raise AssertionError("wrong required generated axiom inventory: "+repr(observed))
    # The local conclusions must actually be declared in the generated source,
    # not merely named in the audit inventory.
    local_prefix=ns.group(1)+"."
    for name in expected:
        if name.startswith(local_prefix):
            local=name[len(local_prefix):]
            if not re.search(r"(?m)^theorem "+re.escape(local)+r"\b",code):
                raise AssertionError("missing generated theorem: "+name)


class ExactEquilibriumLeanTests(unittest.TestCase):
    def replay(self,code,filename,expected):
        verify_emitted_inventory(code,expected)
        rc,log=compile_source(code,filename)
        self.assertEqual(rc,0,log[-10000:])
        self.assertNotIn("sorryAx",log)
        audited_axioms(log,list(expected))

    def test_AE_T46_static_conclusion(self):
        raw=fixture("matching")
        self.replay(emit(raw,candidate(raw)),"AEStatic.lean",STATIC_TARGETS)
        raw=dominant("1/4");raw["epsilon"]="1/5"
        self.replay(emit(raw,candidate(raw)),"AEAbove.lean",STATIC_TARGETS)

    def test_AE_T47_static_semantic_negative(self):
        raw=fixture("matching")
        code=emit(raw,candidate(raw),conclusions=False)
        self.replay(code,"AEStaticCheckOnly.lean",(STATIC+"checked",))
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
            self.replay(emit_kite(raw,candidate(raw)),"AEKite"+name+".lean",
                        KITE_OUTSIDE if name=="OUTSIDE" else KITE_CONVERTED)

    def test_x1_both_players_discounted_replay(self):
        raw=fixture("x1")
        self.replay(emit_discounted(raw,candidate(raw),x1_source=True),"AEX1.lean",X1_TARGETS)

    def test_asymmetric_discounted_conclusion_and_mutation(self):
        raw=asymmetric()
        self.replay(emit_discounted(raw,candidate(raw)),"AEAsymmetric.lean",DISCOUNTED_TARGETS)
        code=emit_discounted(raw,candidate(raw),conclusions=False)
        self.replay(code,"AEAsymmetricCheckOnly.lean",(DISCOUNTED+"checked0",DISCOUNTED+"checked1"))
        # The verified player-two residual is exactly 1. Change it to 0,
        # retaining well-formed definitions and all other proof obligations.
        old="theorem checked1 : checkDiscounted model1 (1 / 2 : ℚ) (1 / 1 : ℚ)"
        new="theorem checked1 : checkDiscounted model1 (1 / 2 : ℚ) (0 / 1 : ℚ)"
        self.assertEqual(code.count(old),1)
        assert_semantic_rejection(self,code,code.replace(old,new,1),"checked1","AEDiscountedMutation.lean")

    def test_AE_T48_sharp_original_transport(self):
        raw=fixture("transport")
        self.replay(emit_transport_fixture(raw,candidate(raw)),"AETransport.lean",TRANSPORT_TARGETS)

    def test_required_inventory_rejects_missing_conclusion(self):
        raw=fixture("matching")
        code=emit(raw,candidate(raw))
        verify_emitted_inventory(code,STATIC_TARGETS)
        # Simulate an emitter omitting the conclusion AND its own audit.
        mutant=re.sub(r"(?ms)^theorem actual\b.*?(?=\n\n#|\n\nend |\Z)","",code)
        mutant=mutant.replace("#print axioms actual\n","").replace("#print axioms actual","")
        self.assertNotEqual(code,mutant)
        with self.assertRaises(AssertionError):
            verify_emitted_inventory(mutant,STATIC_TARGETS)


if __name__=="__main__":unittest.main()
