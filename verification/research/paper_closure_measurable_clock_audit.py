"""Actual source/signature/axiom audit for arbitrary measurable Nat clocks."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = "MeasurableNatClockAxiomAudit"
audit.SIGNATURES_BASENAME = "measurable_nat_clock_signatures_axioms.txt"
audit.DEFAULT_OUTPUT = "research/paper_closures/measurable_nat_clock_receipt.json"
audit.MODULES = ["MultiAgent." + name for name in [
    "MeasurableNatPrivateClock", "MeasurableNatClockTransport", "MeasurableNatClockFixture",
]]

if __name__ == "__main__":
    audit.main()
