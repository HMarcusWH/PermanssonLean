"""Source-bound actual signatures/axioms for standard-Borel all-time autonomy."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = "AutonomyAEAxiomAudit"
audit.SIGNATURES_BASENAME = "autonomy_ae_signatures_axioms.txt"
audit.DEFAULT_OUTPUT = "research/paper_closures/autonomy_ae_receipt.json"
audit.MODULES = [
    "Probability.StandardBorelKernelEquality",
    "MultiAgent.AutonomousMeasurableKey", "MultiAgent.AutonomousInputMarginal",
    "MultiAgent.AutonomousAEComparison", "MultiAgent.AutonomousMarginalLaw",
    "MultiAgent.AutonomousAETransport", "MultiAgent.AutonomousAEMechanisms",
    "MultiAgent.AutonomousAEContinuumFixture",
]

if __name__ == "__main__":
    audit.main()
