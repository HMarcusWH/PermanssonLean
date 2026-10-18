"""Source-bound actual signatures/axioms for through-horizon risk flags."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = "ThroughHorizonRiskAxiomAudit"
audit.SIGNATURES_BASENAME = "through_horizon_risk_signatures_axioms.txt"
audit.DEFAULT_OUTPUT = "research/paper_closures/through_horizon_risk_receipt.json"
audit.MODULES = ["ReverseSolver.ThroughHorizonRiskMonitor", "ReverseSolver.ThroughHorizonRiskFixture"]

if __name__ == "__main__":
    audit.main()
