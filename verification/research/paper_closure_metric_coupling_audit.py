"""Source-bound actual signatures/axioms for derived A3 metric certificates."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = "MetricCouplingAxiomAudit"
audit.SIGNATURES_BASENAME = "metric_coupling_signatures_axioms.txt"
audit.DEFAULT_OUTPUT = "research/paper_closures/metric_coupling_receipt.json"
audit.MODULES = [
    "Perturbation.DobrushinContraction", "Probability.FiniteRowCoupling",
    "Perturbation.FiniteSequentialCoupling", "Perturbation.FiniteTypedRows",
    "Perturbation.FinitePrimitiveMetric", "Perturbation.FiniteStateMetricContraction",
    "Perturbation.FiniteMetricProtocol", "Perturbation.FiniteMetricCouplingFixture",
]

if __name__ == "__main__":
    audit.main()
