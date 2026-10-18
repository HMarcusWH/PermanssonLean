"""Source-bound signatures and transitive axioms for the actual hard-risk LP.

The shared auditor recompiles missing, stale or unbound module artifacts, checks
the pinned compiler, and rejects source/artifact changes during the audit.
"""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = 'RiskLPAxiomAudit'
audit.SIGNATURES_BASENAME = 'risk_lp_signatures_axioms.txt'
audit.DEFAULT_OUTPUT = 'research/paper_closures/risk_lp_receipt.json'
audit.MODULES = ['ReverseSolver.' + name for name in [
    'PolytopeActive', 'PolytopeRational', 'PolytopeCompleteness',
    'PolytopeOptimizer', 'PolytopeLinearProgram', 'PolytopeRegression',
    'FlowExpressions',
    'FiniteOccupancyModel', 'FiniteOccupancyHistory', 'FiniteOccupancyReconstruction',
    'FiniteOccupancyMarginals', 'FiniteOccupancyMonitor', 'FiniteOccupancyRiskFixture',
    'FlowPolytopeEncoding', 'FlowPolytope', 'FlowPolicyOptimality', 'FlowRiskWitness',
]]

if __name__ == '__main__':
    audit.main()
