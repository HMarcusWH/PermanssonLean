"""Actual original behavioral-policy information boundary and transitive axioms."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = 'InformationBoundaryAxiomAudit'
audit.SIGNATURES_BASENAME = 'information_boundary_signatures_axioms.txt'
audit.DEFAULT_OUTPUT = 'research/paper_closures/information_boundary_receipt.json'
audit.MODULES = ['StrategicWorld.InformationBoundary']

if __name__ == '__main__':
    audit.main()
