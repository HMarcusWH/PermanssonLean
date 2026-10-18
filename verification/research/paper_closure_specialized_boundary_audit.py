"""Actual E-02/E-03 negative statements and their transitive axioms."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = 'SpecializedBoundaryAxiomAudit'
audit.SIGNATURES_BASENAME = 'specialized_boundary_signatures_axioms.txt'
audit.DEFAULT_OUTPUT = 'research/paper_closures/specialized_boundary_receipt.json'
audit.MODULES = ['Specialized.BoundaryWitnesses']

if __name__ == '__main__':
    audit.main()
