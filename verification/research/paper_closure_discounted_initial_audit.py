"""Source-bound normalized discount budget including initial mismatch."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = 'DiscountedInitialAxiomAudit'
audit.SIGNATURES_BASENAME = 'discounted_initial_signatures_axioms.txt'
audit.DEFAULT_OUTPUT = 'research/paper_closures/discounted_initial_receipt.json'
audit.MODULES = ['Probability.DiscountedInitialBudget']

if __name__ == '__main__':
    audit.main()
