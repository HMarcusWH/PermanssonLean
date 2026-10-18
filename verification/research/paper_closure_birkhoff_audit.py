"""Actual bounded pointwise ergodic theorem and conditional-limit audit."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = 'BoundedBirkhoffAxiomAudit'
audit.SIGNATURES_BASENAME = 'bounded_birkhoff_signatures_axioms.txt'
audit.DEFAULT_OUTPUT = 'research/paper_closures/bounded_birkhoff_receipt.json'
audit.MODULES = ['Probability.' + name for name in [
    'HopfMaximal', 'BoundedOrbitAverages', 'BoundedBirkhoff',
    'InvariantSigma', 'BoundedBirkhoffConditional', 'BoundedBirkhoffRegression',
]]

if __name__ == '__main__':
    audit.main()
