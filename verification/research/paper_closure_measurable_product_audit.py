"""Source-bound finite-index products with arbitrary measurable coordinates."""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = 'MeasurableProductAxiomAudit'
audit.SIGNATURES_BASENAME = 'measurable_product_signatures_axioms.txt'
audit.DEFAULT_OUTPUT = 'research/paper_closures/measurable_product_receipt.json'
audit.MODULES = ['MultiAgent.' + name for name in [
    'MeasurableFiniteProduct', 'MeasurableProductProtocols', 'MeasurableProductRegression',
]]

if __name__ == '__main__':
    audit.main()
