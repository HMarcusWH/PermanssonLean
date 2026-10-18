"""Q-DISCOUNT actual dependent-history common-mass/product-law audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'Q-DISCOUNT-FULL-PRODUCT'
audit.AUDIT_STEM = 'FullPathProductAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_full_path_product_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Probability/CylinderTotalVariation.lean',
    'PermanssonResearch/Probability/DependentHistoryCommonMass.lean',
    'PermanssonResearch/Probability/FullPathProductTV.lean',
    'PermanssonResearch/Probability/FullPathProductRegression.lean',
]
audit.RESIDUAL = (
    'Actual dependent history spaces H n, normalized time-varying kernels, '
    'and a finite common subkernel construct a common evolution dominated '
    'by both original evolutions. Its mass is bounded below by initial common '
    'mass times the finite retained product; no TV recurrence is assumed. '
    'Summable defects yield the genuine infinite product, and generating-ring '
    'event approximation extends the resulting prefix bound to the actual '
    'whole product laws. Literal equalities identifying their finite-coordinate '
    'marginals with the declared dependent evolutions remain explicit. Initial '
    'mismatch and zero/unit-defect boundaries are retained. A fixed positive '
    'recurring leak is not summable and its retained-mass budget tends only '
    'to one; no exact infinite-survival transfer is asserted.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
