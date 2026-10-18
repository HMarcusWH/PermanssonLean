"""Actual first-moment metric completeness and countable gluing audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'A-COMPLETE-first-moment'
audit.AUDIT_STEM = 'FirstMomentCompletenessAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_completeness_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Probability/' + name + '.lean'
    for name in ['KRDualSeparation', 'GluedCouplingSequence', 'SummableStepLimit',
                 'FirstMomentMetric', 'SummableTransportLimit',
                 'FirstMomentCompleteness', 'FirstMomentCompletenessRegression']
]
audit.RESIDUAL = (
    'Actual coupling-cost-infimum metric and completeness of probability measures with '
    'finite first moments on a complete separable Borel metric space. Zero-distance '
    'separation, countable conditional-kernel gluing, prescribed coordinate and adjacent '
    'joint marginals, measurable almost-sure limits, first moments and transport tail '
    'bounds are proved. General optimal-coupling attainment and invariant-law/ergodic '
    'conclusions are separate theorems.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
