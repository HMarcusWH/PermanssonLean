"""General first-moment KR construction and actual coupling-lift audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'A-KR-POLISH-first-moment'
audit.AUDIT_STEM = 'FirstMomentTransportAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_first_moment_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Probability/' + name + '.lean'
    for name in ['FirstMomentQuantization', 'FiniteLipschitzExtension',
                 'FinitePartitionMeasure', 'FinitePartitionCoupling',
                 'FirstMomentKantorovichDuality', 'FirstMomentTransportRegression']
]
audit.RESIDUAL = (
    'Original coupling-infimum/KR-test supremum identification for arbitrary probability '
    'laws with finite first moments on a separable Borel pseudometric space; in particular '
    'the usual first-moment Polish metric profile. Quantizers, bounded finite extensions, '
    'normalized restricted-cell product lifts, exact marginals and cost integrability '
    'are constructed. General optimal-coupling attainment and actual first-moment-space '
    'completeness are separate from this infimum-identification theorem.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
