"""Finite reverse KR and genuine coupling identification axiom/source audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'A3-K01-finite'
audit.AUDIT_STEM = 'FiniteTransportAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_finite_transport_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Probability/' + name + '.lean'
    for name in ['FiniteTransportSeparation', 'FiniteKantorovichDuality',
                 'FiniteTransportRegression']
]
audit.RESIDUAL = (
    'Genuine finite-state KR identification on the given pseudometric, with measurable '
    'singletons and arbitrary probability laws. The transport plan, exact marginals and '
    'optimality are constructed; no transport duality or optimal-plan premise is used. '
    'General Polish transport duality, Wasserstein completion and nonfinite regeneration '
    'remain outside this finite theorem.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
