"""Finite A3 constructor and actual occupation-factorization axiom audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'A3-I01-finite/A3-F01-finite'
audit.AUDIT_STEM = 'FiniteOccupationAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_finite_occupation_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Perturbation/' + name + '.lean'
    for name in ['FiniteInvariantConstructor', 'FiniteOccupationProperty',
                 'FiniteOccupationFactorization']
]
audit.RESIDUAL = (
    'Finite actual metric spaces only. The invariant-constructor contraction and geometric '
    'bound use the original W1DualLE predicate; this does not itself identify coupling W1 '
    'with that predicate. The generated four-factorization margin theorem covers the '
    'explicit continuous occupation-limit functional property subclass and requires one '
    'actual recurrent class for each of the four kernels. It makes no factorization claim '
    'for survival, time-zero or arbitrary frozen properties. General Polish transport '
    'duality, completeness and nonfinite regeneration are separate obligations.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
