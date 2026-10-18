"""Constructed general first-moment invariant laws and original perturbation audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'A-INVARIANT-first-moment'
audit.AUDIT_STEM = 'FirstMomentInvariantAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_invariant_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Perturbation/' + name + '.lean'
    for name in ['FirstMomentKernel', 'FirstMomentInvariant',
                 'GeneratedInvariantPerturbation', 'FirstMomentInvariantRegression']
]
audit.RESIDUAL = (
    'Constructed unique first-moment invariant laws for Markov kernels on complete '
    'separable Borel metric spaces preserving first moments and satisfying the original '
    'global all-probability-law IsW1Contraction with 0 <= rho < 1. A row-drift criterion '
    'derives moment preservation; actual kernel iterates obey geometric coupling-W1 '
    'bounds and converge in the constructed transport metric. Both original '
    'ContractivePerturbation invariant laws are constructed independently under their '
    'two contraction/moment hypotheses. Non-first-moment invariant laws and general '
    'occupation-property factorization/ergodic bridges are separate scope.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
