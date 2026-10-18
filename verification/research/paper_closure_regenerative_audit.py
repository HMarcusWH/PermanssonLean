"""Constructed nonfinite regenerative averages and original property bridge audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'A-FACTOR-REGEN'
audit.AUDIT_STEM = 'RegenerativeFactorizationAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_regenerative_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Probability/RegenerativeOperator.lean',
    'PermanssonResearch/Probability/RegenerativeMeasure.lean',
    'PermanssonResearch/Probability/RegenerativePoisson.lean',
    'PermanssonResearch/MultipleLimit/RegenerativeAverages.lean',
    'PermanssonResearch/MultipleLimit/RegenerativeWeakEmpirical.lean',
    'PermanssonResearch/Perturbation/RegenerativeData.lean',
    'PermanssonResearch/Perturbation/RegenerativeOccupationProperty.lean',
    'PermanssonResearch/Perturbation/RegenerativeCompactOccupation.lean',
    'PermanssonResearch/Perturbation/RegenerativeOccupationFactorization.lean',
    'PermanssonResearch/Perturbation/RegenerativeCompactFactorization.lean',
    'PermanssonResearch/Probability/RegenerativeRegression.lean',
]
audit.RESIDUAL = (
    'Genuine nonfinite regenerative profile K = epsilon*seed + (1-epsilon)*R, '
    '0 < epsilon <= 1. The explicit geometric probability/invariance, bounded '
    'resolvent/Poisson solution, all-initial canonical bounded measurable averages '
    'and noncompact weak empirical convergence are proved. A predeclared numeric '
    'functional limit with default Phi(fallback) yields all four original typed '
    'path-law factorizations; compact descriptors additionally have a literal '
    'measurable probability-valued limit and fallback. The original full comparison '
    'sets/global dual-Lipschitz predicate and baseline contractions are retained '
    'in the generated original margin theorem; first moments of the constructed '
    'geometric laws explicitly discharge its finite-gap gate. A general global '
    'probability-valued weak-limit selector and unbounded-descriptor empirical-W1 '
    'tail/moment extension are separate scope.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
