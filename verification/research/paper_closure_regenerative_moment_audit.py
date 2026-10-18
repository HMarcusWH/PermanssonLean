"""Audit actual regenerative L1 averages, empirical P1 and original margins."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'A-FACTOR-REGEN-MOMENT'
audit.AUDIT_STEM = 'RegenerativeMomentAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_regenerative_moment_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/Probability/L1Maximal.lean',
    'PermanssonResearch/Probability/L1AverageApproximation.lean',
    'PermanssonResearch/Probability/L1Truncation.lean',
    'PermanssonResearch/Probability/FirstMomentEmpirical.lean',
    'PermanssonResearch/Probability/FirstMomentTopology.lean',
    'PermanssonResearch/Perturbation/FirstMomentOccupationProperty.lean',
    'PermanssonResearch/Probability/FiniteQuantizationBound.lean',
    'PermanssonResearch/Probability/FirstMomentEmpiricalConvergence.lean',
    'PermanssonResearch/Probability/RegenerativeRenewalMass.lean',
    'PermanssonResearch/MultipleLimit/CanonicalShiftLaw.lean',
    'PermanssonResearch/Probability/RegenerativeMomentCondition.lean',
    'PermanssonResearch/Probability/CesaroShiftInvariant.lean',
    'PermanssonResearch/MultipleLimit/RegenerativeInitialTransfer.lean',
    'PermanssonResearch/MultipleLimit/RegenerativeIntegrableAverages.lean',
    'PermanssonResearch/MultipleLimit/RegenerativeDescriptorMoments.lean',
    'PermanssonResearch/MultipleLimit/RegenerativeDescriptorTails.lean',
    'PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean',
    'PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean',
    'PermanssonResearch/Probability/RegenerativeMomentRegression.lean',
]
audit.RESIDUAL = (
    'Genuine homogeneous nonfinite regenerative kernels with 0 <= r < 1, '
    'measurable descriptors into a complete separable Borel metric space, and '
    'an explicit finite expected absolute regenerative descriptor reward. '
    'The geometric invariant descriptor law has a derived first moment; '
    'all-initial integrable nonnegative averages, uniform empirical excess-tail '
    'control, and actual empirical W1 convergence are proved, rather than '
    'assumed. The global kernel-independent P1 occupation limit/fallback selector '
    'is strongly measurable and its projection is weak-Borel measurable. It '
    'agrees with every actual P1 empirical limit; no claim is made for a '
    'merely weak limit whose first moments do not converge. The original four '
    'typed path-law factorizations and full constitutive-margin comparison '
    'retain the global original dual-Lipschitz functional predicate, shared '
    'full comparison set, baseline contractions and every-row defects. '
    'State first moments are derived from explicit state reward budgets. '
    'The real reset-and-increment regression has an unbounded identity '
    'descriptor and positive invariant atoms arbitrarily far away.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
