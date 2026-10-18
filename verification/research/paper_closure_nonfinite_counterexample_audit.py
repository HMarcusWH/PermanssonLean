"""C-01 genuine homogeneous countable-state countermodel audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'C-01'
audit.AUDIT_STEM = 'NonfiniteCounterexampleAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_nonfinite_counterexample_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/MultipleLimit/NonfiniteClock.lean',
    'PermanssonResearch/MultipleLimit/GrowingBlockAverages.lean',
    'PermanssonResearch/MultipleLimit/GrowingBlockCounterexample.lean',
]
audit.RESIDUAL = (
    'Two explicit nonfinite falsifiers on the actual homogeneous Nat-successor '
    'Markov chain, initialized at zero. Its original canonical trajectory law '
    'is proved equal to the Dirac law of the clock. Every singleton empirical '
    'mass tends to zero, ruling out every probability-valued weak limit. A '
    'fixed two-point descriptor with factorial growing blocks has average '
    'endpoint limits zero and one on even/odd blocks, so its actual canonical '
    'empirical averages and descriptor probability laws do not converge. '
    'These are countermodels to unrestricted nonfinite occupation assertions, '
    'not countermodels to the separately proved regenerative or stationary/AC '
    'profiles with their explicit hypotheses.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())
