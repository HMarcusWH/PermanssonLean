# NEXT-04.1 canonical source bridge — wave 1

**Pinned original main:** `3931e4dccafb47b3cdf70177c0cf337102c90731`.
This additive work imports the genuine original typed
`StrategicWorldModel.pathLaw` and the current kernel-evolution,
finite-history and Markov-marginal providers. It proves the canonical
time-n marginal equals the actual `DependentHistory.evolution` from the
same initial measure and the actual `M.inducedKernel`, for every n.
`canonical_point_start_zero` makes point-initialization explicit.

The older `DiscountedProjectedOutputs.lean` remains untouched. It provides
a conditional discounted output theorem but has explicit `hP/hQ`
hypotheses; wave 2 must instantiate those for the actual baseline and
intervention separately, construct original *whole-path*
`RegimePropertyMap` outputs, pull back through the unchanged full
`B₁` domain, and apply original `constitutiveMargin_perturbation_abs_le`.

These wave-1 lemmas do **not** imply full original-margin transport,
strict positivity, Exact GR/PR preservation, empirical accuracy or
independent review. The original target compares point-start laws:
initial mismatch is zero there; a distinct more-general initial-law
bound must retain `epsilon` when the initial distributions differ.
