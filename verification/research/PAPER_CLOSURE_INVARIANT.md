# Automatic first-moment invariant laws

This track implements the general A-INVARIANT constructor on a complete
separable metric space with its Borel measurable space. The kernel must be
Markov, preserve finite first moments about a fixed point, and satisfy the
original `IsW1Contraction K ρ` with `0 ≤ ρ < 1`. That original predicate still
quantifies over every probability law and every admissible real dual bound.

`FirstMomentKernel` defines the actual action `μ ↦ K ∘ₘ μ` on the first-moment
class. A concrete row-drift criterion derives moment preservation from
integrable row distances and the bound `∫ d(y,y₀) K(x,dy) ≤ a d(x,y₀)+b`.
The original global contraction gives a Lipschitz bound for this actual
kernel action in the separately constructed coupling-cost metric.

`FirstMomentInvariant` applies the pinned Banach fixed-point theorem to the
proved complete first-moment metric space. It constructs a probability law
that is invariant under the original kernel and unique within that class.
For every initial first-moment law, the actual recursively composed original
kernel laws satisfy `W₁(μ Kⁿ,π) ≤ ρⁿ W₁(μ,π)` and converge in that transport
metric. Neither invariance nor an invariant-law constructor is an input.

`GeneratedInvariantPerturbation` constructs the two invariant laws in the
original `ContractivePerturbation` object independently from the two kernels'
moment and contraction hypotheses. It derives the original finite-gap gate
from their first moments and proves the genuine coupling bound
`W₁(π,π̃) ≤ δ/(1−ρ)` from the original every-row dual defect.

All four dedicated modules compile with pinned Lean 4.34.0. The discovered
post-build integration test passed its 26-declaration transitive-axiom audit
in 73.752 seconds, allowing only `propext`, `Classical.choice` and `Quot.sound`.
The published receipt binds every source SHA256. The real-line reset-kernel
regression checks the inclusive `ρ=0` case, actual stationary law and
all-initial geometric bound. Uniqueness outside the first-moment class and
general occupation-property factorization or ergodic conclusions are separate
scope.
