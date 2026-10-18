# Finite transport identification

This additive track proves the finite part of A3-K01 on the original metric and
the original `IsKRTest`/`W1DualLE` interfaces. The state space is finite, its
singleton sets are measurable, and the two laws are probability measures. The
metric may be a pseudometric. We do not impose a common supremum-norm bound on
the one-Lipschitz tests.

`FiniteTransportSeparation` constructs the set of row sums, column sums and
costs of all finite joint probabilities. Its image is compact and convex;
adding the nonnegative vertical cost ray gives a closed convex epigraph. A
separating functional for an infeasible proposed cost bound has a strictly
positive cost coefficient, because a product plan is feasible. Normalizing
the separating functional gives actual feasible transport dual potentials
whose objective exceeds the proposed bound.

`FiniteKantorovichDuality` takes the finite infimum of distance minus the
second potential. The triangle inequality makes this function one-Lipschitz;
it dominates the first potential and its negative dominates the second.
Consequently the original dual bound precludes such a separating functional.
The resulting real joint probability is converted to an actual measure, and
both marginal identities are proved exactly.

The exported conclusions identify every original dual bound with the bound
on the infimum of actual integrable coupling costs, prove that this infimum
equals the supremum of the original absolute integral differences, and
construct a coupling attaining the infimum. No optimal plan or transport
duality statement is a premise.

The finite theorem does not assert general Polish transport duality,
completion of the unrestricted Wasserstein space, or a nonfinite coupling
construction. Those remain separate from this finite result. Existing
finite occupation-factorization receipts retain their original scope.

Validation: all three modules compile with the pinned Lean 4.34.0 compiler.
The discovered post-build audit passes all 39 named declarations, checks every
transitive axiom against `propext`, `Classical.choice` and `Quot.sound`, and binds
the result to each source SHA256. Regressions include exact Dirac transport,
equal-law zero, and distance-three transport rejecting a bound of two.
