# D1-C1: Rational nonstationary finite-prefix probability laws

**Status:** research-only PR #47, pending all Lean proofs and exact-head CI.
**Base:** D1-B PR #46, merged on main. D1-C2 typed strategic-world
transport remains a separate PR #48. Frozen v0.1.8 theory and release
evidence must not be changed.

## Process contract

For a finite rational control system and admissible deterministic
remaining-horizon Markov schedule pi, fix ORIGINAL deadline T.

At elapsed time i<T the selected row is

    K_i^(T,pi)(y,z) = (feedbackMatrix sys (pi (T-i))).entry y z.

The original deadline remains T when taking a shorter observed prefix.
The trajectory measures are made by Mathlib Kernel.partialTraj on the
time-indexed family of Markov history-extension kernels, not by declaring
a synthetic weighted-path functional to be a probability measure.

The actual t-transition prefix has coordinates 0..t and distribution
prefixLaw sys pi T x t. IsProbabilityMeasure is established for it.
Prefixes are projective WITHIN the same initial T. There is no
assumption that starting again with deadline t yields that prefix.

## Path atoms and exact rational arithmetic

The independent chronological product weight is

    prod_{i=0}^{t-1} K_i^(T,pi)(w_i,w_{i+1}).

The proof stack relates every actual path atom of partialTraj to the
previous prefix atom and a genuine selected one-step probability.
Induction establishes exact atom/product equality, with wrong initial
states assigned mass zero. Nonnegativity certifies exact rational to
ENNReal embedding. No floating-point approximation is permitted.

## Independent event-value proof

Use the EXISTING D0 successPrefixEvent, which counts goal at time zero
and any later goal reached strictly before earlier forbidden visits.
The target is value-terminal, but transition rows are NOT made absorbing.

The proof compares:
1. Actual first-hit event mass, reduced to the finite path-atom sum.
2. An exhaustive rational forward enumeration of all successor words.
3. The D1-B policyValue via a separate first-successor recursion.

Only AFTER all correspondences are proved can the rational Bellman
upper bound and attaining schedule be transported onto true
nonstationary path probabilities.

## Mandatory regression

The existing 3-state deadline example uses Probe on the first step when
T=2, and Gamble first when T=1. The respective first-step success
probabilities are 1/4 and 1/2; the two-step success probability is 5/8.
A Lean theorem must prove the first-step measures for different initial
deadlines differ, and prove legal within-deadline prefix restriction.

Also test time-zero initialization, initial goal/forbidden, empty goal,
nonempty unreachable goal, stationary reduction to D1-A and normalization.

## Scope / no overclaiming

This PR certifies the RATIONAL constructed finite controlled-process
probability law only. Do not claim the entire time-varying trajectory
equals an existing SINGLE frozen StrategicWorldModel.pathLaw. PR #48
must construct the typed alpha -> P -> U induced-kernel sequence and
prove a whole finite-path measure pushforward equality.

No general history-dependent reduction, randomized-policy optimality,
partial observation, arbitrary externally specified P/U, or empirical
efficacy is claimed.

## Reproduction / merge policy

Use pinned Lake/Mathlib toolchain. Build PermanssonResearch and the
original root. Require all four workflows green on the exact final
commit, all research imports and axiom audit passing, no new axioms or
proof placeholders, and review every actionable code finding.
