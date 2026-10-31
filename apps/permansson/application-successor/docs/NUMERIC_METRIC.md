# Finite metric contraction and invariant-law perturbation — numerical profile v1

**Source:** `PermanssonResearch/Perturbation/DirectDualContraction.lean`
(`isW1Contraction_of_test_images`), `ContractiveOccupation.lean`
(`ContractivePerturbation`, `invariantLaw_wasserstein_le`) and
`Probability/KantorovichDual.lean` (`W1DualLE`). The numeric profile is a
bounded exact-rational implementation; its Lean correspondence for bounded
reflected instances is described in [`METRIC_LEAN_BRIDGE.md`](METRIC_LEAN_BRIDGE.md).
Application output reports `lean_status=NOT_EXECUTED`.

## Input and computed objects

Run `permansson-app finite-metric <input.json> --output <new-directory>`. The
input supplies a baseline and a perturbed typed `α/P/U` model on the same joint
states (the perturbation may change any primitive, including P) and a positive
distance for every unordered pair of distinct joint states; the triangle
inequality is checked. At most four joint states.

For the α/P/U-induced joint kernels `K` (baseline) and `K̃` (perturbed) the
profile computes, exactly:

1. `W1(K_x, K_y)` for every pair of baseline rows, each with an optimal
   coupling and a 1-Lipschitz potential attaining the same value, and the
   contraction factor `ρ = max_{x≠y} W1(K_x, K_y) / d(x, y)` with the pairs
   attaining it;
2. the row defects `δ_y = W1(K_y, K̃_y)` with certificates and `δ = max_y δ_y`;
3. the unique invariant laws `π` of `K` and `π̃` of `K̃` (a kernel with several
   invariant laws is refused) and `W1(π, π̃)` with its certificate;
4. only when `ρ < 1`, the A3 bound `W1(π, π̃) ≤ δ / (1 − ρ)`.

A coupling alone only bounds a distance from above; every reported distance
also carries a dual potential attaining it.

## Independent check and limits

`receipts.metric.check_metric` does not import the producer: it rebuilds both
kernels from direct α/P/U events and validates every certificate (coupling
marginals, cost equal to the stated distance, Lipschitz potential attaining
it), the maxima, both invariant laws (stochastic, invariant, unique) and the
bound. Optimal couplings are not unique, so certificates are validated rather
than recomputed.

Not provided: Polish-space moment and invariance arguments, occupation-margin
transport, a contraction claim for the perturbed kernel, an empirically
identified metric, independent certification or release acceptance.
