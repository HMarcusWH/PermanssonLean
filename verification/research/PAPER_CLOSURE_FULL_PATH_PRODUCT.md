# Q-DISCOUNT: whole-product-law TV from retained common mass

`DependentHistoryCommonMass` uses genuinely dependent history spaces `H n`.
The actual evolution starts from its declared initial law and extends by
`(mu_n ⊗ K_n).map Prod.snd`. Replacing each normalized kernel by a finite
subkernel dominated by both processes constructs a common evolution.
Its mass is at least `(1-epsilon0) * product_{t<n}(1-eta_t)`, and it is
dominated by both actual prefix laws. The common-submeasure inequality gives
the finite-prefix event-TV bound without assuming a recurrence for TV.

For summable defects, `FullPathProductTV` proves that the retained products
converge to the genuine infinite product. Each finite retained product
dominates that limit. Parent module `CylinderTotalVariation` approximates
each event in the sum of the two original probability measures by the ring
of finite-coordinate events, giving the whole-law bound
`TV(P,Q) <= 1-(1-epsilon0)*product_t(1-eta_t)`.

The full-law theorem retains literal equalities identifying each actual
finite-coordinate marginal with the declared dependent history evolution.
No stationarity, finite state space, topology, RN construction, or Markov
property of a projected observation process is assumed.

The regression source identifies the actual prefix laws of Boolean constant
paths with their dependent history evolutions. It checks zero initial/row
defects, the sharp unit initial mismatch despite identical row kernels,
and a summable sequence containing a unit row budget. A fixed positive
recurring defect is proved nonsummable, and its finite retained-mass budget
converges only to one. The theorem makes no exact-survival transfer claim.

All four sources, including the parent cylinder-extension module, compile
under pinned Lean 4.34.0. The discovered integration test passed, freshly
auditing all 43 named declarations and their transitive axioms against the
exact source hashes. The source-bound receipt permits only `propext`,
`Classical.choice`, and `Quot.sound`.
