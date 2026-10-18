# Regenerative first moments and literal empirical P1 limits

This extension treats homogeneous kernels on standard Borel state spaces
with an actual every-row decomposition `K = (1-r) seed + r R`, where
`0 <= r < 1`. Descriptors are measurable maps into a complete separable
Borel metric space and may be unbounded. The additional moment condition
is the finite expected absolute regenerative reward

`sum_n r^n integral |f| d(seed R^n) < infinity`.

The condition is stated as a nonnegative extended integral series, so an
infinite real integral cannot satisfy it through the default value of the
Bochner integral. Tonelli proves its equivalence with integrability under
the actual constructed geometric invariant law. For descriptors, `f` is
the distance to a fixed descriptor basepoint.

The proof first establishes integrable nonnegative time averages under
the genuine stationary canonical path law. A finite Hopf maximal inequality
gives an L1 approximation theorem; bounded truncations and dominated
convergence then extend the established bounded regenerative averages.
Stationarity is used only for that step. For arbitrary initial laws, a
constructed common state measure has mass `1-r^n`. The full shifted path
laws have total variation at most `r^n` from the stationary law. Measurable
shift-invariant good events therefore transfer to every initial law. The
time-average convergence event is proved shift invariant without assuming
that an unbounded observable has a bounded endpoint term.

Actual all-initial scalar averages are then proved for every nearest-center
quantization error and every finite quantization-cell indicator. A genuine
Kantorovich bound for finite quantizations converts these countably many
scalar laws into convergence of the literal positive-horizon empirical
probabilities in the first-moment Wasserstein metric. Uniform empirical
excess tails and distance-times-tail indicators are also derived over all
positive horizons; uniform integrability and Wasserstein convergence are
conclusions, not hypotheses.

The global occupation selector takes the actual P1 empirical limit when
one exists, and a fixed predeclared P1 fallback otherwise. It is strongly
measurable and its probability projection is measurable for the Borel
sigma algebra of the original weak probability topology. The selector,
descriptor, fallback and bounded continuous functional are fixed
independently of all compared kernels. The resulting original full-path
property factors for all four actual typed baseline and intervention
processes, at every starting state. The full original constitutive-margin
theorem retains the global dual-Lipschitz functional predicate, the shared
full comparison set, both baseline contraction bounds and every-row
defects. Primitive state reward budgets derive the first moments needed
for its finite-gap gate.

The real-state reset-and-increment regression resets to zero with
probability one half and otherwise increments the current state. Its
invariant law has positive atoms arbitrarily far away, while its identity
descriptor satisfies the regenerative moment condition. The regression
uses the actual canonical path law for every initial probability, with
no finite-state, compact-state or compact-support simplification.

The selector identifies actual P1 empirical limits. It does not claim to
identify a merely weak limit when empirical first moments fail to
converge. This restriction is explicit and is sufficient for the selected
regenerative profile with the stated moment condition.

All nineteen sources compile under pinned Lean 4.34.0. The discovered
integration test passed in 42.035 seconds and freshly audited all 113 named
declarations, permitting only `propext`, `Classical.choice` and `Quot.sound`.
The source-bound receipt is
`paper_closure_regenerative_moment_receipt_2026-10-18.json`.
