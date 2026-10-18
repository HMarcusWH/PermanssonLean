# Actual bounded pointwise ergodic theorem

The six modules listed by `paper_closure_birkhoff_audit.py` derive almost-everywhere
convergence of bounded measurable real orbit averages on an arbitrary probability
space under a measurable probability-preserving transformation. Neither
invertibility nor ergodicity is assumed. The limit equals conditional expectation
on the actual sigma-algebra of measurable sets satisfying `T⁻¹ s = s`.

`HopfMaximal` constructs finite positive maximal sums and proves their integrated
coboundary inequality. Dominated convergence gives the Hopf inequality when every
point has a positive forward partial sum. `BoundedOrbitAverages` proves actual
measurability, bounds and exact shift invariance of the upper average, using the
bounded endpoint defect. `BoundedBirkhoff` applies Hopf to the observable minus
its invariant upper average plus an arbitrary positive constant. Its integral
bound, and the corresponding bound for the negative observable, force the upper
and lower averages to agree almost everywhere.

`InvariantSigma` uses the pinned library's exact invariant sigma-algebra.
`BoundedBirkhoffConditional` restricts measure preservation to every invariant
measurable set, integrates the actual finite orbit averages, and uses dominated
convergence to identify their limit with the original conditional expectation.
Thus conditional expectation identification is derived rather than supplied as
an oracle.

The regressions retain distinct pointwise limits for the identity on two points
and apply the conditional-limit theorem to a genuinely noninjective reset map.
The first rejects a constant-limit conclusion without ergodicity; the second
checks the theorem does not require invertibility.

The source/signature/transitive-axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`. Stationary Markov shift preservation,
regular conditional random probabilities, weak empirical convergence and
absolute-continuity transfer are separate applications. This theorem covers
bounded observables; it does not claim an integrable-observable extension.
