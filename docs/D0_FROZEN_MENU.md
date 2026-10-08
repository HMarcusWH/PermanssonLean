# D0 — finite frozen-menu reverse-regime objective and optimizer

**Status:** PR #39 research candidate. Formal declarations are not certified
until the exact head commit passes Research Lean and the transitive axiom audit.
Not part of frozen v0.1.8 Exact GR/PR or any application certification.

## Scientific contract

D0 freezes an indexed **finite nonempty menu** of already-typed
`AdmissibleStrategicIntervention F` instances attached to one
`StrategicWorldModel M`. Each candidate is a single **stationary
intervention held fixed over all T transitions**. Its kernel is the actual
`candidate.intervention.apply.inducedKernel` and its world primitive P is
unchanged by the typed strategic-intervention proof.

The frozen `FrozenHittingTarget` has measurable target G and forbidden D,
and an explicit `Disjoint G D` witness. `successPrefixEvent target T`
is the measurable length-(T+1) path event that there is some `t≤T` in G
with **no visit to D at any earlier time**. Initial membership counts.
Entering D before G is terminal for *value evaluation*, not an assertion
that the original world kernel absorbs at D.

For an initial joint state `y`, the exact model-defined probability is

```
v_i(y) = finitePrefixLaw K_i y T (successPrefixEvent target T)
K_i = (menu.choice i).intervention.apply.inducedKernel.
```

`optimalMember` is a noncomputably selected exact argmax of all values
on `menu.indices`. Its theorem proves the selected index belongs to the
menu and weakly dominates **every menu member**, not all conceivable
interventions or adaptive policies. A zero optimum gives zero success
probability for *every member of that same complete menu*. It does not
prove literal pathwise impossibility or claim anything about unlisted
interventions, strategies or the unknown true world model.

## Exact finite executable evaluation

`verification/research/d0_finite_solver.py` evaluates rational finite
transition tables. It has independent path-enumeration and backward
finite-hitting recursion functions and enumerates all named entries in
a user-supplied menu. `test_d0_frozen_menu.py` compares these two
calculations for multiple states/horizons and checks target/forbidden
precedence, initial membership, unreachable frozen menus, tie-breaking,
horizon-dependent optima, invalid rows and the sampling false-negative
counterexample.

**IMPORTANT:** The executable solver is not presently accompanied by a
Lean theorem equating *its recursive implementation* with the abstract
`finitePrefixLaw` event value or proving that arbitrary provided numeric
matrices arise from the `AdmissibleStrategicIntervention` interface.
Consequently, the result is labeled `EXACT_FINITE_MENU_CALCULATION`,
not `PROVED_OPTIMUM` in the formal application sense. The Lean optimizer
separately proves existence/dominance of an exact mathematical argmax of
model-defined probabilities; it is noncomputable, not executable policy
extraction.

The D0-B follow-up should formalize a finite hitting recursion and its
forward-law equality, then prove executable selection for exact rational
models and a typed matrix-factorization bridge where needed. D1 later
extends to adaptive state-feedback policies using the correct P/U/α order.
This PR does not introduce any such adaptive-policy semantics.

## Release and proof firewall

All Lean files live beneath `PermanssonResearch/ReverseSolver/` and
are direct imports of `PermanssonResearch.lean`. The original core,
locked Lean/mathlib toolchain, frozen paper, application schemas,
claims and historical verification records must remain unchanged.
