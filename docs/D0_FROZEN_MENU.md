# D0 — finite frozen-menu reverse-regime objective and optimizer

**Status:** D0-A (#39), D0-B (#40), and D0-C (#41) are merged and
certified for finite rational matrices, with D0-C proving all-horizon
canonical `finitePrefixLaw` hitting-value equality. D0-D (#42) is merged:
it constructs an explicit typed strategic-world factorization for **every
certified finite rational matrix** in a deliberately chosen research family,
with unchanged P and U across its action-selection interventions.
D0-E (#43) develops the all-horizon transported typed-menu optimality theorem,
subject to final-head Lean/CI proof gates. Neither construction validates an
arbitrary supplied strategic-world model, the separate Python implementation,
or frozen v0.1.8 Exact GR/PR assertions.

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

**IMPORTANT:** D0-C now proves the *mathematical rational hitting recursion*
equals the canonical `finitePrefixLaw` event value for the genuine discrete
Markov kernel constructed from a certified rational matrix. This is **not**
a proof of correctness of the separate Python implementation, and does not
establish that its input tables are induced by `AdmissibleStrategicIntervention`
instances. Consequently, executable reports remain labeled
`EXACT_FINITE_MENU_CALCULATION`, not `PROVED_OPTIMUM` in the typed
strategic-world application sense. The Lean optimizer
separately proves existence/dominance of an exact mathematical argmax of
model-defined probabilities; it is noncomputable, not executable policy
extraction.

PR #40 formalized the finite hitting recursion, independent rational forward
enumeration, their equality, and computable selection of an exact rational
fixed-menu winner. PR #41 proves canonical finite-prefix correspondence for
every certified rational matrix and horizon. PR #42 supplies the distinct
**constructed finite strategic-world factorization**, not an identification
theorem for arbitrary typed models. PR #43 seeks to prove and apply the
all-horizon value transport for a complete frozen menu **in that constructed
family**, rather than injecting a pre-assumed `exact_values` field.
D1's adaptive state-feedback policies remain separate new theory.

## Release and proof firewall

All Lean files live beneath `PermanssonResearch/ReverseSolver/` and
are direct imports of `PermanssonResearch.lean`. The original core,
locked Lean/mathlib toolchain, frozen paper, application schemas,
claims and historical verification records must remain unchanged.

## D0-B implementation boundary (PR #40)

The new finite rational matrix evaluator has proof-carrying stochastic rows,
a computable Lean backwards hitting recursion, and a deterministic List.argmax
selection theorem over a fixed nonempty candidate list. This is a statement
about the **explicit exact rational matrices**. It is not, by itself, a proof
that any supplied matrix is a permitted intervention's induced kernel.

The rational weighted-suffix forward enumeration now has a Lean theorem
proving equality with the rational backward hitting recursion. D0-C supplies the distinct
finite-matrix-to-**canonical `finitePrefixLaw`** theorem. PR #42 supplies a concrete typed strategic-world factorization in a
special research family; PR #43 adds the corresponding exact all-horizon
menu-value transfer. A **general** factorization or value bridge for arbitrary
already supplied `FrozenMenu` objects is not established by either result. The strict Python
validator rejects floating-point, Boolean, string, NaN and infinity entries;
integers and `Fraction` entries are permitted as exact rationals.

## D0-B theorem inventory (PR #40)

Research-only, conditional on passing CI for the PR's exact head:

| Lean file | Mathematical role |
| --- | --- |
| `RationalKernel.lean` | Certified nonnegative rational transition rows summing to one; finite hitting recursion and `[0,1]` value bounds |
| `FiniteEvaluation.lean` | Finite successor-word enumeration with path-product weights; proof total mass is one; proof enumeration equals recursion for any finite rational matrix |
| `CertifiedSelection.lean` | Computable ordered-list argmax, membership, dominance and zero-optimum property, for a frozen complete list |
| `ValueCorrespondence.lean` | Conditional transfer of the computable index to `FrozenMenu`: full two-way coverage and **exact_values** field required; preserves original world primitive P |
| `CertificationExamples.lean` | Small rational one-step exact winner and arithmetic properties in Lean |

The theorem about a genuine typed strategic-world menu is **conditional on**
the explicit equality-of-values field. This field is not automatically derived
from rational entries or the separate `finitePrefixLaw`; treating it as an
unconditional formal bridge would overstate this PR. The Python report
rechecker independently re-enumerates exact paths, but is not verified as
software by Lean. The kernel realization/canonical law and eventual executable
checker should remain separate research work until proved.


## D0-C certified mathematical correspondence (PR #41)

The rational finite-state path evaluation and the canonical measure-theoretic
`ProbabilitySupport.finitePrefixLaw` are not definitionally equal. D0-C
proves their equality by building a genuine discrete probability kernel from
certified rational stochastic rows, proving its finite-prefix projectivity,
single-history transition-product weights, and exact target-before-forbidden
event semantics; then it bijectively reindexes histories indexed by
`Finset.Iic T` as their time-zero state plus precisely `T` successor
states. Histories starting at the wrong state have zero canonical mass.

The proof combines exact path-atom sum decomposition, the original D0-B
successor-word enumerator, the rational/ENNReal product bridge, and the
existing forward-enumeration-to-backward-recursion theorem. The unconditional
research theorem is:

```lean
rationalHittingValue_eq_canonical_all_horizons
```

For every `M : RationalMarkovMatrix n`, disjoint `target`, finite
horizon `T` and starting state `y : Fin n`, its statement is

```text
(rationalHittingValue M target T y : ℝ) =
  hittingValue (rationalTargetAsFrozen target)
    (rationalFiniteKernel M) y T
```

No `exact_values`, model-intervention or conditional correspondence
hypothesis is passed to this theorem. CI at `22525678` built the complete
research root, audited 438 research declarations with only `propext`,
`Classical.choice` and `Quot.sound` permitted, ran rational regressions,
and rejected proof placeholders and custom axiom declarations. This is an
exact *mathematical* theorem over the certified matrix model, not a proof
that the Python code implements it faithfully.

The Python fixed-menu implementation must additionally enforce one shared
state dimension, normalize finite target/forbidden iterables once per public
call, and reject forged result scope labels. No string such as
`PROVED_OPTIMUM` may be accepted by the independent report rechecker.

Even if D0-C proves finite rational/canonical correspondence, the claim is
about `K_M`, the kernel represented by the matrix `M`. It does **not**
by itself prove `K_M=K_(G,P)` for any original typed strategic-world
intervention. That requires a separately checked finite encoding,
kernel equality/intertwining and target/start transport. Do not promote
application status or claim proof of the Python implementation.


## D0-D typed finite strategic-world realization (PR #42)

PR #42, merged as `26934070f1d0498a5d77b5ca88504ef8eb7033f3`, formalizes
a concrete research family with
`S = Unit`, `X = Fin n`, and `A = Fin n`. The stochastic action
kernel chooses a rationally weighted next-world candidate, the fixed world
kernel P copies that action into X, and the fixed strategic update U
preserves trivial Unit memory. Every row-stochastic rational finite
matrix therefore has a **constructed** canonical typed factorization.

`FiniteStrategicRealization.inducedKernel_worldCylinder` and
`intervenedKernel_worldCylinder` identify the actual alpha → P → U
induced next-state distribution on **all measurable encoded world
events**, not merely one test atom. The action-selection intervention
`rationalStrategicIntervention` preserves exactly the baseline P and U.
The two-state witness gives distinct one-step goal probabilities 1/2 and 1.

The constructed `researchActionFamily` explicitly has permissive
research-only admissibility. These proofs do not infer admissibility for
external strategic games or reconstruct unknown structural P or U from
observations. One-step correspondence alone is insufficient to claim
equal full finite-prefix hitting values; that is D0-E's separate obligation.

## D0-E certified typed-menu optimality (PR #43)

**Mathematical implementation, gated on final-head CI verification.**
The new research-only modules are:

| Lean file | Purpose |
| --- | --- |
| `GenericFinitePrefixAtoms.lean` | Generic transition-pair and one-step atom recurrence for mathlib's real `finitePrefixLaw` |
| `FiniteStrategicPathBridge.lean` | Exact all-horizon atomic law/pushforward equality under the proven `Unit × Fin n ≃ Fin n` state encoding; goal/forbidden event transport; `typedHittingValue_eq_rational_all_horizons` |
| `TypedMenuCertification.lean` | Construct the finite typed menu with precisely the rational candidate-list membership and discharge `ExactMenuValueCorrespondence.exact_values` by proof |
| `TypedMenuCertificationExamples.lean` | Certify a nontrivial listed two-choice winner and genuine typed path-law values and fixed world/update |

The intended theorem `certifiedSelected_dominatesTyped` maximizes
the **actual canonical typed-model hitting probability**, for all
horizons, initial points and **members of the explicitly frozen finite
menu**. It is paired with `certifiedSelected_mem`,
`certifiedSelected_exactValue`, and world/update preservation.
List-order tie-breaking belongs to the original D0-B `List.argmax`
policy, and duplicate list indices do not enlarge the set of eligible
typed interventions. The original model baseline is present only if
listed. The original target/forbidden order includes time zero and does
not modify the underlying Markov transition kernel to be absorbing.

The construction does **not** establish optimality against all
conceivable admissible strategic interventions, arbitrary externally
furnished `StrategicWorldModel` instances, or D1 state-feedback
policies. Nor does a typed Lean certificate certify independently
executed Python code or empirical transition probabilities. Do not
promote application status beyond its original schema or claim that
an outcome conditional on a constructed kernel predicts the world.

No proofs in #43 may use `sorry`, `admit`, custom axioms or an
input `exact_values` hypothesis in place of the genuine path-law
transport. The frozen v0.1.8 kernel and mathlib toolchain are unchanged.
