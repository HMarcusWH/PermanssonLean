# D0 — finite frozen-menu reverse-regime objective and optimizer

**Status:** D0-A (#39) and D0-B (#40) merged with recorded green Research Lean CI.
D0-C (#41) proves the finite-rational-matrix to canonical `finitePrefixLaw`
hitting-value correspondence at **every finite horizon**. Its research build,
transitive axiom audit and all four CI workflows passed on commit `22525678`.
The research result remains separate from frozen v0.1.8 Exact GR/PR and
does **not** certify any strategic-world intervention or Python implementation.

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
fixed-menu winner. PR #41 proves the canonical finite-prefix
correspondence for every certified rational matrix and finite horizon. A further
typed strategic-world matrix-factorization bridge remains necessary before the rational results certify strategic interventions. D1 later
extends to adaptive state-feedback policies using the correct P/U/α order.
This PR does not introduce any such adaptive-policy semantics.

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
finite-matrix-to-**canonical `finitePrefixLaw`** theorem. Typed
strategic-world kernel factorization and exact menu-value transfer are **still
required** before promoting this to an unconditional `FrozenMenu`
model-value optimum. The strict Python
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
