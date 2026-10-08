# D0 — finite frozen-menu reverse-regime objective and optimizer

**Status:** D0-A (#39) and D0-B (#40) merged with recorded green Research Lean CI.
D0-C (#41) is an in-progress research draft; its canonical finite-prefix
correspondence is **not certified** until the exact PR head passes independent Lean CI.
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

PR #40 formalized the finite hitting recursion, independent rational forward
enumeration, their equality, and computable selection of an exact rational
fixed-menu winner. PR #41 separately targets canonical finite-prefix
correspondence. A further typed strategic-world matrix-factorization bridge
remains necessary before the rational results certify strategic interventions. D1 later
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
proving equality with the rational backward hitting recursion. A distinct
finite-matrix-to-**canonical `finitePrefixLaw`** theorem and typed kernel
factorization are still required before promoting this to an unconditional
`FrozenMenu` model-value optimum. The strict Python
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


## D0-C implementation and representation boundary (PR #41 draft)

The rational finite-state path evaluation and the canonical measure-theoretic
`ProbabilitySupport.finitePrefixLaw` are not definitional equals. A proof
must explicitly identify histories indexed by `Finset.Iic T` with the
initial state plus `T` successor states, and identify their event semantics
and exact path weights. The construction of a row-stochastic matrix as a
discrete Markov kernel is a separate first obligation.

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
