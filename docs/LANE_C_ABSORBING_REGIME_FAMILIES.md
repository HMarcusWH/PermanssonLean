# Lane C1 — finite absorbing-family and random occupation laws

**Research status:** Draft PR #52; proposed finite absorbing subclass of the
[research architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md#6-lane-c--multiple-limit-and-basin-family-semantics).
The core v0.1.8 `RegimeSpecification.target` remains a single frozen
probability measure and is **not modified** here.

## Mathematical separation

Let `Y` be finite, `K` a genuine Markov kernel and `A ⊆ Y` a nonempty
set of absorbing fixed points, i.e. `K(a) = δ_a` for every `a ∈ A`.
There are four different assertions that must never be conflated:

1. **Kernel absorption:** the actual Markov semigroup has a uniform
   `N ≥ 1`, `0 < ε ≤ 1` with `K^N(y,A) ≥ ε` for every transient `y`.
2. **Path-space geometric survival:** for canonical path law `P_y`,
   `P_y(τ_A > kN) ≤ (1-ε)^k`; derive with the conditional Markov property
   and an actual N-step bridge, not independent-block multiplication.
3. **Almost-sure trajectory convergence:** conditional on eventual absorption
   into some `H(w) ∈ A`, the original positive-horizon empirical occupation
   process converges in the **original weak topology** to `δ_{H(w)}`.
4. **Law of the limit:** `Law_y(δ_H)`, the pushforward of the random
   endpoint distribution by `a ↦ δ_a`; its barycenter
   `∑ P_y(H=a) δ_a` is not generally the pathwise random limit itself.

The finite four-state adversarial fixture in
`verification/research/test_lane_c.py` has states `t,u,a,b` and
`t→u=1`, `u→u=1/2`, `u→a=1/6`, `u→b=1/3`, and `a,b` fixed.
It has `N=2`, `ε=1/2` and absorption weights `1/3,2/3`.
This fixture is independent exact arithmetic and **does not substitute** for
the corresponding typed strategic model's formally verified induced kernel.

## Current research modules and exact scope

| Module | Explicit mathematical obligation | Status |
|---|---|---|
| `AbsorbingFamily` | finite typed Markov kernel, nonempty pointwise absorbing states, unique terminal destination | Source committed; Lean gate required |
| `AbsorptionTail` | geometric survival and limit zero from an **explicit per-block survival recurrence** | Conditional theorem; **missing stochastic-semigroup bridge** |
| `RandomLimit` | eventual constancy implies canonical weak empirical occupation convergence for the Boolean state space | Proof source committed; Lean gate required |
| `LimitLaws` | distribution of endpoint Dirac laws is the measurable probability pushforward, exact measurable-event weights | Proof source committed; Lean gate required |
| `Counterexamples` | no shared state-space Dirac limit for distinct fixed points; observational descriptor collapse | Proof source committed; Lean gate required |
| `DescriptorTransport` | pushforward terminal Dirac measure through an observed descriptor | Proof source committed; Lean gate required |
| `TypedStrategicWitness` | real stochastic α/P/U kernels for the branching four-state experiment | Construction only; **induced-kernel equality and a.s. absorption not yet proved** |
| `Recovery` | conservative original GR recovery given independent original GR gates and an actual path-law a.s. common absorbing target | Conditional original semantics; Lean gate required |

Do not promote PR #52 or describe C1 as end-to-end established until:
- a theorem derives per-block survival from the actual `K^N` bound with
  correct zero-time and horizon conventions;
- a theorem converts its geometric tail into canonical path-law a.s.
  absorption and a *measurable* random destination;
- the actual typed strategic witness induced kernel is verified to equal
  the exact finite transition matrix, not just analogically similar;
- all descriptor occupation and law-of-random-measure claims hold for the
  declared finite family and supported initial laws;
- source statements are checked for hidden circularity, are axiom audited,
  and the negative examples refute the stated stronger claims.

## Known necessary counterexamples

- **C1:** Two distinct absorbing states have distinct limiting state Dirac laws.
- **C2:** For transient `u`, `ν∞ = δ_a` or `δ_b`, with endpoint weights
  `1/3,2/3`; their weighted mixture is the expectation, not an a.s.
  trajectory limit.
- **C3:** The already-proved period-two model has convergent empirical
  occupation but oscillating time marginals; retain as regression control.
- **C4:** Infinite nonstationary alternation is outside the finite stationary
  assumptions; no general almost-sure claim is made.
- **C5:** A constant observed descriptor maps different absorbing states to
  the same observed Dirac measure.
- An overly broad ex-post target set is not an admissible frozen target.

## Frozen-source and release gates

1. Use the existing `PermanssonResearch` target, pinned Lean 4.34.0/mathlib.
2. Preserve frozen `PermanssonLean/`, `PermanssonLean.lean`, `paper/`,
   `application/`, toolchain, and historical artifacts.
3. Import every module directly from `PermanssonResearch.lean`.
4. Pass all four **final-head** CI workflows, independent rational tests,
   source placeholder scanner and transitive axiom audit.
5. Resolve the explicit open kernel-to-path-law bridging steps before claiming
   full C1 scientific completion.
6. Record substantive mathematical review and only then promote and merge.

**No unrestricted finite irreducible recurrent-class theorem is asserted.**
Periodicity, nonabsorbing class invariant distributions, empirical class
ergodicity and the complete Lane C decomposition are reserved for PR #53.
