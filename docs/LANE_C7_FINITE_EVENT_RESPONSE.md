# C7 — finite eventually-true observed-event constitution

**Status:** PROPOSED / source elaboration and adversarial verification pending.
**Base:** `main@b6e91f9badce1a2292a0ef6f1be8d7922c167cdf`, merged PR #57.
**Boundary:** research-only; frozen Permansson v0.1.8 source, old lanes,
applications, release hashes and pinned toolchain remain unchanged.

## Frozen target

For a finite nonempty genuine Markov state space Y, Boolean observation h
and fixed infinite-path event E_h = {w : eventually h(w n)=true}, prove
a canonical-almost-sure equivalence between E_h and selection of a recurrent
class all of whose members have Boolean label true. Consequently:

```text
P_mu^K(E_h) = sum_{i in goodRepresentatives(K,h)} P_mu^K(selector_K=i)
```

Never equate eventual constancy and occupation-law convergence for
arbitrary paths. Mixed-label periodic classes are bad despite genuine
occupation convergence. Intervened models use their OWN class selector.

For genuine typed baseline and admissible strategic intervention J with
fixed world P, prove the exact original real property response and an
attained finite comparison-set margin. Finally prove the original
unweakened `IsUniformGeneralizedPermanssonRegimeRelative` iff original
baseline Exact GR and all comparison states have unequal frozen-event
probabilities.

## Source gates

1. `FiniteObservedClassSupport.lean` (existing C2 strict class positivity).
2. `FiniteObservedEventMass.lean` (a.s. selector/event equivalence; exact mass).
3. `TypedObservedEventConstitution.lean` (each genuine induced kernel).
4. `FiniteObservedUniformMargin.lean` (finite minimum and original PR iff).
5. `ExactSixStateC7Witness.lean` (C6 recovery; mixed-periodic negative).
6. Independent exact-`Fraction` test suite (>=20 cases), transitive
   axiom audit, research and original builds, both executable workflows,
   review and final synthetic-merge gate before merge.

**Nonclaims:** not empirical identification; not a generic arbitrary
observed-event classifier; not confirmatory PR_g; no cross-kernel
class-selector identity; not a universal infinite-state theorem.
