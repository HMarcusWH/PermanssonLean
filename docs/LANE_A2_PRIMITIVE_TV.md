# A2 — Typed primitive-kernel TV robustness (PR #64)

**Research status: IMPLEMENTATION IN PROGRESS / UNVERIFIED UNTIL EXACT-HEAD RESEARCH LEAN CI.**
**Base:** `main@d137ac2308285f843a1ccf76fede74b4b6b65131`.
**Release target:** proposed Permansson v0.2.0 Proposition 5.5 / Corollary 5.6.
**Boundary:** independently versioned `PermanssonResearch` theory. Original v0.1.8 paper, Lean source, hashes, application schema and toolchain are frozen.

## Question and mathematical target

The strategic-world model samples action `α`, next world `P`, and updated strategic state `U` in that order. Its genuine induced Markov kernel is `K = K_(α,P,U)`. For two same-typed triples with all-row event-supremum total-variation upper errors `δα, δP, δU ∈ [0,1]`, establish:

```text
  ∀ y, TV(K(y), Ktilde(y)) ≤ dK = min(1, δα + δP + δU)
  ∀ y, TV(prefix_T(K,y), prefix_T(Ktilde,y)) ≤ e_T
  e_T = 1 - (1-dK)^T ≤ T*dK
```

The actual Lean typeclass hypotheses for the common-part construction include the source/target `CountableOrCountablyGenerated` instances, rather than silently claiming every arbitrary measurable-space kernel supports the constructed common density.

No stage-independence assumption is necessary. Construct a common dominated subkernel of the actual three-stage sampling order, and bound the missing probability mass. The additive theorem is the A2 release obligation. The optional sharper primitive *product* bound requires a separately accepted proof and is explicitly deferred.

## Original versus approximate intervention

`PrimitiveModelPair` retains the same strategic/world/action measurable types and component type, with an actual original and approximate `AdmissibleStrategicIntervention`. Its `component_eq` and `target_eq` witnesses prevent silently treating two unrelated target grammars as the same frozen intervention.

`J` is strategic: `P^J=P`. The approximation's matched strategic intervention is also strategic: `Ptilde^Jtilde=Ptilde`. A2 permits **P ≠ Ptilde as model error**, not as a strategic-generator intervention. This is why the original CQ-1 `StrategicApproximationPair` with `approx_world_eq` cannot be reused unchanged.

All primitive errors apply to all rows used by each relevant model, including intervention-reachable rows invisible at baseline. Comparisons are *conditional* on a matching substantive protocol and on those global bounds; the theorem does not identify them from observations.

## Two independent budgets and real margin

For the baseline and matched intervened pair, supply separate `PrimitiveErrorBounds` and independently derive `d0,dJ`; never reuse the baseline bound without an intervention-specific hypothesis. For any frozen measurable `[0,1]` finite-prefix score `f` and horizon `T`:

```text
  e0 = 1 - (1-d0)^T
  eJ = 1 - (1-dJ)^T
  |κtilde_f(B1) - κ_f(B1)| ≤ e0 + eJ
```

This is the source-compatible factor-one bounded score. A generic L-Lipschitz path property is **not** automatically admitted as a `FinitePathProperty`; a separate explicit Lipschitz bridge is needed. The existing `RegimeSpecification.constitutiveMargin_perturbation_abs_le` proves the metric margin part. The actual second-model uniform margin must be identified via the original `transportComparisonSet` theorem (requires `MeasurableSpace.SeparatesPoints`).

Optional independently verified numerical output-error values `b0,bJ` can be added *after* the exact model comparison via `HasConstitutiveOutputErrors`. Do not call a numerical output profile the exact margin of a second model.

## Complete CQ-1 finite-persistence certificate

The current original `FiniteConstitutiveCertificate` combines:
1. `IsFinitePersistent M spec T eta`, for **every** `y ∈ spec.region`;
2. `0 < κ`;
3. `κ ≤ original constitutiveMargin`, over the complete B₁.

From a certified original finite certificate and `κ > e0 + eJ`, construct an approximate *genuine* finite certificate using:
- `eta' = clampedPersistenceError eta e0`;
- `κ' = κ - e0 - eJ > 0`;
- `transportComparisonSet` for the approximate baseline;
- the original finite-survival TV bridge for every state in the region.

When `eta'=1`, the persistence statement may be vacuous, so a **nontrivial survival floor** requires an additional condition `eta+e0<1`. This certificate is not Exact GR, Exact PR, QSD, identified causal effect or empirical classification.

## Source files

- `PermanssonResearch/Perturbation/PrimitiveModelPair.lean` — typed matched models and original comparison transport
- `PermanssonResearch/Perturbation/PrimitiveTV.lean` — true induced-kernel primitive error derivation
- `PermanssonResearch/Perturbation/PrimitiveMargin.lean` — two-budget error, exact profile, uniform margin and complete certificate
- `verification/research/test_a2_primitive_tv.py` — deterministic exact-rational primitive/order/negative controls
- `PermanssonResearch.lean` — root imports; verification infrastructure audits every research declaration

## Destructive suite

Tests A2-01 through A2-15 include zero/single stage/capped errors, 0/1-horizon cases, post-intervention-only rows, x'-sensitive update order, changed P as structural error, zero uniform gap despite a positive statewise effect, small-leak infinite-invariance failure, score bounds, protocol matching and seeded exact-rational exhaustive path-law examples.

The Python suite is not a Lean theorem, a source-bound Lean receipt, or a proof of external data identity. Required Lean witness/negative controls remain a separate review gate.

## Review and release gates

**Before changing PROPOSED to PROVED**, all of the following must be observed on the *exact final PR head and GitHub synthetic merge*: actual research Lean compilation of theorem declarations; all discovered test suites; root imports; transitive axiom audit restricted to `propext, Classical.choice, Quot.sound`; `sorry/admit/axiom` firewall; original Lean build; D0 and C10 release evidence; executable verification; application contract Ubuntu/Windows; source review of actual binder/quantifier scopes; and explicit author merge approval.

CI green never proves identification, forecast skill or third-party peer review. Do not merge this draft while any required check remains pending or while substantive findings are open.
