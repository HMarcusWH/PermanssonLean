# Permansson v0.2.0 — Master Implementation Index

**Role:** the authoritative *live* integration index for the v0.2.0 research
build. Every v0.2.0 mathematical deliverable has a persistent anchor ID below.
Each PR that touches an anchor must update its row in the same PR.

**Created:** 16 October 2026, on `main@6191a1acbf00867042a21c8e6c4a532af43017bc`
(PRs #1–#68 merged; Lean 4.34.0; mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

**Precedence when documents disagree:** mathematical contract
([integration spec](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)) →
current Lean declarations and their exact hypotheses → exact-commit CI evidence →
dated ledgers ([proof ledger](V020_RESEARCH_PROOF_LEDGER.md),
[research build](RESEARCH_BUILD.md), lane documents) → historical plans.
A roadmap entry is never evidence that a theorem exists.

## Status vocabulary

| Status | Meaning |
|---|---|
| PROPOSED | Specified mathematics; no Lean declaration yet |
| DEFINED | Lean definitions/structures exist; the claim itself is not proved |
| PROVED | A Lean theorem with exactly the stated hypotheses compiles with no `sorry`/`admit`/custom axiom, and its transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`. *Source-level status only*; see the Verification field for CI |
| OPEN | Attempted or required, not proved; the reason is recorded |
| BLOCKED | Cannot start until a named upstream anchor is PROVED/merged |

**Verification** is recorded separately from Status: a PROVED anchor is
*CI-verified* only when the Research Lean workflow passes on the exact source
SHA **and** the GitHub synthetic merge, with a recorded run ID. Conditional
theorems (explicit extra hypotheses) are listed with the hypothesis in the
claim and are never described as unconditional.

## Version boundary (all anchors)

- `PermanssonLean/` (frozen v0.1.8 core), `lean-toolchain`, `lake-manifest.json`,
  v0.1.8 TeX/PDF/hashes and application schema: **unchanged** by every anchor
  in this index unless an anchor explicitly states otherwise (none does).
- New mathematics lives only in `PermanssonResearch/`, each module imported
  directly by `PermanssonResearch.lean`.

---

## Dependency graph (anchors)

```text
FROZEN v0.1.8 CORE (PermanssonLean/)
  |-- pathLaw, HasTransitionPair, prefix_maps_eq_of_initial_and_transition,
  |   measure_eq_of_prefix_maps_eq (WellPosedness)
  |
  +-- CA (#66 exit routing) --> CB (#67 switching) --> CC (#68 stopped paths)
  |                                                        |
  |                                                      C69 (#69, this index's first PR)
  |                                                        |
  +-- A2 (#64) / CQ-1 ---------------------+               C70 (random-entry occupation, Prop 4.2f)
  +-- B2 (#65) / Lane B -------------------+                 |
  +-- exact quotients (Thm 7.4b) ----------+--> E1           |
  +-- typed interventions + B2 ------------+--> F1           |
  +-- A2 + C-lane occupation/C11 ----------+--> A3           |
  +-- D0/D1 + C69/C70 ---------------------------------------+--> D2 (separate solver lane)
  +-- E1, F1, A3, C70, D0/D1, C10/C11 -----------------------+--> X1 (flagship)
                                                             |
                                          R (v0.2.0 manuscript + release audit)
```

Forward references (producer → consumers) and backward references
(consumer → providers) are recorded in each anchor's *Inputs* / *Consumers*.

---

## Merged provider anchors (inputs to the remaining program)

These are recorded so consumers can cite exact declarations. Status reflects
the merged source; CI evidence is in the PR and dated ledgers.

| Anchor | Claim (exact encoded scope) | Provider declarations | PR / merge | Status |
|---|---|---|---|---|
| CA.1 | Finite/infinite first-exit routing equals canonical path-event probability, `y ∈ B` | `RegimeExit/ExitConservation.lean`: `exitRouting_eq_prob_exit_in`, `exitRoutingInfinite_eq_prob_exit_in`; `ExitRouting.lean`: `firstExitStep_eq_pathEvent` | #66 / `a5987dc1` | PROVED |
| CA.2 | Conservation: `R^(L)(y,Y\B)+P_y(τ>L)=1`, `R^(∞)(y,Y\B)+P_y(τ=∞)=1` | `exitRouting_add_killedSurvivalMass_eq_one`, `exitRoutingInfinite_add_survivalForever_eq_one` (+ law-start analogues) | #66 | PROVED |
| CA.3 | QSD destination fraction for `0<θ<1`; θ=1 no exit | `QSDDestination.lean`: `qsdRoutingInfinite_eq_fraction`; `QSDExitBoundary.lean`: `qsdThetaOne_no_exit` | #66 | PROVED |
| CB.1 | Switch margin `κ_{ψ_B,J}(B₁) ≥ 1-η` for frozen `ψ_B = P(τ_B=∞)` | `SwitchConstitution.lean`: `switch_constitutive_margin_ge`, `switch_uniformly_strategically_constitutive` | #67 / `6e1fecf4` | PROVED |
| CB.2 | Grounded confirmatory uniform PR bridge for the switch | `SwitchGrounded.lean`: `switch_grounded_confirmatory_uniformPR`, `switch_original_strategic_constitution` | #67 | PROVED |
| CB.3 | Target retention a.s. after routed entry (target Exact GR invariance) | `SwitchRetention.lean`: `switch_eventual_retention_ae`; `SwitchRetentionMass.lean`: `successful_switch_retention_probability_ge` | #67 | PROVED |
| CB.4 | Model-specific (five-state witness) post-switch occupation, **not** generic random entry | `SwitchWitnessOccupation.lean`: `actual_successful_switch_occupation_ae` | #67 | PROVED (witness only) |
| CC.1 | First-exit stopped future = integral over full first-exit **histories** | `StopHistoryFuture.lean`: `firstExit_shifted_history_future_integral`; `StoppedFutureSubmeasure.lean`: `finiteStoppedFutureMeasure_eq_history`, `infiniteStoppedFutureMeasure_univ` | #68 / `6191a1ac` | PROVED |
| CC.2 | *Conditional* bridge: `HasCanonicalLastStateRestart N →` endpoint restart | `ConditionalRestartBridge.lean`: `stoppedFuture_measure_restart_of_lastState` | #68 | PROVED (conditional) |
| CC.3 | *Conditional* reduction: all prefix laws → last-state restart | `StationaryLastStateReduction.lean`: `hasCanonicalLastStateRestart_of_allPrefixLaws` | #68 | PROVED (conditional) |
| A2.1 | Additive primitive TV `δ_K ≤ min(1, δ_α+δ_P+δ_U)` | `Perturbation/PrimitiveTV.lean`: `inducedKernel_tv_le_primitive_sum` | #64 | PROVED |
| A2.2 | Two-budget finite-horizon margin transport | `PrimitiveMargin.lean`: `primitive_constitutiveMargin_abs_le`, `transportPrimitiveFiniteConstitutiveCertificate`; `PrimitiveLipschitz.lean`: `primitiveLipschitz_constitutiveMargin_abs_le` | #64 | PROVED |
| B2.1 | Sequential metric triangle theorems and conditional margins | `GrammarRobust/SequentialEffects.lean`: `jointEffect_le_action_add_condUpdate`, `jointEffect_abs_action_sub_condUpdate_le`; `ConditionalMargins.lean`: `condUpdateMargin_ge_joint_sub_action`, `jointOnly_conditionalMargins_eq_jointMargin` | #65 | PROVED |
| CORE.P54 | Proposition 5.4 finite-prefix TV (linear and geometric) | `PermanssonLean/Probability/FinitePrefixTV.lean`: `proposition_5_4`, `finitePrefix_eventTotalVariation_le_linear` | v0.1.8 | PROVED (frozen) |
| CORE.Q74b | Exact intervention-compatible quotient preservation | `PermanssonLean/Quotient/Preservation.lean`: `quotient_frozenFamilyPR_iff`, `quotient_margin_eq_each_label` | v0.1.8 | PROVED (frozen) |
| CORE.P52 | Property-space margin perturbation bridge | `PermanssonLean/Regime/Perturbation.lean`: `constitutiveMargin_perturbation_abs_le` | v0.1.8 | PROVED (frozen) |

---

## C69 — C-Exit D: unconditional canonical restart (PR #69)

Lane document: [LANE_C_EXIT_RESTART.md](LANE_C_EXIT_RESTART.md) (C-Exit D section).
Source modules: `PermanssonResearch/RegimeExit/ShiftedPrefixStationarity.lean`,
`PermanssonResearch/RegimeExit/StoppedFutureRestart.lean`.

### C69.1 — shifted finite-prefix stationarity

- **Claim.** For every canonical `N : StrategicWorldModel S X A` (arbitrary measurable
  `S, X, A`; no countability/standard-Borel/finite-state hypothesis), every `m : ℕ`,
  every history `h : Π i : Iic m, S × X`, and every `T : ℕ`:
  `(canonicalShiftedHistoryKernel N m h).map (frestrictLe T) = (canonicalFutureKernel N (h m)).map (frestrictLe T)`.
  I.e. `HasCanonicalShiftedPrefixLaws N` holds unconditionally.
- **Source.** Spec §2.3 (strong Markov step of Prop. 4.2f); LANE_C_EXIT_RESTART step 3.
- **Provider.** `hasCanonicalShiftedPrefixLaws`; supporting `shiftedHistory_hasTransitionPair`,
  `stationaryHistoryKernel_add_eq_comap_drop`, `map_frestrictLe_zero_of_eval_zero`, and the
  generic `PermanssonResearch.Probability.compProd_map_left_eq_map_compProd_comap`
  (moved to `Probability/CompProdPushforward.lean` by the E1 PR; originally in this module).
- **Inputs.** Frozen `StrategicWorldModel.prefix_maps_eq_of_initial_and_transition`,
  `pathLaw_has_transition_pair`; mathlib `Kernel.partialTraj_compProd_eq_map_traj`,
  `Kernel.traj_map_frestrictLe_apply`; #68 `shiftedHistory_zero_marginal`,
  `canonicalFutureKernel_apply`, `canonicalFutureKernel_zero_marginal`.
- **Consumers.** C69.2.
- **Counterexamples.** Time-inhomogeneous kernels (stationarity is used exactly in
  `stationaryHistoryKernel_add_eq_comap_drop`); second-order history-dependent chains.
  Python: `C69LastStateRestartTests.test_negative_control_past_dependent_chain`,
  `C69StoppedFutureTests.test_nonstationary_kernel_breaks_restart`.
- **Status.** PROVED.
- **Verification.** Local: module compiles on Lean 4.34.0 / pinned mathlib; local
  `#print axioms` audit of all 34 new C69 declarations: only `propext`,
  `Classical.choice`, `Quot.sound` (33 after the E1 PR moves the generic
  `compProd_map_left_eq_map_compProd_comap` to `Probability/CompProdPushforward.lean`,
  where `e1_axiom_audit.py` audits it). CI: see PR #69 (record run IDs at merge).
- **Manuscript.** v0.2.0 §4.2 strong-Markov lemma preceding Prop. 4.2f.

### C69.2 — unconditional full-future last-state restart

- **Claim.** `HasCanonicalLastStateRestart N` for every canonical `N`:
  `canonicalShiftedHistoryKernel N m h = canonicalFutureKernel N (h m)`, i.e.
  `L(Y_{m+·} | Y_{0:m}=h) = P_{h_m}` as probability measures on `ℕ → S × X`.
- **Source.** Spec §2.3; LANE_C_EXIT_RESTART.
- **Provider.** `hasCanonicalLastStateRestart`, `canonicalShiftedHistoryKernel_eq_restart`;
  corollaries `canonicalShiftedHistoryKernel_eq_of_last_eq` (different pasts/lengths),
  `pointPathLaw_shifted_lastState_joint`, `pointPathLaw_prefix_shift_event`
  (deterministic-time Markov property, event form).
- **Inputs.** C69.1; #68 `hasCanonicalLastStateRestart_of_allPrefixLaws`
  (which uses frozen `measure_eq_of_prefix_maps_eq`); `pointPathLaw_shifted_history_joint`.
- **Consumers.** C69.3, C69.4, C70.1, C70.2, D2.4.
- **Counterexamples.** Same as C69.1. No `StrongMarkov` premise and no second path-law construction.
- **Status.** PROVED.
- **Verification.** As C69.1.
- **Manuscript.** v0.2.0 §4.2 (Lemma: deterministic-time and first-exit Markov restart).

### C69.3 — unconditional finite first-exit future law

- **Claim.** For `y ∈ B`, finite `n`, measurable `D`, measurable `F ⊆ (ℕ → S × X)`:
  `P_y(E_{n,D} ∩ θ_{n+1}⁻¹F) = ∫_{z∈D} P_z(F) ExitStep_n(y,dz)`, first exit at time `n+1`;
  `ExitStep_n` is the unnormalized PR #66 submeasure and `restrict D = restrict (D \ B)`.
- **Source.** Spec §2.3; LANE_C_EXIT_RESTART "planned primary identity".
- **Provider.** `finiteStoppedFutureMeasure_restart`, `firstExit_shift_event_restart`,
  `finiteStoppedFutureMeasure_eq_bind` (measure form), `firstExitStepMeasure_region_zero`,
  `firstExitStepMeasure_restrict_diff_region`.
- **Inputs.** C69.2; CC.2 `stoppedFuture_measure_restart_of_lastState` (its hypothesis
  is now discharged); CA `firstExitStepMeasure`, `exitSubkernel_region_zero`.
- **Consumers.** C69.4, C70.1, C70.2.
- **Counterexamples.** Indexing at `n` instead of `n+1`; destination inside `B`;
  post-intervention kernel mismatch (`test_post_intervention_kernel_mismatch_rejected`).
- **Status.** PROVED.
- **Verification.** As C69.1.
- **Manuscript.** v0.2.0 §4.2, Prop. 4.2f proof, step "restart at first exit".

### C69.4 — countable infinite-future exit routing

- **Claim.** For `y ∈ B`, measurable `D`, `F`:
  `μ_D^∞(F) = Σ_n μ_{n,D}(F) = ∫ P_z(F) (R_B^{(∞)}(y,·)|_D)(dz)`; pathwise,
  `P_y(τ_B<∞, Y_{τ_B}∈D, θ_{τ_B}∈F) = ∫_D P_z(F) R_B^{(∞)}(y,dz)` with `τ_B` only ever
  evaluated at finite values; never-exit mass is preserved
  (`μ_{Y\B}^∞(univ) + P_y(τ_B=∞) = 1`); zero routing mass gives zero future mass.
- **Source.** Spec §2.2–2.3 (V20.4–V20.7).
- **Provider.** `infiniteStoppedFutureMeasure_apply_tsum`, `infiniteStoppedFutureMeasure_restart`,
  `infiniteStoppedFutureMeasure_eq_bind`, `firstExitFutureEvent`, `mem_firstExitFutureEvent_iff`,
  `pathLaw_firstExitFutureEvent`, `pathLaw_firstExitFutureEvent_restart`,
  `infiniteStoppedFutureMeasure_add_survivalForever_eq_one`,
  `infiniteStoppedFutureMeasure_eq_zero_of_routing_zero`, `infiniteStoppedFutureMeasure_le_routing`.
- **Inputs.** C69.3; CA.1/CA.2; mathlib `lintegral_sum_measure`, `Measure.restrict_sum`, `measure_iUnion`.
- **Consumers.** C70.1, C70.2, C70.3, D2.4.
- **Counterexamples.** Normalizing a zero-mass arrival; assigning never-exit mass to a
  destination; evaluating `Y_τ` at `τ=∞` (Python `C69CountableRoutingTests`).
- **Status.** PROVED.
- **Verification.** As C69.1.
- **Manuscript.** v0.2.0 §4.2 Theorem 4.2e′ (routing with restart) and Prop. 4.2f proof.

### C69.5 — destructive tests and focused CI

- **Claim.** Executable exact-`Fraction` cross-checks (not proofs): different pasts/same last
  state, every prefix horizon, branching futures, competing destinations, delayed exits and
  `n+1` indexing, no exit and zero arrival, positive never-exit mass with exact infinite
  routing (Gaussian elimination over `Fraction`) and exact finite remainder identity,
  post-intervention kernel mismatch, nonstationary-kernel and second-order-chain
  counterexamples, future-dependent (non-cylinder) events.
- **Provider.** `verification/research/test_c_exit_restart.py` classes
  `C69LastStateRestartTests`, `C69StoppedFutureTests`, `C69CountableRoutingTests`
  (21 new tests; 47 total in the file); `.github/workflows/c-exit-restart-d-smoke.yml`.
- **Status.** PROVED is not applicable (executable evidence). Local result: 47/47 pass.

---

## C70 — C-Exit E: random-entry occupation and Proposition 4.2f (next PR)

**Status of lane:** BLOCKED on C69 merge (or an explicitly stacked PR on top of #69).

### C70.1 — almost-sure occupation after random entry

- **Claim.** Let `J` be admissible strategic, `R' = (J(G), P, B', B'_0, h', ν', c')` an
  independently certified Exact GR for `K^J` with almost-sure weak occupation convergence,
  `B'_0 ⊆ B' ⊆ Y \ B`. For `y ∈ B`, `P^J_y`-a.s. on `{τ_B < ∞, Y_{τ_B} ∈ B'_0}`, the
  post-entry empirical `h'`-occupation measures converge weakly to `ν'`; and the
  *whole-path* empirical occupation `T⁻¹ Σ_{t<T} δ_{h'(Y_t)}` also converges to `ν'`
  (finite random prefix deleted with an explicit `2τ_B/T` bounded-Lipschitz or
  weak-topology estimate).
- **Source.** Spec §2.3 (random-entry argument).
- **Provider (planned).** `RegimeExit/RandomEntryOccupation.lean`:
  `postEntryOccupation_ae`, `empiricalOccupation_shift_tendsto_iff` (finite-prefix deletion),
  `switch_occupation_ae_of_routing`.
- **Inputs.** C69.2–C69.4; CB.3; frozen `Regime/Occupation.lean`
  (`empiricalOccupation`, `IsLimitingOccupationLaw`), `ConvergenceMode.almostSureWeak`;
  target `IsExactGeneratedRegime` certificate.
- **Consumers.** C70.3, X1.3.
- **Counterexamples.** Target entered without Exact-GR invariance; occupation target
  of a *different* kernel; descriptor undefined outside `B'`.
- **Status.** PROPOSED.

### C70.2 — in-probability convergence after random entry

- **Claim.** With a research-library in-probability weak-convergence mode (explicitly typed
  over a metric on `ProbabilityMeasure H`), the post-entry occupation converges in
  probability on the routed event, using endpoint-conditioned convergence probabilities,
  the countable stopping decomposition (C69.4) and dominated/bounded convergence.
- **Provider (planned).** `RegimeExit/InProbabilityOccupation.lean`.
- **Counterexamples.** An arbitrary `ConvergenceMode.custom` predicate is **not** transported.
- **Status.** PROPOSED.

### C70.3 — completed scoped Proposition 4.2f

- **Claim.** Combine CA, CB, C69, C70.1–C70.2 and the grounded confirmatory semantics:
  routing bound `R_B^{J,∞}(y,B'_0) ≥ 1-η` on `B₁` ⇒ with probability `≥ 1-η` finite
  first exit into `B'_0`, retention in `B'` and target occupation convergence (for the two
  supported modes); `ψ_B(P_y)=P_y(τ_B=∞)` frozen; `κ_{ψ_B,J}(B₁) ≥ 1-η`; positive
  uniform constitution only under `η<1` and all original gates.
- **Provider (planned).** `RegimeExit/Proposition42f.lean`: `proposition_4_2f_almostSure`,
  `proposition_4_2f_inProbability`.
- **Status.** PROPOSED.

---

## E1 — approximate type-respecting quotients (branch `claude/zen-einstein-ub8zgr-e1`, stacked on #69)

Lane document: [LANE_E1_APPROX_QUOTIENT.md](LANE_E1_APPROX_QUOTIENT.md). Modules:
`Probability/EventTVCalculus.lean`, `Probability/CompProdPushforward.lean`,
`Quotient/ApproxPrefix.lean`, `Quotient/ApproxMargin.lean`, `Quotient/ApproxAdversaries.lean`.

| Anchor | Claim | Provider | Status |
|---|---|---|---|
| E1.0 | General event-TV calculus without countability: integral of `[0,1]` functions within TV (Hahn), pushforward contraction, triangle, two `⊗ₘ` comparison bounds | `lintegral_le_add_eventTotalVariation`, `eventTotalVariation_map_le`, `eventTotalVariation_triangle`, `eventTotalVariation_compProd_right_le`, `eventTotalVariation_compProd_left_le` | PROVED |
| E1.1 | Defect as an UPPER-BOUND predicate `HasQuotientDefect q K K̄ η :⇔ ∀ y, ‖q_#K(y,·) − K̄(q y,·)‖_TV ≤ η` over EVERY fine state (the spec's `η = sup_y …` is the least such bound; the supremum itself is not defined in Lean and all theorems are monotone in `η`); per-label defects `η_ℓ` against `K̄^{φ(ℓ)}` enter as per-label hypotheses of the family theorem; exact intertwining ⇒ `η=0` | `HasQuotientDefect`, `ApproxKernelIntertwines`, `approxKernelIntertwines_zero_of_exact` | DEFINED (+ PROVED reduction) |
| E1.2 | `TV(q-projected fine T-prefix, coarse T-prefix) ≤ min(1, Tη)` from the same fine start; projected process need not be Markov | `approxQuotient_prefix_tv_le_linear`, `approxQuotient_prefix_tv_le_min`, `approxQuotient_pathLaw_tv_le_linear` (spec name), `approxQuotient_pathLaw_prefix_tv_le` | PROVED |
| E1.3 | For a factored property whose coarse side is an `L`-event-TV-Lipschitz `T`-prefix functional (`TVLipschitzPrefixProperty`, `L = p.constant`), with `0 ≤ η₀, η_J`: `\|Δ(y)−Δ̄(q y)\| ≤ L(min(1,Tη₀)+min(1,Tη_J))`; margins with `B̄₁ = q(B₁)`; positive-margin transfer; frozen-family version; Thm 7.4b certificate interface (arbitrary factored `ψ`, `QuotientCompatibleComparisonSets`); exact intertwining ⇒ equal margins | `approxQuotient_effect_abs_le`, `approxQuotient_margin_abs_le`, `approxQuotient_fine_margin_pos_of_coarse`, `approxQuotient_coarse_margin_pos_of_fine`, `approxQuotient_family_margin_abs_le`, `approxQuotient_margin_abs_le_of_certificates`, `approxQuotient_margin_eq_of_exact` | PROVED |
| E1.4 | Leakage counterexample (Lean, kernel level): for every `ε ∈ (0,1]`, defect ≤ ε, fine region one-step invariant, coarse model leaves it with probability exactly ε (Exact-GR/PR non-transfer is the interpretation, not a separate theorem); Python (finite chains, NOT proofs): non-Markov projection from one start with non-vacuous linear bound (`Tη < 1`), defect over unreachable states, initial-law lift failure, lumpable η=0 (horizons ≤ 5) and equal margins, leakage incl. the η=1 cap, factorization failure, label mismatch, baseline-only certificate insufficient, non-saturated region does not descend, untyped (parity) quotient with η=0 rejected, positive margins above budget transferring in both directions with a leaking coarse region and an admissible `B₁` | `small_defect_does_not_preserve_invariance`; `test_e1_approx_quotient.py` (20) | PROVED / executable |
| E1.5 | Geometric bound `1 − (1 − η)^T` | — | OPEN (needs a measurable common-mass construction; NOT implied by E1.2) |

Inputs: CORE.Q74b (`TypeRespectingStateCompression`, `KernelIntertwines`, `kernelIntertwines_apply`,
`QuotientFamilyMatching`, `PropertyFactorsThroughCompression`, `QuotientCompatibleComparisonSets`),
CORE.P54 (`finitePrefixLaw`, `eventTotalVariation`), A2 (`TVLipschitzPrefixProperty`),
CQ-1 (`ConstitutiveQuasi.pathLaw_finitePrefix_eq`),
CORE.P52 (`abs_sInf_image_sub_sInf_image_le_of_uniform`), C69 shared lemma (moved to
`Probability/CompProdPushforward.lean`). Consumers: X1, R. Manuscript: §7.4.3 (Thm 7.4c).
Verification: local compile; `e1_axiom_audit.py` all declarations allowlisted (count in the PR); CI pending (E1 PR).

## F1 — multi-agent closed-loop versus opponent-locked protocols

| Anchor | Claim | Planned provider | Status |
|---|---|---|---|
| F1.1 | Conditional-product subclass: player action kernels `α_i`, update kernels `U_i`, common `U_0`, common `P`; product composition is a `StrategicWorldModel` | `MultiAgent/ProductGame.lean` | PROPOSED |
| F1.2 | CL and OL protocols as distinct typed interventions; OL requires a declared measurable opponent anchor | `MultiAgent/Protocols.lean` | PROPOSED |
| F1.3 | `|Δ_CL − Δ_OL| ≤ d_ψ(z_CL, z_OL) ≤ Δ_CL + Δ_OL`, connected to original path-law margins | `MultiAgent/AdaptationBound.lean`: `abs_closedLoop_sub_openLoop_le_adapt` | PROPOSED |
| F1.4 | Witnesses: CL≠OL, CL=OL, baseline-support-only anchor non-identification; correlated actions out of scope | `MultiAgent/ProtocolWitnesses.lean` + Python | PROPOSED |

Inputs: typed interventions (frozen), B2.1. Consumers: X1, R. Manuscript: §5.4.3.

## A3 — contractive infinite-horizon robustness (branch `claude/zen-einstein-ub8zgr-a3`, stacked on the E1 branch / #71)

Lane document: [LANE_A3_CONTRACTIVE.md](LANE_A3_CONTRACTIVE.md). Modules:
`Probability/KantorovichDual.lean`, `Probability/KantorovichTV.lean`,
`Perturbation/ContractiveOccupation.lean`, `Perturbation/ContractiveAdversaries.lean`.
All W₁ statements use the Kantorovich–Rubinstein DUAL form `W1DualLE` (measurable, bounded, 1-Lipschitz
tests) on arbitrary pseudo-metric spaces; KR duality with the coupling form is NOT formalized.

| Anchor | Claim | Provider | Status |
|---|---|---|---|
| A3.0 | Dual-W₁ calculus without Polish/standard-Borel hypotheses: monotone, symmetric, triangle, closed under limits; pointwise kernel defect ⇒ mixture defect; `L`-Lipschitz pushforward scales by `L`; finite first moments ⇒ finite bound | `W1DualLE`, `IsKRTest`, `W1DualLE.trans`, `W1DualLE.of_tendsto`, `W1DualLE.comp_of_forall`, `W1DualLE.map_lipschitz`, `W1DualLE.of_integrable_dist` | DEFINED (+ PROVED) |
| A3.1 | (V20.17) `W₁(π, π̃) ≤ δ/(1−ρ)` given invariance of both laws, uniform dual-W₁ contraction `0 ≤ ρ < 1` of the ORIGINAL kernel, pointwise defect `δ` at every state and a finite initial gap (no finite-state restriction) | `invariantLaw_wasserstein_le`, `ContractivePerturbation.w1_le` | PROVED |
| A3.2 | (V20.18) `\|κ̃ − κ\| ≤ L_F L_h (δ₀/(1−ρ₀) + δ_J/(1−ρ_J))` for the ORIGINAL frozen margins when `ψ(P_y) = F(h_#π)` for all four processes on `B₁` (hypothesis), `h` measurable `L_h`-Lipschitz, `F` `L_F`-Lipschitz for dual W₁ | `occupationMargin_robust`, `descriptorFunctional_dist_le` | PROVED |
| A3.3 | Survival counterexample on actual models (`Unit × ℝ`): for every `ε ∈ (0,1]`, both kernels are dual-W₁ contractions with `ρ = 0`, defect `≤ ε`, yet `P₀(τ_B = ∞)` is `1` vs `0` | `contraction_does_not_transfer_survival` | PROVED |
| A3.4 | TV → W₁ only with a diameter factor: `dist ≤ D ⇒ W₁ ≤ D·TV`; on `ℝ` no constant converts TV into W₁ | `W1DualLE.of_eventTV`, `tv_does_not_control_w1_on_real` | PROVED |
| A3.5 | Existence/uniqueness of invariant laws; contraction from Doeblin/Dobrushin; ergodic bridge `ψ(P_y) = F(h_#π)`; KR duality; bounded → all 1-Lipschitz tests | — | OPEN (hypotheses in A3.1–A3.2) |

Inputs: E1.0 (`abs_lintegral_toReal_sub_le_eventTotalVariation`, `eventTotalVariation_le_of_forall`,
`abs_measureReal_sub_le_eventTotalVariation`); frozen `constitutiveMargin`, `constitutiveEffect_nonneg`,
`baselinePropertyValue`, `intervenedPropertyValue`, `ConstitutiveComparisonSet.pathLawNontrivial`,
`PermanssonLean/Regime/Perturbation.lean: abs_sInf_image_sub_sInf_image_le_of_uniform`; frozen survival
machinery (`killedKernel_apply`, `survivalProbability_eq_killedSurvivalMass`, `killedSurvivalMass`,
`survivesForeverSet_eq_iInter`, `survivesThroughSet_antitone`, `measurableSet_survivesThroughSet`) and
`StrategicWorldModel.inducedKernel_apply`. A2 is NOT used (no primitive budget is converted; A3.4 shows why a TV
budget cannot be substituted). Consumers: X1, R. Manuscript: §5.4.1.
Verification: local compile; `a3_axiom_audit.py` 50/50 declarations allowlisted; CI on the A3 PR.

## D2 — reverse-solver regime-switching objectives (separate lane)

| Anchor | Claim | Planned provider | Status |
|---|---|---|---|
| D2.1 | Reach-by-horizon objective with exact Bellman evaluation on declared finite policy classes | `ReverseSolver/D2Reach.lean` | PROPOSED |
| D2.2 | Reach-before-forbidden objective | `ReverseSolver/D2ReachAvoid.lean` | PROPOSED |
| D2.3 | Reach-and-stay for declared finite duration (hit ≠ stay) | `ReverseSolver/D2ReachStay.lean` | PROPOSED |
| D2.4 | Eventual switching under exact/bounded conditions, consuming C69.4 | `ReverseSolver/D2Switch.lean` | BLOCKED (C69, C70) |
| D2.5 | `sup_π inf_K` vs `inf_K sup_π` separation witness; no rectangularity assumed | `ReverseSolver/D2MinimaxAdversaries.lean` | PROPOSED |

Inputs: D0/D1, C69, C70. Must not mutate D0/D1 receipts.

## X1 — flagship economic-world MPE versus learning model

| Anchor | Claim | Planned provider | Status |
|---|---|---|---|
| X1.1 | Exact rational MPE: Bellman equations and every unilateral incentive inequality on the commons family (spec §8.1) | `Examples/CommonsMPE.lean` + independent rational checker | PROPOSED |
| X1.2 | Learning generator in the SAME world `P`, Markov-sufficient memory | `Examples/CommonsLearning.lean` | PROPOSED |
| X1.3 | Comparative regime certificates (persistence, occupation, GR, constitution, grounding, nine categorical dimensions) | `Examples/CommonsComparison.lean` | PROPOSED |
| X1.4 | Scientific interpretation section | manuscript | PROPOSED |

Inputs: E1, F1, A3, C69/C70, D0/D1, C10/C11. Consumers: R.

## R — v0.2.0 manuscript and release

| Anchor | Deliverable | Status |
|---|---|---|
| R.1 | New versioned v0.2.0 TeX (v0.1.8 untouched), only PROVED or visibly conditional statements | PROPOSED |
| R.2 | Theorem-to-Lean crosswalk generated from this index | PROPOSED |
| R.3 | Environment/commit manifests, machine-readable receipts, SHA-256 inventory | PROPOSED |
| R.4 | Editorial carry-forward (spec §9) | PROPOSED |
| R.5 | Fresh end-to-end reproduction and audit | PROPOSED |

---

## Handoff log

### PR #69 (C-Exit D) — opened from `claude/zen-einstein-ub8zgr`, base `main@6191a1ac`

- **Completed anchors:** C69.1–C69.4 (PROVED, source level), C69.5 (tests/workflow).
- **Open anchors:** none inside C69. C70.* depend on C69 merge.
- **Version boundary:** frozen core, toolchain, manifest, v0.1.8 paper and
  application schema unchanged.
- **Next PR contract (C70):** inputs `hasCanonicalLastStateRestart`,
  `pathLaw_firstExitFutureEvent_restart`, `infiniteStoppedFutureMeasure_restart`,
  CB.3 retention; target C70.1–C70.3 above.
