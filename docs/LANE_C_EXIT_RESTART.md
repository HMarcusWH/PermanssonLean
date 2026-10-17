# C-Exit C/D — Canonical stopped-path restart (PRs #68, #69)

## C-Exit D (PR #69) — unconditional restart: C69.1–C69.5

**Base:** `main@6191a1acbf00867042a21c8e6c4a532af43017bc` (PR #68 merged).
**Branch:** `claude/zen-einstein-ub8zgr`. **Anchors:** see
[V020_IMPLEMENTATION_INDEX.md](V020_IMPLEMENTATION_INDEX.md) §C69.

The PR #68 obligations that were left as explicit predicates are now
**discharged without new hypotheses**:

| Anchor | Statement | Declaration | Module |
|---|---|---|---|
| C69.1 | `HasCanonicalShiftedPrefixLaws N` for every canonical `N` | `hasCanonicalShiftedPrefixLaws` | `RegimeExit/ShiftedPrefixStationarity.lean` |
| C69.1 (core step) | shifted continuation satisfies the frozen `HasTransitionPair` for `N.inducedKernel` | `shiftedHistory_hasTransitionPair` | same |
| C69.2 | `HasCanonicalLastStateRestart N`: `L(Y_{m+·}\|h) = P_{h_m}` | `hasCanonicalLastStateRestart`, `canonicalShiftedHistoryKernel_eq_restart` | same |
| C69.2 corollaries | different pasts / lengths, same last state ⇒ same future law; deterministic-time Markov property (joint and event forms) | `canonicalShiftedHistoryKernel_eq_of_last_eq`, `pointPathLaw_shifted_lastState_joint`, `pointPathLaw_prefix_shift_event` | same |
| C69.3 | `P_y(E_{n,D} ∩ θ_{n+1}⁻¹F) = ∫_D P_z(F) ExitStep_n(y,dz)` for every measurable `F` | `finiteStoppedFutureMeasure_restart`, `firstExit_shift_event_restart`, `finiteStoppedFutureMeasure_eq_bind` | `RegimeExit/StoppedFutureRestart.lean` |
| C69.3 mask | `ExitStep_n(y,B)=0`, so restricting to `D` equals restricting to `D\B` | `firstExitStepMeasure_region_zero`, `firstExitStepMeasure_restrict_diff_region` | same |
| C69.4 | `μ_D^∞(F) = Σ_n μ_{n,D}(F) = ∫ P_z(F) R_B^{(∞)}(y,dz)\|_D` | `infiniteStoppedFutureMeasure_apply_tsum`, `infiniteStoppedFutureMeasure_restart`, `infiniteStoppedFutureMeasure_eq_bind` | same |
| C69.4 pathwise | `P_y(τ_B<∞, Y_{τ_B}∈D, θ_{τ_B}∈F) = ∫_D P_z(F) R_B^{(∞)}(y,dz)`, `τ_B` finite by construction | `firstExitFutureEvent`, `mem_firstExitFutureEvent_iff`, `pathLaw_firstExitFutureEvent`, `pathLaw_firstExitFutureEvent_restart` | same |
| C69.4 firewalls | never-exit mass preserved; zero routing ⇒ zero future; no mass creation | `infiniteStoppedFutureMeasure_add_survivalForever_eq_one`, `infiniteStoppedFutureMeasure_eq_zero_of_routing_zero`, `infiniteStoppedFutureMeasure_le_routing` | same |

### Proof route (no new path-law construction, no `StrongMarkov` premise)

1. `shiftedHistory_zero_marginal` (PR #68) fixes the time-0 law at `δ_{h_m}`.
2. Mathlib's `Kernel.partialTraj_compProd_eq_map_traj` is the absolute-time
   transition-pair identity of `traj κ m h` at time `m+n`.
3. **Stationarity is used exactly once**, in
   `stationaryHistoryKernel_add_eq_comap_drop`: the history kernel at
   `m+n` reads only the last coordinate, hence equals the time-`n` kernel
   read through the map that drops the first `m` coordinates. The generic
   `compProd_map_left_eq_map_compProd_comap` transports step 2 to the
   shifted law.
4. The frozen `prefix_maps_eq_of_initial_and_transition` gives every prefix
   law (C69.1); the frozen projective uniqueness theorem
   `measure_eq_of_prefix_maps_eq`, via PR #68's
   `hasCanonicalLastStateRestart_of_allPrefixLaws`, gives the full law (C69.2).
5. C69.2 discharges the hypothesis of PR #68's
   `stoppedFuture_measure_restart_of_lastState` (C69.3); `Measure.restrict_sum`
   and `lintegral_sum_measure` give the countable interchange (C69.4).

No finite-state, countable or standard-Borel restriction is used. The
theorem is specific to the **stationary** canonical model; the Python suite
contains a nonstationary counterexample and a second-order chain where
last-state restart fails.

### Verification evidence (local, this branch)

- Lean 4.34.0 / pinned mathlib `5ed29652`: both modules compile; full
  `lake build PermanssonResearch` and default `lake build` are re-run
  before the PR is marked ready (see PR #69 body for exact results).
- `verification/research/c69_axiom_audit.py`: 34/34 new declarations depend
  only on `propext`, `Classical.choice`, `Quot.sound`.
- `verification/research/test_c_exit_restart.py`: 47/47 exact-Fraction
  tests (26 pre-existing + 21 C69 tests: `C69LastStateRestartTests`,
  `C69StoppedFutureTests`, `C69CountableRoutingTests`).
- Focused workflow: `.github/workflows/c-exit-restart-d-smoke.yml`.

These are source-level results. CI verification is recorded on PR #69 with
exact run IDs; no PASS is inherited by later commits.

### Out of scope here (next: C70)

Random-entry occupation convergence (almost-sure and in-probability) and
the completed scoped Proposition 4.2f are C70.1–C70.3. Nothing in this PR
asserts target occupation convergence after random entry.

---

## Historical PR #68 plan (C-Exit C) — preserved

**Status:** active draft; incrementally compile the kernel and path-law
proofs before claiming the arbitrary measurable-event restart theorem.

**Base:** merged \`main@6e1fecf4fc3731b5c6ebee937edf3201b8186fcf\`
(PR #67; four post-merge workflows passed).

**Specification:** \`docs/PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md\`
§2.3 (Proposition 4.2f), mathematically separate from the already-proved
arrival and constitutive-margin certificates.

## Planned primary identity

For \`N\` a fixed canonical strategic-world model, source \`B\`, actual
first exit \`E(n,D)\`, \`y∈B\`, and a measurable \`A⊆(ℕ→Y)\`:

\`\`\`text
P_y(E(n,D) ∩ shift_(n+1)^-1(A))
  = ∫ z in D, P_z(A) ∂firstExitStepMeasure(N,B,n,y).
\`\`\`

Equivalently the corresponding restricted/shifted measures on infinite
paths are equal. First-exit never occurs at time zero from y∈B.

## Do not fake the missing step

1. \`CanonicalTailKernel.lean\`: actual measurable infinite-future kernel,
   equal to the canonical Dirac-point path law.
2. \`RestartSanity.lean\`: check the shifted future's zeroth observation
   equals the genuine first-exit endpoint measure. **Not full restart.**
3. \`StationaryTailLaw.lean\`: prove deterministic-time continuation for
   full future path from the last observed state (not just one-step law).
4. \`SwitchRestartLaw.lean\`: prove finite first-exit restricted-shifted
   probability-measure equality using the actual post-intervention model.
5. \`SwitchRestartSum.lean\`: disjoint countable first-exit-time mixture,
   preserving missing never-exit mass and zero-probability cases.
6. \`SwitchRestartAdversaries.lean\`: typed true-kernel witnesses
   for nontrivial future events.

Do NOT apply \`pathLaw\` to unnormalized exit submeasures. Use a Markov
kernel composed with the submeasure. Use the original \`D\B\` mask,
the original stationary \`α→P→U\` process, and do not assume \`StrongMarkov\`
as a premise. Standard-Borel or finite-state restrictions are not
automatically valid for the general theorem. Prove arbitrary measurable
future-event identity, not merely first-coordinate agreement.

## CI acceptance

Focused source-head smoke + original Lean, executable verification,
application contracts, Research Lean synthetic merge, 3-axiom
transitive audit, direct research-root imports, 668+ regressions,
source firewall, D0-F golden/C10 evidence.

A green focused smoke for a *subset* of modules is NOT the primary
Proposition 4.2f completion. The full implementation remains draft
until all mathematical and CI obligations are discharged.
