# F1 — Multi-agent closed-loop versus opponent-locked protocols

**Branch:** `claude/zen-einstein-ub8zgr-f1`, stacked on PR #69. It updates the
implementation index created there and has no mathematical dependency on C69, C70 or E1.
**Anchors:** F1.0–F1.5 in [V020_IMPLEMENTATION_INDEX.md](V020_IMPLEMENTATION_INDEX.md).
**Normative mathematics:** [integration spec](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
§6, (V20.28)–(V20.29), destructive ledger MA1–MA3. Manuscript target: §5.4.3.

## Scope

- This lane formalizes a declared **two-player conditional-product subclass**. It does not claim that games in general have independent action and update kernels.
- **Player 1 is the only treated player formalized.** Treating player 2, and `n` players, are OPEN (F1.5).
- Given the current joint state, the joint action law is a product. So a state-conditional joint law such as the perfectly correlated `correlatedLaw` on `Bool × Bool` is not produced by any `TwoPlayerGenerator` (MA3, Lean).
- Correlation mediated by a shared `S₀` coordinate, for example a public coin drawn by `U₀`, **is** representable. The Python suite checks this.

## Declared kernels and genuinely opponent-locked anchors

The spec asks J_OL to install a "frozen, ex-ante declared non-reactive anchor".
The broader declared-kernel family does not itself satisfy that requirement.
The distinction below is essential; the broader counterexample is not MA2.

1. **Broader declared-kernel family: `protocolFamily G P r anchors`.**
   - Any declared anchor kernel on the full joint state is admissible if it is in the menu.
   - Non-reactivity is **not enforced** by this family; it is the menu's responsibility.
   - If the menu contains the baseline opponent, the OL label carries the CL generator (`openLoop_self`).
   - The retained world-feedback counterexample uses this family and does **not** fulfill the strict opponent-locked MA2 requirement.
2. **Local factorization: `strictAnchors anchors`.**
   - `IsStrictlyNonReactive a` requires the anchor's action kernel to factor through `(s₀, s₂)`.
   - Its update kernel must factor through `((s₀, s₂), a₂)`.
   - The anchor therefore never reads player 1's private state, the world state or player 1's action.
   - `IsStrictlyNonReactive.action_eq` and `.update_eq` certify equality on equal keys.
   - This condition alone permits indirect response through an endogenous `S₀`.
3. **Autonomous locked sub-menu: `opponentLockedAnchors G anchors`.**
   - Requires local factorization **and** `IsExogenousCommon G`: `U₀` factors through the old `S₀` alone.
   - The condition excludes a common-state channel such as `s₀' = a₁`; it is a sufficient autonomous subclass, not a universal definition of all possible non-reactive protocols.
   - Both CL and OL preserve common exogeneity (`IsExogenousCommon.closedLoop`, `.openLoop`).
   - The Boolean witness's `strictFamily` uses this sub-menu. `gen_common_exogenous` proves its common process exogenous, rather than leaving an obligation implicit.

Protocols never change `U₀` or `P`. A nonstationary, clocked anchor therefore needs its clock in a state coordinate the protocol can update: either the **baseline** `S₀`/`U₀` (the Python clock test builds it that way), or the anchor's **own** `S₂` through the anchor's own update, when `S₂` can hold the clock (at the cost of `S₂`'s baseline meaning).

Typed action **feasibility** of anchors is not encoded in Lean. It is a property the menu must satisfy. The Python suite has a separate feasibility toy, independent of the F1.4 witness, which has no feasibility constraint.

## Theorem-to-source crosswalk

| Anchor | Mathematical statement | Lean declaration | Module |
|---|---|---|---|
| F1.0 | If `K(y,·) = δ_{f y}` for all `y`, the canonical path law from `δ_y` is `δ_{(f^n y)_n}`. This holds on arbitrary measurable spaces, by frozen uniqueness. A deterministic `α → P → U` on singleton-measurable `A` and `X` has a Dirac induced kernel. | `pathLaw_dirac_of_deterministic`, `inducedKernel_eq_dirac_of_deterministic`, `dirac_compProd_eq_map`, `detOrbit` | `StrategicWorld/DeterministicOrbit.lean` |
| F1.1 | (V20.28) with `n = 2`: `S = S₀ × (S₁ × S₂)`, `α = α₁ ⊗ α₂`, `U = U₀ ⊗ (U₁ ⊗ U₂)`, common `P`. These assemble a frozen `StrategicGenerator` and `StrategicWorldModel`. | `TwoPlayerGenerator`, `toGenerator`, `toModel`, `toGenerator_action_apply`, `toGenerator_update_apply`, `toModel_world` | `MultiAgent/ProductGame.lean` |
| F1.2 | `J_CL` replaces player 1 only. `J_OL` also installs a menu anchor. Both are admissible strategic interventions of one frozen family, and `P` is held fixed. Admissible ⇔ the CL generator, or an OL generator with a menu anchor. The autonomous locked sub-menu requires local factorization and exogenous `U₀`. | `closedLoop`, `openLoop`, `protocolFamily`, `closedLoopIntervention`, `openLoopIntervention`, `protocol_world_eq`, `protocol_admissible_cases`, `openLoop_self`, `IsStrictlyNonReactive`, `IsExogenousCommon`, `opponentLockedAnchors` | `MultiAgent/Protocols.lean` |
| F1.3 | (V20.29): `\|Δ₁ − Δ₂\| ≤ A ≤ Δ₁ + Δ₂`. `A = Δ₁` if `Δ₂ = 0`, and `A = Δ₂` if `Δ₁ = 0`. Specialized to CL/OL. A uniform gap `A ≤ G` on `B₁` gives `\|κ₁ − κ₂\| ≤ G` for the ORIGINAL frozen margins. No direction is asserted. | `protocolGap`, `abs_effect_sub_le_protocolGap`, `protocolGap_le_effect_add`, `protocolGap_eq_of_effect_zero`, `protocolGap_eq_of_effect_zero_left`, `abs_closedLoop_sub_openLoop_le_adapt`, `abs_constitutiveMargin_sub_le_of_protocolGap` | `MultiAgent/AdaptationBound.lean` |
| F1.4 | MA1 and agreement in an autonomous strict family; MA1 locus; broader state-feedback counterexample; scoped strict MA2 obstruction; MA3. **Strict MA2 remains unfulfilled.** | see the witness section below | `MultiAgent/ProtocolWitnesses.lean` |
| F1.5 | Treated player 2; `n` players; a typed clock construction; typed feasibility; causal mediation | — | **OPEN** / not claimed |

## The Boolean witness

- **State and actions.** `S₀ = Unit`, `S₁ = S₂ = Bool` (each player records its own last action), `X = Bool`, `Aᵢ = Bool` (`true` = extract).
- **World.** The common `P` is `x' = a₁`.
- **Baseline.** Player 1 repeats its last action. The opponent copies player 1's last action, so it is reactive and not strictly non-reactive (`baselineOpponent_not_strict`).
- **Replacement.** Player 1 always extracts.
- **Property.** `ψ(P) = P(s₂(Y₂) = true)`: the opponent's action taken at time 1, recorded in `s₂` at time 2. The metric is `|·|`.
- **Start.** `y₀ = (((), (false, false)), false)`.
- **Computation.** All values come from `gen_value`, through `pathLaw_dirac_of_deterministic` (frozen uniqueness).

| Protocol | Anchor | Strict? | `ψ` | Lean value theorem |
|---|---|---|---|---|
| baseline | — | — | 0 | `baseline_value` |
| CL | (opponent responds) | — | 1 | `closedLoopStrict_value`, `closedLoop_value` |
| OL | never extract (`anchorConst`) | yes | 0 | `openLoopConstStrict_value`, `openLoopConst_value` |
| OL | always extract (`anchorExtract`) | yes | 1 | `openLoopExtractStrict_value` |
| OL | read world state (`anchorWorld`) | **no** | 1 | `openLoopWorld_value` |

- **MA1 (`closedLoop_ne_openLoop`, strict family).** `Δ_CL = 1`, `Δ_OL = 0`, `A = 1`.
- **MA1 locus (`protocols_separate_after_reachable_state`).** The CL and baseline path laws from `y₀` are the Dirac masses at the stated orbits (conjuncts of the theorem). At `y₀` the CL opponent and the strict anchor play the same law. At the CL state at time 1, which is **not** on the baseline orbit, they play different laws. The equality of the two property values at horizon 1 is checked in Python only.
- **Agreement (`closedLoop_eq_openLoopExtract`, strict family).** The gap is 0.
- **State-feedback agreement (`closedLoop_eq_openLoopWorld`).** This is the same equality for `anchorWorld`. That anchor reads `x`, which equals player 1's last action, so it is not opponent-locked in the strict sense.
- **Broader state-feedback counterexample (`declared_anchors_agree_on_support_but_openLoop_differs`), not strict MA2.**
  - The baseline path law from `y₀` is the Dirac mass at its orbit (a conjunct of the theorem), and the strict `anchorConst` and the state-feedback `anchorWorld` **both coincide with the baseline opponent**: action kernels at every state of that orbit, and update kernels everywhere.
  - Yet their OL values differ (0 vs 1).
  - So agreement with the baseline on baseline support does not identify a declared state-feedback anchor off support.
  - The theorem also records which of the two anchors is strict.
- **Strict MA2 obstruction (`strict_recording_anchors_pathLaw_eq`).**
  - Scope: the stated Boolean toy, `S₀ = Unit`, deterministic action functions, own-action recording updates, common world `x' = a₁`, same start `y₀`.
  - For **any** treated action function `a₁`, any two strictly non-reactive recording anchors with action `false` at `y₀` yield **identical full canonical path laws**. In this toy that is precisely action agreement at the sole baseline-reachable state; their updates already coincide with the baseline everywhere.
  - `const_opponent_orbit_s2` proves that the anchor's reachable own state stays `false`. Strictness transports baseline action agreement to every counterfactual state with that same own key. `strict_recording_anchor_orbit_eq` then identifies the whole orbit, and `strict_recording_anchor_pathLaw_eq` identifies its actual canonical path law.
  - Distinct anchor functions may differ at the unreachable own-state key `s₂ = true`. Such off-support differences cannot be exposed by player 1 in this autonomous toy.
  - This is **not** an impossibility theorem for arbitrary stochastic models or all possible anchor notions. No strict MA2 witness has been proved, and the integration spec is unchanged. The strict MA2 requirement remains **OPEN / unfulfilled**; substituting another strict recording anchor into this toy cannot supply it.
- **MA3 (`correlated_generator_not_product`).** A generator whose joint action law at some state **equals** `correlatedLaw` is not the generator of any `TwoPlayerGenerator`. Behind it is `correlatedLaw_ne_prod`: `correlatedLaw` is not `ν₁ ⊗ ν₂` for any measures, with s-finite `ν₂`.

## What is NOT claimed

- **V20.29 is a metric identity on property values.** It holds for any two admissible strategic interventions of one family. It is **not** an identified direct/indirect causal mediation effect, because OL also intervenes on the opponent. A causal reading needs separately defended modularity, observation/support, anchor and identification assumptions. None are formalized.
- **Direction is separate.** The sign of `Δ_CL − Δ_OL` is not determined by `A`. The margin theorem bounds `|κ_CL − κ_OL|` only by a uniform gap.
- **Non-reactivity is not enforced by the declared-kernel family.** `strictAnchors` alone does not rule out endogenous-common-state response; `opponentLockedAnchors` adds an explicit sufficient exogeneity condition.
- **Strict MA2 is unfulfilled.** The broader state-feedback example is retained under a renamed declaration and cannot be cited as completion of that requirement.
- **No feasibility, no clock construction in Lean.** Anchor feasibility and a typed clock construction are not formalized.
- **B2.1 is not used.** V20.29 is proved directly from the metric triangle.

## Executable adversaries

`verification/research/test_f1_multiagent_protocols.py` contains 17 exact-`Fraction` tests on finite two-player games. They are cross-checks, not proofs. Each Lean-mirroring test names the theorem it mirrors in its docstring. They cover:

- **Strictness classification.** Strict anchors are recognized, and the world-reading and baseline opponents are rejected.
- **MA1.** The locus check: equal opponent laws at `y₀`, the off-orbit state at time 1, horizon-1 equality and horizon-2 separation.
- **Agreement.** Both the strict and the state-feedback variant.
- **Broader state-feedback counterexample.** Both anchors are compared with the **baseline** opponent's action and update laws on support; the world-reading one is explicitly rejected as strict. The off-support state is shown reachable under CL and under each OL run.
- **Strict obstruction.** Exhausts all 256 deterministic treated action functions and both strict own-state action functions agreeing with baseline. The anchors differ at `s₂ = true`, yet their full length-6 path laws coincide. Removing baseline agreement makes the full laws differ, demonstrating an essential hypothesis. A separate non-deterministic finite fixture cross-checks full-law equality without promoting the Lean scope.
- **Common-state loophole.** A separate fixture has `s₀' = a₁`. Two locally strict anchors agree with baseline yet yield OL values 0 and 1. `IsExogenousCommon`'s finite counterpart rejects this common process; an autonomous public clock passes. This fixture cannot be promoted as an opponent-locked MA2 witness.
- **MA3.** A non-product check (a Bool×Bool law is a product iff it equals the product of its marginals); misrepresentation of coordination by the product of marginals (`1` vs `1/2`); and **shared-source correlation through `S₀`**, which gives coordination 1 with every kernel in product form.
- **Feasibility (separate toy).** The menu builder keeps only anchors feasible on every OL-reachable state. Both players' actions under baseline, CL and every kept OL run are feasible. The excluded anchor is not a protocol.
- **Protocol membership predicate (`is_protocol`, mirroring `protocol_admissible_cases`).** It accepts CL and OL. It rejects an edit of `P` (which also changes the OL value `1 → 0`), a non-menu anchor, a menu action paired with a non-menu update, a wrong player-1 replacement, a correlated joint-action override, and a clock added by editing `U₀` inside the intervention. Laws are compared as measures (explicit zero atoms dropped).
- **`openLoop_self`.** Checked directly, and on random games.
- **Clock.** The clock is declared in the baseline. `z₀`, `z_CL` and `z_OL` are unchanged. The clock-only anchor is strict and admissible. Its projected run visits the same unaugmented state at `t = 1` and `t = 2` with different successors, so no stationary kernel on the unaugmented state reproduces it.
- **V20.29 on 60 random games × 8 states.** The two-sided bound and the equality clauses are metric identities (arithmetic sanity checks only). The checks that can fail are: the path-law value equals an independent state-distribution iteration, `openLoop_self`, and non-degeneracy (OL ≠ CL on many sampled states; an equality case with a nonzero effect is hit).
- **Direction vs gap.** For the same protocol pair, the sign of `Δ_CL − Δ_OL` takes both values, at states with the **same** gap `A`. On `B = {s₁ = false}` the margins differ (1 vs 0), and the uniform gap bounds their difference with equality.

Mutation checks: replacing the strictness predicate by `True`, dropping the `P`/`U₀` comparison in `is_protocol`, or making `closed_loop` change the opponent each make tests fail; the update half of the strictness predicate and the player-1/anchor-update halves of `is_protocol` have dedicated negative fixtures.

## Verification evidence

- The source head before this correction, `b7e83c326af6b3de2babbe65b4b4afe2256cf300`, had five successful CI workflows and a 111-declaration allowlisted axiom audit. Those checks do not certify the correction.
- The corrected exact rational suite passes **17/17** tests locally. Pinned Lean compilation, updated declaration audit and source-bound CI must be rerun on the corrected head before acceptance.
- All five modules remain directly imported by `PermanssonResearch.lean`; no new module was added. The existing audit covers top-level theorem, lemma, def, abbrev, instance, structure, inductive and class declarations, including attribute-prefixed, `noncomputable`, `protected` and non-ASCII names; it rejects anonymous instances and `private` declarations.
- Focused workflow: `.github/workflows/f1-multiagent-protocols-smoke.yml`.
