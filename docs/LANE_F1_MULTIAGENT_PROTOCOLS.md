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

## Two readings of "non-reactive anchor"

The spec asks J_OL to install a "frozen, ex-ante declared non-reactive anchor".
Lean makes both readings explicit.

1. **Declared-kernel reading: `protocolFamily G P r anchors`.**
   - Any declared anchor kernel on the full joint state is admissible if it is in the menu.
   - Non-reactivity is **not enforced** by this family; it is the menu's responsibility.
   - If the menu contains the baseline opponent, the OL label carries the CL generator (`openLoop_self`).
   - MA2 needs this reading: there, one anchor reads the world state, which the intervention changes.
2. **Strict reading: `protocolFamily G P r (strictAnchors anchors)`.**
   - `IsStrictlyNonReactive a` requires the anchor's action kernel to factor through `(s₀, s₂)`.
   - Its update kernel must factor through `((s₀, s₂), a₂)`.
   - The anchor therefore never reads player 1's private state, the world state or player 1's action.
   - Caveat: `S₀` is updated by the common `U₀`, which may read player 1's action. Exogeneity of `S₀` is a separate modelling obligation.

Protocols never change `U₀` or `P`. A nonstationary, clocked anchor therefore needs the clock declared in the **baseline** `S₀`/`U₀`; the Python clock test builds it that way.

Typed action **feasibility** of anchors is not encoded in Lean. It is a property the menu must satisfy. The Python suite has a separate feasibility toy, independent of the F1.4 witness, which has no feasibility constraint.

## Theorem-to-source crosswalk

| Anchor | Mathematical statement | Lean declaration | Module |
|---|---|---|---|
| F1.0 | If `K(y,·) = δ_{f y}` for all `y`, the canonical path law from `δ_y` is `δ_{(f^n y)_n}`. This holds on arbitrary measurable spaces, by frozen uniqueness. A deterministic `α → P → U` on singleton-measurable `A` and `X` has a Dirac induced kernel. | `pathLaw_dirac_of_deterministic`, `inducedKernel_eq_dirac_of_deterministic`, `dirac_compProd_eq_map`, `detOrbit` | `StrategicWorld/DeterministicOrbit.lean` |
| F1.1 | (V20.28) with `n = 2`: `S = S₀ × (S₁ × S₂)`, `α = α₁ ⊗ α₂`, `U = U₀ ⊗ (U₁ ⊗ U₂)`, common `P`. These assemble a frozen `StrategicGenerator` and `StrategicWorldModel`. | `TwoPlayerGenerator`, `toGenerator`, `toModel`, `toGenerator_action_apply`, `toGenerator_update_apply`, `toModel_world` | `MultiAgent/ProductGame.lean` |
| F1.2 | `J_CL` replaces player 1 only. `J_OL` also installs a menu anchor. Both are admissible strategic interventions of one frozen family, and `P` is held fixed. Admissible ⇔ the CL generator, or an OL generator with a menu anchor. The strict reading is available as a sub-menu. | `closedLoop`, `openLoop`, `protocolFamily`, `closedLoopIntervention`, `openLoopIntervention`, `protocol_world_eq`, `protocol_admissible_cases`, `openLoop_self`, `IsStrictlyNonReactive`, `IsStrictlyNonReactive.action_eq`, `strictAnchors` | `MultiAgent/Protocols.lean` |
| F1.3 | (V20.29): `\|Δ₁ − Δ₂\| ≤ A ≤ Δ₁ + Δ₂`. `A = Δ₁` if `Δ₂ = 0`, and `A = Δ₂` if `Δ₁ = 0`. Specialized to CL/OL. A uniform gap `A ≤ G` on `B₁` gives `\|κ₁ − κ₂\| ≤ G` for the ORIGINAL frozen margins. No direction is asserted. | `protocolGap`, `abs_effect_sub_le_protocolGap`, `protocolGap_le_effect_add`, `protocolGap_eq_of_effect_zero`, `protocolGap_eq_of_effect_zero_left`, `abs_closedLoop_sub_openLoop_le_adapt`, `abs_constitutiveMargin_sub_le_of_protocolGap` | `MultiAgent/AdaptationBound.lean` |
| F1.4 | MA1 (strict family), MA1 locus, agreement (strict family, plus a state-feedback variant), MA2, MA3 | see the witness section below | `MultiAgent/ProtocolWitnesses.lean` |
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
- **MA1 locus (`protocols_separate_after_reachable_state`).** At `y₀` the CL opponent and the strict anchor play the same law. At the CL state at time 1, which is **not** on the baseline orbit, they play different laws. The equality of the two property values at horizon 1 is checked in Python only.
- **Agreement (`closedLoop_eq_openLoopExtract`, strict family).** The gap is 0.
- **State-feedback agreement (`closedLoop_eq_openLoopWorld`).** This is the same equality for `anchorWorld`. That anchor reads `x`, which equals player 1's last action, so it is not opponent-locked in the strict sense.
- **MA2 (`anchors_agree_on_support_but_openLoop_differs`).**
  - The strict `anchorConst` and the state-feedback `anchorWorld` **both coincide with the baseline opponent**: action kernels at every baseline-reachable state, and update kernels everywhere.
  - Yet their OL values differ (0 vs 1).
  - So agreement with the baseline on baseline support does not identify the anchor off support.
  - The theorem also records which of the two anchors is strict.
- **MA3 (`correlated_generator_not_product`).** A generator whose joint action law at some state **equals** `correlatedLaw` is not the generator of any `TwoPlayerGenerator`. Behind it is `correlatedLaw_ne_prod`: `correlatedLaw` is not `ν₁ ⊗ ν₂` for any measures, with s-finite `ν₂`.

## What is NOT claimed

- **V20.29 is a metric identity on property values.** It holds for any two admissible strategic interventions of one family. It is **not** an identified direct/indirect causal mediation effect, because OL also intervenes on the opponent. A causal reading needs separately defended modularity, observation/support, anchor and identification assumptions. None are formalized.
- **Direction is separate.** The sign of `Δ_CL − Δ_OL` is not determined by `A`. The margin theorem bounds `|κ_CL − κ_OL|` only by a uniform gap.
- **Non-reactivity is not enforced by the declared-kernel family.** The strict family still leaves the exogeneity of `S₀` as an obligation.
- **No feasibility, no clock construction in Lean.** Anchor feasibility and a typed clock construction are not formalized.
- **B2.1 is not used.** V20.29 is proved directly from the metric triangle.

## Executable adversaries

`verification/research/test_f1_multiagent_protocols.py` contains 14 exact-`Fraction` tests on finite two-player games. They are cross-checks, not proofs. Each Lean-mirroring test names the theorem it mirrors in its docstring. They cover:

- **Strictness classification.** Strict anchors are recognized, and the world-reading and baseline opponents are rejected.
- **MA1.** The locus check: equal opponent laws at `y₀`, the off-orbit state at time 1, horizon-1 equality and horizon-2 separation.
- **Agreement.** Both the strict and the state-feedback variant.
- **MA2.** Both anchors are compared with the **baseline** opponent's action and update laws on support. The off-support state is shown reachable under CL.
- **MA3.** An exact non-product argument; misrepresentation of coordination by the product of marginals (`1` vs `1/2`); and **shared-source correlation through `S₀`**, which gives coordination 1 with every kernel in product form.
- **Feasibility (separate toy).** The menu builder keeps only anchors feasible on every OL-reachable state. Baseline and CL are feasible. The excluded anchor is not a protocol.
- **Protocol membership predicate (`is_protocol`, mirroring `protocol_admissible_cases`).** It accepts CL and OL, rejects an edit of `P` (which also changes the OL value `1 → 0`), rejects a non-menu anchor, and rejects a clock added by editing `U₀` inside the intervention.
- **`openLoop_self`.** Checked directly, and on random games.
- **Clock.** The clock is declared in the baseline. `z₀`, `z_CL` and `z_OL` are unchanged. The clock-only anchor is strict and admissible. Its projected run visits the same unaugmented state at `t = 1` and `t = 2` with different successors, so no stationary kernel on the unaugmented state reproduces it.
- **V20.29 on 60 random games × 8 states.** The two-sided bound is a metric identity. The substantive checks are the equality clauses `A = Δ_CL` when `Δ_OL = 0` (and conversely) and `openLoop_self`.
- **Direction vs gap.** For the same protocol pair, the sign of `Δ_CL − Δ_OL` takes both values. On `B = {s₁ = false}` the margins differ (1 vs 0), and the uniform gap bounds their difference with equality.

The tests were mutation-checked. Breaking the strictness predicate, the protocol-membership predicate or `closed_loop` makes tests fail.

## Verification evidence (local)

- Lean 4.34.0 with pinned mathlib: all five modules compile, and `PermanssonResearch.lean` imports them directly.
- `verification/research/f1_axiom_audit.py`: **111** declarations, all allowlisted (98 with allowlisted axioms, 13 axiom-free). It covers top-level theorem, lemma, def, abbrev, instance, structure, inductive and class declarations, including attribute-prefixed, `noncomputable`, `protected` and non-ASCII names. It rejects anonymous instances and `private` declarations.
- Focused workflow: `.github/workflows/f1-multiagent-protocols-smoke.yml`.
