# F1 — Multi-agent closed-loop versus opponent-locked protocols

**Branch:** `claude/zen-einstein-ub8zgr-f1`, stacked on PR #69 (it updates the
implementation index created there; no mathematical dependency on C69/C70/E1).
**Anchors:** F1.0–F1.5 in [V020_IMPLEMENTATION_INDEX.md](V020_IMPLEMENTATION_INDEX.md).
**Normative mathematics:** [integration spec](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
§6, (V20.28)–(V20.29), destructive ledger MA1–MA3; manuscript target §5.4.3.

## Scope

This lane covers a declared **two-player conditional-product subclass**. It does
not claim that games in general have independent action and update kernels. The
`n`-player statement is the same algebra, but only `n = 2` is formalized (F1.5
OPEN). Correlated action models lie outside the subclass, and MA3 is a Lean
theorem showing they cannot be represented by it.

## Theorem-to-source crosswalk

| Anchor | Mathematical statement | Lean declaration | Module |
|---|---|---|---|
| F1.0 | If `K(y,·) = δ_{f y}` for all `y`, the canonical path law from `δ_y` is `δ_{(f^n y)_n}`. Holds on arbitrary measurable spaces, by frozen uniqueness. A deterministic `α → P → U` on singleton-measurable `A`, `X` has a Dirac induced kernel. | `pathLaw_dirac_of_deterministic`, `inducedKernel_eq_dirac_of_deterministic`, `dirac_compProd_eq_map`, `detOrbit` | `StrategicWorld/DeterministicOrbit.lean` |
| F1.1 | (V20.28), `n = 2`: `S = S₀ × (S₁ × S₂)`, `α = α₁ ⊗ α₂`, `U = U₀ ⊗ (U₁ ⊗ U₂)`, common `P`. This gives a frozen `StrategicGenerator` / `StrategicWorldModel`. | `GameState`, `PlayerOneMechanism`, `PlayerTwoMechanism`, `TwoPlayerGenerator`, `toGenerator`, `toModel`, `toGenerator_action_apply`, `toGenerator_update_apply`, `toModel_world` | `MultiAgent/ProductGame.lean` |
| F1.2 | `J_CL` replaces player 1 only, so the opponent's kernels stay as they are and respond to the counterfactual history. `J_OL` also installs a frozen anchor from an ex-ante declared menu. Both are admissible strategic interventions of one frozen family. `P` is held fixed. Admissible ⇔ the CL generator, or an OL generator with a menu anchor. | `closedLoop`, `openLoop`, `Protocol`, `protocolFamily`, `closedLoopIntervention`, `openLoopIntervention`, `closedLoop_apply`, `openLoop_apply`, `protocol_world_eq`, `protocol_admissible_cases`, `openLoop_self` | `MultiAgent/Protocols.lean` |
| F1.3 | (V20.29): `\|Δ₁ − Δ₂\| ≤ A ≤ Δ₁ + Δ₂`. `A = Δ₁` if `Δ₂ = 0`, and `A = Δ₂` if `Δ₁ = 0`. Specialized to CL/OL. A uniform gap `A ≤ G` on `B₁` gives `\|κ₁ − κ₂\| ≤ G` for the ORIGINAL frozen margins. | `protocolGap`, `abs_effect_sub_le_protocolGap`, `protocolGap_le_effect_add`, `protocolGap_eq_of_effect_zero`, `protocolGap_eq_of_effect_zero_left`, `abs_closedLoop_sub_openLoop_le_adapt`, `abs_constitutiveMargin_sub_le_of_protocolGap` | `MultiAgent/AdaptationBound.lean` |
| F1.4 | MA1, agreement, MA2 on a typed Boolean commons toy; MA3 (correlated ≠ product) | `closedLoop_ne_openLoop`, `closedLoop_eq_openLoopWorld`, `anchors_agree_on_support_but_openLoop_differs`, `correlatedLaw_ne_prod`, `correlated_generator_not_product` | `MultiAgent/ProtocolWitnesses.lean` |
| F1.5 | `n` players; typed clock construction; causal mediation | — | **OPEN** / not claimed |

## The Boolean witness

- **Spaces.** `S₀ = Unit`, `S₁ = S₂ = Bool` (each player records its own last action), `X = Bool`, `Aᵢ = Bool` (`true` = extract).
- **World kernel.** The common `P` is `x' = a₁`.
- **Baseline.** Player 1 repeats its last action. The opponent copies player 1's last action, so it is reactive.
- **Declared replacement.** Player 1 always extracts.
- **Property.** `ψ(P) = P(opponent extracts at time 2)`, with metric `|·|`.
- **Start.** `y₀ = (((), (false, false)), false)`.

All values below are computed exactly through `pathLaw_dirac_of_deterministic` (frozen uniqueness).

| Protocol | anchor | `ψ` | effect |
|---|---|---|---|
| baseline | — | 0 | — |
| CL | (opponent responds) | 1 | `Δ_CL = 1` |
| OL | never extract | 0 | `Δ_OL = 0` |
| OL | read world state `x` | 1 | `Δ_OL = 1` |

- **MA1.** `A = 1 = Δ_CL`. The protocols separate only after the intervention-reachable state where player 1 has extracted.
- **Agreement.** The world-reading anchor gives CL = OL.
- **MA2.** The two anchors have identical action kernels at every baseline-reachable state (the baseline orbit is constant at `y₀`) and identical update kernels, yet their OL values differ. Baseline agreement does not identify the anchor off support.

## What the theorems take, and what is NOT claimed

- V20.29 holds for **any** two admissible strategic interventions of one frozen family and any metric property space. It is a metric identity on property values.
- **Not mediation.** The bounds are not identified direct/indirect causal mediation effects: OL also intervenes on the opponent's mechanism. A causal response-channel reading needs separately defended modularity, observation/support, anchor and identification assumptions. None of these are formalized.
- **Direction is separate.** The sign of `Δ_CL − Δ_OL` is not determined by `A`. The margin theorem bounds `|κ_CL − κ_OL|` only by a uniform gap.
- **Anchor menu.** The menu is declared ex ante, and admissibility checks membership only. Action feasibility for anchors is the application's job; it is encoded in the menu, and the Python suite gives a rejection witness.
- **Stationary anchors.** Anchors are stationary kernels on the joint state. A time-dependent anchor needs a clock declared in `S₀`; the Python suite shows a time-dependent anchor that no stationary kernel on the unaugmented state can reproduce.
- **Fixed `P`.** `P` is fixed by the frozen strategic-intervention grammar (`protocol_world_eq`). A "protocol" that edits `P` is not in the family.
- **B2.1 is not used.** V20.29 compares two intervened outputs and is proved directly.

## Executable adversaries

`verification/research/test_f1_multiagent_protocols.py` has 11 exact-`Fraction` tests on finite two-player games. These are cross-checks, not proofs. They cover the spec §6 test list:

- **Response vs frozen (MA1).** Includes that the separation needs an intervention-reachable state: horizon 1 agrees, horizon 2 differs.
- **CL = OL** for the world-reading anchor.
- **Off-support anchors (MA2).** Baseline-agreeing anchors that differ off support.
- **Correlated actions (MA3).** A correlated law is not a product on a `1/20` grid, and the product of its marginals misrepresents the coordination probability (`1` vs `1/2`).
- **Infeasible anchor.** An anchor using an infeasible action is rejected.
- **Changing `P`.** An edited `P` changes the OL value (`1` → `0`), so it is not a protocol.
- **Clock.** A time-dependent anchor needs a clock state (identical states at `t = 1, 2` require different actions; a clock in `S₀` makes it stationary).
- **V20.29 on random games.** Both bounds checked on 60 random games × 8 states, horizon 3.
- **Direction vs gap.** The sign of `Δ_CL − Δ_OL` takes both values across states, while the uniform gap bounds the margin difference.

## Verification evidence (local)

- Lean 4.34.0 with pinned mathlib: all five modules compile, and `PermanssonResearch.lean` imports them directly.
- `verification/research/f1_axiom_audit.py` covers every theorem/lemma/def/abbrev/instance, including attribute-prefixed and non-ASCII names. It rejects anonymous instances. The count is printed by the script; see the PR.
- Focused workflow: `.github/workflows/f1-multiagent-protocols-smoke.yml`.
