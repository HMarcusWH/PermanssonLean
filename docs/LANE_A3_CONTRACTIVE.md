# A3 — Conditional dual invariant-law and margin robustness

**Branch:** `claude/zen-einstein-ub8zgr-a3` (PR #73, base `main` after E1/#71 merged). It
reuses E1's Hahn-decomposition TV calculus for the bounded-diameter conversion.
**Anchors:** A3.0–A3.5 in [V020_IMPLEMENTATION_INDEX.md](V020_IMPLEMENTATION_INDEX.md).
**Normative mathematics:** [integration spec](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
§4, (V20.16)–(V20.18), the survival counterexample and the TV→W₁ warning. Manuscript target: §5.4.1.

## The distance used: W₁ in Kantorovich–Rubinstein dual form

`W1DualLE μ ν c` means: for every **measurable, bounded, 1-Lipschitz** `f : Y → ℝ`,
`|∫ f dμ − ∫ f dν| ≤ c`.

- **Generality.** It is stated on an arbitrary pseudo-metric space with an arbitrary σ-algebra. There is no Polish, standard-Borel, countability or finite-state hypothesis.
- **Test class.** Measurability is part of the test class, so no Borel hypothesis is needed. Bounded tests are integrable against every finite measure.
- **Not formalized.** Kantorovich–Rubinstein duality, i.e. equality with the coupling definition of W₁, is NOT formalized. Neither is the passage from bounded to all 1-Lipschitz tests under finite first moments. All A3 theorems are statements about the dual-form bound.
- **Specification boundary.** These are dual-form analogues of (V20.17)–(V20.18), not a completed formalization of the spec's coupling-form Wasserstein assertions. A coupling-form contraction has not been proved to imply `IsW1Contraction`; that implication needs a separate metric-comparison bridge. The arbitrary measurable-space generality here does not supply KR duality. The coupling-form obligations remain OPEN.
- **Python check.** On finite real supports the dual value equals the coupling W₁. The Python suite checks this.

## Theorem-to-source crosswalk

| Anchor | Mathematical statement | Lean declaration | Module |
|---|---|---|---|
| A3.0 (calculus) | Monotonicity, symmetry, triangle, closure under limits. A pointwise kernel defect gives a mixture defect: `∀y, W₁(κ_y, η_y) ≤ δ ⇒ W₁(κ∘μ, η∘μ) ≤ δ`. An `L`-Lipschitz pushforward scales by `L`. Finite first moments give a finite bound. | `W1DualLE`, `IsKRTest`, `W1DualLE.mono`, `.symm`, `.trans`, `.of_tendsto`, `.nonneg`, `W1DualLE.comp_of_forall`, `W1DualLE.map_lipschitz`, `W1DualLE.of_integrable_dist` | `Probability/KantorovichDual.lean` |
| A3.1 | Dual analogue of (V20.17): `K π = π`, `K̃ π̃ = π̃`, `K` a uniform dual contraction with `0 ≤ ρ < 1`, and pointwise dual defect `≤ δ`, together with a finite initial dual gap, give `W1DualLE π π̃ (δ/(1−ρ))`. | `IsW1Contraction`, `invariantLaw_step`, `invariantLaw_wasserstein_le`, `ContractivePerturbation`, `ContractivePerturbation.w1_le` | `Perturbation/ContractiveOccupation.lean` |
| A3.2 | Conditional dual analogue of (V20.18): if `ψ(P_y) = F(h_#π)` for every `y ∈ B₁` and all **four** compared processes, with `h` `L_h`-Lipschitz and measurable and `F` `L_F`-Lipschitz for dual W₁, then `\|κ̃ − κ\| ≤ L_F L_h (δ₀/(1−ρ₀) + δ_J/(1−ρ_J))`. Both margins are ORIGINAL frozen constitutive margins. | `IsW1LipschitzFunctional`, `descriptorFunctional_dist_le`, `occupationMargin_robust` | same |
| A3.3 | Survival counterexample. For every `ε ∈ (0,1]`, the kernels `K = δ₀` and `K̃ = (1−ε)δ₀ + εδ₁`, realized as actual `StrategicWorldModel`s on `Unit × ℝ`, have an explicit `ContractivePerturbation` with invariant laws, finite gap, `ρ = 0` and defect `ε`. Yet `P₀(τ_B = ∞)` is `1` versus `0` for `B = {x = 0}`. | `model_invariant`, `leakPerturbation`, `bundled_survival_counterexample`, `contraction_does_not_transfer_survival` (also `fine_survivalForever`, `leak_survivalForever`, `survivalProbability_model`, `killedPow_model`) | `Perturbation/ContractiveAdversaries.lean` |
| A3.4 | TV → W₁ only with a proved diameter factor: `dist ≤ D ⇒ W₁ ≤ D·TV`. On `ℝ`, for every `ε ∈ (0,1]` and every `C`, some pair has `TV ≤ ε` but `W₁ > Cε`. | `W1DualLE.of_eventTV`, `tv_does_not_control_w1_on_real`, `tailMix` | `Probability/KantorovichTV.lean` |
| A3.5 | Existence and uniqueness of invariant laws; derivation of contraction from Doeblin/Dobrushin conditions; the ergodic bridge `ψ(P_y) = F(h_#π)`; KR duality | — | **OPEN** (hypotheses here) |

## Proof of A3.1 (fixed-point iteration)

Let `c` be any finite bound on the initial gap.

- **One step.** `W₁(π, π̃) ≤ c` implies `W₁(π, π̃) = W₁(Kπ, K̃π̃) ≤ W₁(Kπ, Kπ̃) + W₁(Kπ̃, K̃π̃) ≤ ρc + δ`. The first term uses contraction; the second uses the mixture lemma under `π̃`.
- **Iteration.** Iterating gives the bound `ρⁿ(c − L) + L` for every `n`, where `L = δ/(1−ρ)`.
- **Closure.** Since `ρⁿ → 0`, closure of the bound gives `W₁(π, π̃) ≤ L`.

No supremum of a possibly unbounded set is taken, and no completeness or fixed-point theorem is used.

## What the theorems take, and what stays a separate obligation

- **Hypotheses.** Invariance, contraction, the pointwise defect, finiteness of the initial gap (implied by finite first moments, `W1DualLE.of_integrable_dist`), Lipschitz descriptor and functional, and the factorization identity for all four processes on `B₁` are **hypotheses**.
- **Factorization identity.** The spec's alternative, "prove it from an ergodic convergence theorem", is not done here. Path-law properties are not derived from invariant laws.
- **Factorization map.** The theorem accepts `h` separately from `spec.descriptor` and `spect.descriptor`; the four supplied identities justify its use. Identifying it with a regime's predeclared descriptor is a further caller obligation when that interpretation is intended.
- **No primitive budget.** No typed primitive (A2) budget is converted into a W₁ defect. A3.4 shows why a TV budget cannot be substituted without a diameter factor.
- **Not an Exact-GR or PR statement.** A3.3 shows that an exact-survival indicator property violates the unrestricted conclusion although every A3.1 hypothesis holds. `leakPerturbation` now supplies the actual bundle, including invariance and finite gap, and `bundled_survival_counterexample` exports it alongside the survival flip. The factorization premise of A3.2 is not established for that property.

## Executable adversaries

`verification/research/test_a3_contractive.py` has 13 exact-`Fraction` tests on finite chains on the real line, where `W₁ = ∫|F_μ − F_ν|`. These are not proofs. They cover:

- **Dual form.** The dual value equals the coupling value on finite real supports.
- **A3.0.** The mixture defect bound, and Lipschitz pushforward scaling.
- **V20.17 on random contractive pairs.** These are Doeblin-type kernels `(1−θ)ν + θR_x`; most cases have a nontrivial gap.
- **The `1/(1−ρ)` factor is needed.** On slowly mixing two-state chains with fixed `δ`, the ratio `W₁(π, π̃)/δ` grows as `ρ → 1`.
- **No contraction, no bound.** With `ρ = 1` (identity kernel), every law is invariant.
- **V20.18.** On random pairs with `h = id` and `F = mean`.
- **Non-vacuous positive-margin transfer.** A deterministic fixture has `κ = 1`, `κ̃ = 4/5`, and total budget `1/5`, attaining the bound and certifying `κ̃ ≥ 4/5 > 0`. Deleting either budget term gives the false bound `1/5 ≤ 1/10`.
- **Denominator mutation.** Another deterministic margin fixture has `κ = 1/2`, `κ̃ = 5/11`, `ρ = 9/10`, and `δ = 1/100`; the correct budget `1/10` is below `κ`, while replacing `δ/(1−ρ)` by `δ` fails.
- **Factorization mutation.** Replacing the factored property by forever survival gives margins `1` versus `0` despite invariant-law budget `1/100`, explicitly defeating deletion of the four-process premise.
- **A3.3 survival.** The exact `(1−ε)ⁿ` survival recursion.
- **A3.4.** `W₁ ≤ D·TV` on bounded grids, and `TV = ε`, `W₁ = εn` on unbounded supports.

## Independent adversarial review, 17 October 2026

Reviewed source head `f757b9ef2ea62f07872eb7920b6ecdd4b13b983f` against integration spec §4 and both transfer audits. The one-step recurrence, its iteration and limit, descriptor scaling, and infimum-margin comparison are coherent under the actual encoded hypotheses. No unconditional ergodic theorem is proved: `hfac` is a conjunction of four identities on every comparison state. `ContractivePerturbation` takes invariant-law existence as data and uses a finite dual gap; finite first moments are a sufficient route to that last field, not an existence or uniqueness argument. The dual/coupling distinction remains an explicit open obligation. The survival example's previously implicit invariance/finite-gap certification is now bundled, and deterministic destructive tests address the weak random-margin coverage identified in the transition audit.

## Verification evidence

- Historical head `f757b9e`: Lean 4.34.0 / pinned mathlib compiled all four modules; all were imported by `PermanssonResearch.lean`; the focused audit allowlisted 50/50 declarations. Those receipts do not verify the new bundle declarations.
- Accepted source `a977da54057837797ab1cea163f8bcec98cddb2d`: all five workflows and a fresh independent review passed before PR #73 merged at `9cf3410e9786b68f68d93c0684613329cdc9159e`. The focused pinned build and transitive audit accepted **53/53 declarations**, and **13/13 exact rational tests passed**. Full Research run `39038951100` checked synthetic merge `11c4baace0de6025709b0cdd637e99c255a70bc6`: 4861 audited declarations, 777 tests, 384 direct imports and source-bound C10 PASS. The audit covers every top-level theorem/lemma/def/abbrev/instance/structure/inductive/class, attribute-prefixed, `noncomputable`/`protected` and non-ASCII names; anonymous instances and `private` declarations are rejected. [Acceptance record](https://github.com/HMarcusWH/PermanssonLean/pull/73#issuecomment-6234932052).
- Focused workflow: `.github/workflows/a3-contractive-smoke.yml`.
