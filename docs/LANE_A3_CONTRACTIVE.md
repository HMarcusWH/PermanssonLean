# A3 — Contractive long-run W₁ robustness

**Branch:** `claude/zen-einstein-ub8zgr-a3`, stacked on the E1 branch (PR #71). It
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
- **Python check.** On finite real supports the dual value equals the coupling W₁. The Python suite checks this.

## Theorem-to-source crosswalk

| Anchor | Mathematical statement | Lean declaration | Module |
|---|---|---|---|
| A3.0 (calculus) | Monotonicity, symmetry, triangle, closure under limits. A pointwise kernel defect gives a mixture defect: `∀y, W₁(κ_y, η_y) ≤ δ ⇒ W₁(κ∘μ, η∘μ) ≤ δ`. An `L`-Lipschitz pushforward scales by `L`. Finite first moments give a finite bound. | `W1DualLE`, `IsKRTest`, `W1DualLE.mono`, `.symm`, `.trans`, `.of_tendsto`, `.nonneg`, `W1DualLE.comp_of_forall`, `W1DualLE.map_lipschitz`, `W1DualLE.of_integrable_dist` | `Probability/KantorovichDual.lean` |
| A3.1 | (V20.17): `K π = π`, `K̃ π̃ = π̃`, `K` a uniform W₁ contraction with `0 ≤ ρ < 1`, and `sup_y W₁(K_y, K̃_y) ≤ δ`, together with a finite initial gap, give `W₁(π, π̃) ≤ δ/(1−ρ)`. | `IsW1Contraction`, `invariantLaw_step`, `invariantLaw_wasserstein_le`, `ContractivePerturbation`, `ContractivePerturbation.w1_le` | `Perturbation/ContractiveOccupation.lean` |
| A3.2 | (V20.18): if `ψ(P_y) = F(h_#π)` for every `y ∈ B₁` and all **four** compared processes, with `h` `L_h`-Lipschitz and measurable and `F` `L_F`-Lipschitz for dual W₁, then `\|κ̃ − κ\| ≤ L_F L_h (δ₀/(1−ρ₀) + δ_J/(1−ρ_J))`. Both margins are ORIGINAL frozen constitutive margins. | `IsW1LipschitzFunctional`, `descriptorFunctional_dist_le`, `occupationMargin_robust` | same |
| A3.3 | Survival counterexample. For every `ε ∈ (0,1]`, the kernels `K = δ₀` and `K̃ = (1−ε)δ₀ + εδ₁`, realized as actual `StrategicWorldModel`s on `Unit × ℝ`, are both W₁ contractions with `ρ = 0` and have defect `≤ ε`. Yet `P₀(τ_B = ∞)` is `1` versus `0` for `B = {x = 0}`. | `contraction_does_not_transfer_survival` (also `fine_survivalForever`, `leak_survivalForever`, `survivalProbability_model`, `killedPow_model`) | `Perturbation/ContractiveAdversaries.lean` |
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
- **No primitive budget.** No typed primitive (A2) budget is converted into a W₁ defect. A3.4 shows why a TV budget cannot be substituted without a diameter factor.
- **Not an Exact-GR or PR statement.** A3.3 shows that an exact-survival indicator property violates the conclusion although every A3.1 hypothesis holds.

## Executable adversaries

`verification/research/test_a3_contractive.py` has 10 exact-`Fraction` tests on finite chains on the real line, where `W₁ = ∫|F_μ − F_ν|`. These are not proofs. They cover:

- **Dual form.** The dual value equals the coupling value on finite real supports.
- **A3.0.** The mixture defect bound, and Lipschitz pushforward scaling.
- **V20.17 on random contractive pairs.** These are Doeblin-type kernels `(1−θ)ν + θR_x`; most cases have a nontrivial gap.
- **The `1/(1−ρ)` factor is needed.** On slowly mixing two-state chains with fixed `δ`, the ratio `W₁(π, π̃)/δ` grows as `ρ → 1`.
- **No contraction, no bound.** With `ρ = 1` (identity kernel), every law is invariant.
- **V20.18.** On random pairs with `h = id` and `F = mean`.
- **A3.3 survival.** The exact `(1−ε)ⁿ` survival recursion.
- **A3.4.** `W₁ ≤ D·TV` on bounded grids, and `TV = ε`, `W₁ = εn` on unbounded supports.

## Verification evidence (local)

- Lean 4.34.0 / pinned mathlib: all four modules compile and are imported by `PermanssonResearch.lean`.
- `verification/research/a3_axiom_audit.py`: 50/50 declarations allowlisted (top-level theorem/lemma/def/abbrev/instance/structure/inductive/class, attribute-prefixed, `noncomputable`/`protected` and non-ASCII names; anonymous instances and `private` declarations are rejected).
- Focused workflow: `.github/workflows/a3-contractive-smoke.yml`.
