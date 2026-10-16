# E1 — Approximate type-respecting quotients

**Branch:** `claude/zen-einstein-ub8zgr-e1`, stacked on PR #69 (it updates the
implementation index created there; no mathematical dependency on C69/C70).
**Anchors:** E1.1–E1.5 in [V020_IMPLEMENTATION_INDEX.md](V020_IMPLEMENTATION_INDEX.md).
**Normative mathematics:** [integration spec](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
§7, V20.30–V20.34; manuscript target §7.4.3 (Theorem 7.4c), after Theorem 7.4b.

## Theorem-to-source crosswalk

| Anchor | Mathematical statement | Lean declaration | Module |
|---|---|---|---|
| E1.0 (calculus) | For measurable `0 ≤ f ≤ 1`: `∫f dμ ≤ ∫f dν + TV(μ,ν)`; pushforward contraction; triangle; `TV(α⊗κ, α⊗ι) ≤ η` if kernels within `η` pointwise; `TV(α⊗κ, β⊗κ) ≤ TV(α,β)`. **No countability / standard-Borel hypothesis** (Hahn decomposition) | `lintegral_le_add_eventTotalVariation`, `abs_lintegral_toReal_sub_le_eventTotalVariation`, `eventTotalVariation_map_le`, `eventTotalVariation_triangle`, `eventTotalVariation_compProd_right_le`, `eventTotalVariation_compProd_left_le` | `Probability/EventTVCalculus.lean` |
| E1.0 (shared) | `(ρ.map f) ⊗ₘ η = (ρ ⊗ₘ η.comap f).map (Prod.map f id)` — moved here from C69 so neither lane imports the other | `compProd_map_left_eq_map_compProd_comap` | `Probability/CompProdPushforward.lean` |
| E1.1 | One-step defect `η = sup_y ‖q_#K(y,·) − K̄(q y,·)‖_TV`, for EVERY fine state; typed version through a `TypeRespectingStateCompression`; exact `KernelIntertwines` ⇒ `η = 0` | `HasQuotientDefect`, `ApproxKernelIntertwines`, `hasQuotientDefect_zero_of_intertwines`, `approxKernelIntertwines_zero_of_exact` | `Quotient/ApproxPrefix.lean` |
| E1.2 | `TV((q^{0:T})_# P_y^{K,0:T}, P_{q y}^{K̄,0:T}) ≤ min(1, Tη)` — projected fine process need not be Markov | `approxQuotient_prefix_tv_le_linear`, `approxQuotient_prefix_tv_le_min`, `approxQuotient_pathLaw_prefix_tv_le` (canonical path laws) | same |
| E1.2 (support) | Ionescu–Tulcea recursion of `finitePrefixLaw`; projection commutes with appending | `finitePrefixLaw_succ`, `prefixMap_appendLast`, `finitePrefixLaw_zero_map` | same |
| E1.3 | Effects: `\|Δ(y) − Δ̄(q y)\| ≤ L(min(1,Tη₀)+min(1,Tη_J))`; margins with `B̄₁ = q(B₁)`: same bound; positive-margin transfer both ways; frozen-family version over the label equivalence `φ` | `approxQuotient_effect_abs_le`, `approxQuotient_margin_abs_le`, `approxQuotient_fine_margin_pos_of_coarse`, `approxQuotient_coarse_margin_pos_of_fine`, `approxQuotient_family_margin_abs_le`, `approxBudget_le_linear` | `Quotient/ApproxMargin.lean` |
| E1.3 (property) | The fine property FACTORS through the compressed prefix law by construction; the coarse property is an explicit A2 `TVLipschitzPrefixProperty` | `projectedPrefixProperty`, `projectedPrefixProperty_value`, `coarsePrefixProperty_value` | same |
| E1.4 | Leakage: identity quotient on `Bool`, `K = δ_false`, `K̄_ε = (1−ε)δ_false + εδ_true`; defect ≤ ε, fine `{false}` invariant, coarse leaks with probability ε for every ε > 0 | `leaky_hasQuotientDefect`, `fine_region_invariant`, `coarse_region_leaks`, `small_defect_does_not_preserve_invariance` | `Quotient/ApproxAdversaries.lean` |
| E1.5 | Geometric bound `1 − (1−η)^T` | — | **OPEN** (needs a measurable common-mass/coupling construction; not implied by E1.2) |

## Proof of E1.2 (last-step hybrid)

`μ_{T+1} = (μ_T ⊗ K_T).map append`, and the projection commutes with appending, so
the projected fine law at `T+1` is `A = (μ_T ⊗ q_#K_T)` read through `q^{0:T}`.
With the hybrid `H = (q^{0:T}_#μ_T) ⊗ K̄_T` and the coarse law `C = ν_T ⊗ K̄_T`:
`TV(A,H) ≤ η` (same first law; kernels compared at every fine history, where
`q_#K(h_T)` and `K̄(q h_T)` are within `η` by hypothesis) and
`TV(H,C) ≤ TV(q^{0:T}_#μ_T, ν_T)` (same kernel). Hence `δ_{T+1} ≤ δ_T + η`, `δ_0 = 0`.
The coarse kernel is never applied to a fine history, the projected process is
never assumed Markov, and no fibre disintegration is used.

## Hypotheses kept independent (spec §7, conditions (ii)–(vi) of Thm 7.4b)

The Lean margin theorem takes as explicit inputs: the type-respecting compression;
`B̄₁.states = q(B₁.states)` (exact equality); both comparison sets as ORIGINAL
`ConstitutiveComparisonSet`s of their own models; separate defects `η₀` (baseline)
and `η_J` (matched intervention); property factorization (by definition of
`projectedPrefixProperty`); a frozen label equivalence for the family version.
Nothing is inferred from small TV error. Exact-GR and grounding gates of either
model are not touched and must be established independently.

## Executable adversaries

`verification/research/test_e1_approx_quotient.py` (14 exact-`Fraction` tests):
non-Markov projection (explicit history dependence) with the linear bound checked
for a grid of coarse kernels and all horizons ≤ 6; the defect as a supremum over
ALL fine states; horizon zero; exact lumpability (`η = 0` ⇒ TV 0 at every horizon);
leakage (`TV = 1 − (1−ε)^T ≤ Tε`, invariance lost); the geometric envelope observed
numerically only (E1.5 stays OPEN); margin budget V20.33–34; a non-factoring
property distinguishing exactly-lumped models; a label mismatch defeating the
budget; positive coarse margin without coarse Exact GR.

## Verification evidence (local)

- Lean 4.34.0 / pinned mathlib: all five modules compile; signatures inspected —
  no `CountableOrCountablyGenerated` or standard-Borel instance appears.
- `verification/research/e1_axiom_audit.py`: 45/45 declarations allowlisted.
- The C69 audit still passes (33/33) after moving the shared lemma.
- Focused workflow: `.github/workflows/e1-approx-quotient-smoke.yml`.
