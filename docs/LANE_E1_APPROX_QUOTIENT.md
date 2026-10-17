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
| E1.1 | One-step defect as an UPPER-BOUND predicate `∀ y, ‖q_#K(y,·) − K̄(q y,·)‖_TV ≤ η`, for EVERY fine state (the spec's `sup_y` is the least such `η`; the supremum is not itself defined); typed version through a `TypeRespectingStateCompression`; exact `KernelIntertwines` ⇒ `η = 0` | `HasQuotientDefect`, `ApproxKernelIntertwines`, `hasQuotientDefect_zero_of_intertwines`, `approxKernelIntertwines_zero_of_exact` | `Quotient/ApproxPrefix.lean` |
| E1.2 | `TV((q^{0:T})_# P_y^{K,0:T}, P_{q y}^{K̄,0:T}) ≤ min(1, Tη)` — projected fine process need not be Markov | `approxQuotient_prefix_tv_le_linear`, `approxQuotient_prefix_tv_le_min`, `approxQuotient_pathLaw_tv_le_linear`, `approxQuotient_pathLaw_prefix_tv_le` (canonical path laws) | same |
| E1.2 (support) | Ionescu–Tulcea recursion of `finitePrefixLaw`; projection commutes with appending | `finitePrefixLaw_succ`, `prefixMap_appendLast`, `finitePrefixLaw_zero_map` | same |
| E1.3 | Effects: `\|Δ(y) − Δ̄(q y)\| ≤ L(min(1,Tη₀)+min(1,Tη_J))`; margins with `B̄₁ = q(B₁)`: same bound; positive-margin transfer both ways; frozen-family version over the label equivalence `φ` | `approxQuotient_effect_abs_le`, `approxQuotient_margin_abs_le`, `approxQuotient_fine_margin_pos_of_coarse`, `approxQuotient_coarse_margin_pos_of_fine`, `approxQuotient_family_margin_abs_le`, `approxBudget_le_linear` | `Quotient/ApproxMargin.lean` |
| E1.3 (property) | The fine property FACTORS through the compressed prefix law by construction; the coarse property is an explicit A2 `TVLipschitzPrefixProperty` | `projectedPrefixProperty`, `projectedPrefixProperty_value`, `coarsePrefixProperty_value` | same |
| E1.3 (7.4b interface) | Frozen `PropertyFactorsThroughCompression` and `QuotientCompatibleComparisonSets` certificates feed the margin bound for arbitrary factored `ψ`; exact intertwining (AQ1) gives EQUAL margins | `projectedPrefixProperty_factors`, `eq_projectedPrefixProperty_of_factors`, `image_states_of_quotientCompatible`, `approxQuotient_margin_abs_le_of_certificates`, `approxQuotient_margin_eq_of_exact` | same |
| E1.4 | Leakage (kernel level): identity quotient on `Bool`, `K = δ_false`, `K̄_ε = (1−ε)δ_false + εδ_true`; for every `ε ∈ (0,1]`: defect ≤ ε, fine `{false}` invariant, coarse leaves it with probability exactly ε. The step to "no Exact-GR/PR transfer" is interpretive (no `IsExactGeneratedRegime` theorem) | `leaky_hasQuotientDefect`, `fine_region_invariant`, `coarse_region_leaks`, `small_defect_does_not_preserve_invariance` | `Quotient/ApproxAdversaries.lean` |
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

## What the Lean theorems take, and what stays a separate obligation

The core margin inequality (`approxQuotient_margin_abs_le`) uses exactly: a
`TypeRespectingStateCompression`; the image relation `B̄₁.states = q(B₁.states)`;
both comparison sets as ORIGINAL `ConstitutiveComparisonSet`s of their own models;
separate defects `η₀` (baseline) and `η_J` (matched intervention) with
`0 ≤ η₀`, `0 ≤ η_J`; a coarse `TVLipschitzPrefixProperty p` — a `T`-prefix
functional that is `L`-Lipschitz for event TV, `L = p.constant ≥ 0` (this carries
the proof; non-Lipschitz or whole-path properties are NOT covered); and a fine
property that factors through the compressed prefix law into `p` (built into
`projectedPrefixProperty`). The certificate-level wrapper
`approxQuotient_margin_abs_le_of_certificates` instead takes the frozen Theorem 7.4b
objects for conditions (iv) and (v): `QuotientCompatibleComparisonSets` (preimage
form `B₁ = q⁻¹B̄₁`, turned into the image relation by
`image_states_of_quotientCompatible`) and `PropertyFactorsThroughCompression` for
an arbitrary fine `ψ` factoring through `p.toRegimeProperty` for such a
TV-Lipschitz `p` (`eq_projectedPrefixProperty_of_factors`). The frozen-family version runs over the
label equivalence of `QuotientFamilyMatching`.

**Not used and NOT formalized in E1** (they remain independent obligations for any
Exact-GR / PR claim on either side): `B = q⁻¹B̄`, `B₀ = q⁻¹B̄₀`, the descriptor
factorization `h = h̄∘q` and the same descriptor target law `ν` (Theorem 7.4b
(ii)–(iii); `QuotientCompatibleRegimeSpecifications`), the grounding factorization
`g = ḡ∘q` (`RelevanceMapFactorsThroughCompression`), each model's Assumption 4.1 /
nontriviality gates, convergence-mode compatibility, and admissible initial-law
lifts. The margin inequality is true without them; it simply says nothing about
Exact GR. Factorization only on the compared Dirac laws (weaker than the frozen
all-laws predicate) is not covered.

**Spec name map.** The spec crosswalk's `approxQuotient_pathLaw_tv_le_linear` exists
with exactly that name (canonical path laws, `T η` form); the capped form is
`approxQuotient_pathLaw_prefix_tv_le`, and the generic kernel-level forms are
`approxQuotient_prefix_tv_le_linear` / `approxQuotient_prefix_tv_le_min`.

## Executable adversaries

`verification/research/test_e1_approx_quotient.py` (20 exact-`Fraction` tests on
finite chains; executable cross-checks, NOT proofs of the measurable-space theorems):

- **Non-Markov projection (AQ2).** From the single fine start `0`, the projected
  next-step law depends on the coarse history (`1/2` vs `0` for `KNM`; `1/2` vs
  `12/25` for a near-lumpable kernel). The linear bound `TV ≤ Tη` is checked on a
  near-lumpable family (`η ∈ {1/20, 1/10, 1/8}`) only at horizons with `Tη < 1`
  (vacuous horizons are rejected) and with a strictly positive TV observed; the
  fully non-lumpable `KNM` grid (`η ≥ 1/2`) is kept only as a cap sanity check.
- **Defect over ALL fine states.** An unreachable fine state carries the largest
  one-step TV; the defect equals it and strictly exceeds the reachable supremum,
  a class representative and the fibre mean.
- **Initial-law lift.** With `η = 0`, a coarse start that is not the image of the
  fine initial law breaks the bound already at `T = 0`.
- **Exact lumpability (AQ1).** `η = 0` gives TV `0` for horizons `≤ 5` (all horizons:
  `approxQuotient_prefix_tv_le_linear` with `η = 0`), and equal fine/coarse effects
  for a second exactly lumpable pair with a different coarse kernel.
- **Leakage (AQ3).** `TV = 1 − (1−ε)^T ≤ Tε`, including the cap `TV = 1` at `ε = 1`;
  invariance lost. The geometric envelope (E1.5) is observed numerically only on
  the near-lumpable family; it stays OPEN in Lean.
- **Margins (V20.33–34).** Pointwise and margin bounds with two positive defects
  `η₀ = η_J = 1/10` and budget `< 1` (gap `3/50` at `T = 3`); a baseline-only
  certificate (`η₀ = 0`) does not cover the gap (`1/120 > 0`) when the matched
  intervention has `η_J = 1/10`; label mismatch defeats the budget.
- **Descent failures.** A property reading the hidden fine state separates exactly
  lumped models (ψ must factor); a non-saturated region `B = {0}` inside fibre
  `{0, 1}` has a hit probability that is not a function of the (identical) projected
  laws (B/h descent is a separate obligation).
- **Typing.** The parity quotient `q(s, x) = s XOR x` lumps a kernel exactly
  (`η = 0`) but is not of the form `q_S × q_X`, so the typed theorems do not apply.
- **Positive margin is not Exact GR.** On `{0, 1, 2}` with an admissible
  `B₁ = {0, 1}` (distinct path laws, inside the region): margins `1` and
  `(1−ε)^3` both exceed the budget `3ε` and transfer in both directions, while the
  coarse region `{0, 1}` leaks.

## Verification evidence (local)

- Lean 4.34.0 / pinned mathlib: all five modules compile; signatures inspected —
  no `CountableOrCountablyGenerated` or standard-Borel instance appears.
- `verification/research/e1_axiom_audit.py`: every theorem/lemma/def/abbrev/instance
  in the five modules allowlisted (anonymous instances are rejected by the script;
  count printed by the script; see the PR).
- The C69 audit passes 33/33 after moving the shared lemma (`compProd_map_left_eq_map_compProd_comap` is now audited by `e1_axiom_audit.py`).
- Focused workflow: `.github/workflows/e1-approx-quotient-smoke.yml`.
