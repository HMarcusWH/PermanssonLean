# NEXT-04 / nonstationary fine/coarse common-history transport

Scope: explicit time-indexed **actual** fine and coarse history evolutions, distinct initial laws, measurable projection maps, and a finite common fine subkernel. Source provider `DependentHistoryCommonMass.lean` supplies evolution, all-history rowwise common mass, and the product lower bound. `CompProdPushforward.lean` supplies first-factor transport.

## Claimed mathematical content

1. `projected_evolution_le` proves induction-based domination of the actual projected common fine-history measure by the actual coarse history measure, requiring `ξ.map(q 0) ≤ ν` and all-history projected `R n` row domination by `L n`. This is not an assumed TV bound or a Markov projection.
2. `projected_evolution_tv_le_product` proves `TV(q_n # evolution(μ,K,n), evolution(ν,L,n)) ≤ 1 -(1-ε) ∏_{t<n}(1-η_t)` from `ξ≤μ`, `q_0#ξ≤ν`, `R_n≤K_n`, each projected common row beneath coarse `L_n`, `ξ(univ)≥1-ε`, and every fine common row retaining mass `1-η_n`.

The shared initial sublaw and ALL-history row premises are required; no probabilistic independence assumption is introduced. ε and η are allowed to be zero or one, and η may be nonstationary. The quantified history spaces can encode `0..n` observations.

## NOT proved by this PR

- The actual `canonicalPathLaw`/`partialTraj` identification for a user-chosen fine/coarse strategic-world model. That remains a typed adapter.
- A general measurable RN existence theorem providing `R` for arbitrary kernels (not needed under the explicit subkernel hypothesis).
- A discounted original constitutive-margin wrapper with source-model output identification and the full original comparison basin (separate NEXT-04 follow-on).
- Exact GR/PR, whole-path TV from a recurring positive defect, empirical identification, or real-world causal claims.

Before acceptance: pinned Lean 4.34.0 Research build, theorem signatures/axioms, a positive source instance and semantic negative test, original Lean, preservation/export/archive, CI H/S identities. Do not merge without explicit authorization.
