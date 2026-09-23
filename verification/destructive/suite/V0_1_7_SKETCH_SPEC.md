# Permansson v0.1.7-SKETCH — mathematical upgrade specification

**Control:** frozen v0.1.6 submission-final.  v0.1.7 is additive unless a theorem-backed change earns promotion.

## Core candidate upgrades

1. **Polish descriptor spaces.** Replace the declaration that the descriptor space `H` is compact metrizable by `H` Polish, using a bounded compatible metric for bounded-Lipschitz weak convergence. This does **not** assert existence of a limiting law.
2. **Exact killed-kernel persistence.** For measurable `B`, define `K_B(y,A)=K(y,A∩B)`. For `y∈B`, finite survival after `L` transitions is exactly `K_B^L 1(y)`, and expected exit time is the extended Green series `Σ_{n≥0}K_B^n1(y)`.
3. **QSD-certified quasi-regimes.** Optional subclass only. A QSD `μ K_B = θ μ` gives geometric survival and a conditionally stationary law. Existence/uniqueness are never assumed without hypotheses; QSD, Yaglom limit, and quasi-ergodic law remain distinct.
4. **Constitutive effect profile and uniform margin.** `Δ_{ψ,J}(y)=d_ψ(ψ(P_y),ψ(P_y^J))`, `κ_{ψ,J}(B1)=inf_{y∈B1}Δ_{ψ,J}(y)`. This is notation for v0.1.6's already-tested pointwise/uniform distinction, not a new PR definition.
5. **Perturbation certification.** If baseline and intervention property outputs move by at most `ε0,εJ`, then `|Δ-Δ~|≤ε0+εJ` and `κ~≥κ-ε0-εJ`. Therefore `κ>ε0+εJ` certifies robustness. Kernel-to-law bounds are imported only in finite-horizon, ergodic/contraction, or killed/QSD subclasses where assumptions are explicit.
6. **Intervention-family signatures.** `Sig_J(M)=(K_M,{K_M^J}_{J∈J})`. Matched full signatures plus matched frozen semantics preserve the corresponding family of PR classifications. Partial signatures do not.
7. **Intervention-compatible quotient theorem (candidate).** A quotient must intertwine the baseline and every frozen intervention kernel and must also preserve/descend `B,B0,h,g,ψ` and the nontriviality gates. Baseline lumpability alone is insufficient.

## Original-math research lane

8. **Scalar-defect reduction (specialized linear/bilinear subclass).** Codimension-one core agreement can force a symmetric discrepancy to rank ≤2; an additional rigidity condition may collapse it to a scalar rank-one common-mode defect. No universal nonlinear PR claim is made.
9. **Persistent finite detection (candidate).** Strict failure plus continuity in the consumed topology plus legal finite approximation gives finite detection; exact nested embeddings are separately required for persistent badness.
10. **First-bad quotient/Schur reduction (candidate).** If a nested hierarchy has a least bad level and successor quotient dimension `r`, seek an `r×r` Schur/Feshbach obstruction; scalarization is justified only for `r=1`.
11. **Singular compatibility (candidate).** At singular predecessor/linearized operators, use kernel/range compatibility; do not silently insert an inverse or pseudoinverse as an exact solution.
12. **Quadratic-response witness (specialized subclass).** Where a constitutive comparison genuinely has signed rank-one form `c(xx^T-yy^T)`, the uploaded Gram-witness theorem supplies a constructive negative witness and exact robustness margin.
13. **Smooth-intervention jets / tiny detector banks (experimental).** Architectures inspired by the uploaded moment-jet and two-translate theorems remain experimental until a natural Permansson interface is proved.

## Promotion rule

Each addition is evaluated against v0.1.6 by theorem power, assumptions, quantitative information, certification power, semantic cost, and new failure surface. Tests are falsification evidence, not substitutes for general proofs.
