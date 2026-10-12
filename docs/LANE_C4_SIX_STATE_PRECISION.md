# Lane C4 — exact six-state coordinates and periodic marginal nonconvergence

**Status:** Research implementation **in review** in [PR #55](https://github.com/HMarcusWH/PermanssonLean/pull/55). Do not infer a successful proof from its creation. All theorem-source and CI evidence must be checked at the exact final head and synthetic merge.

**Frozen base:** `main@12cdd6c1e0fab5481f314e1d97b19d0c437d0936` (merged C3 PR #54). This work is a separate research library extension and does not change original v0.1.8 theory, paper, application statuses or historical release artifacts.

## 1. Exact claim

The typed six-state realization has physical joint state `SixY := JointState Unit (Fin 6)`, true kernel `K := ExactSixStateTyped.typedModel.inducedKernel`, recurrent classes A={a0,a1} and B={b0,b1}, with transient t/u. Exact rational row data `ExactSixState.transition` already existed, as did C2's noncomputably constructed unique actual invariant probability measures `ExactSixStateClassLaws.πA/πB`.

C4 identifies the **actual probability measures**, not just a reference rational matrix:

\[
\pi_A=(0,0,1/2,1/2,0,0),\qquad
\pi_B=(0,0,0,0,1/3,2/3).
\]

Under the **same genuine infinite typed α→P→U path law** from a0, the one-time marginals satisfy at *all* finite n:

\[
\mathcal L_{a0}(Y_{2n})=\delta_{a0},\qquad
\mathcal L_{a0}(Y_{2n+1})=\delta_{a1}.
\]

Consequently the full probability-valued marginal sequence has **no weak limit**, although C2's empirical occupation satisfies:

\[
\widehat\mu_N\longrightarrow\pi_A\quad\text{almost surely}.
\]

The same pathology is *not* asserted under a stationary initial distribution πA; it has constant marginals.

## 2. Proof dependencies and no-model-swap boundary

The new `ExactSixStateStationaryCoordinates.lean` proves `realTransition_typed_six_state` using the exact genuine typed kernel singleton identity `ExactSixStateRecurrentGeometry.typed_six_state_atom`, `FiniteKernelRealBridge.realTransition`, and proved nonnegativity. The rational vectors are reindexed to the real joint state by the existing encoded bijection, their normalized/positive/stationary/support properties proved against the actual typed kernel, and the corresponding actual `ProbabilityMeasure` values constructed with `FiniteInvariantMeasureTransport.vectorMeasure`. The unique class-supported stationary law theorem from `FiniteClassInvariantMeasure` identifies each explicitly constructed measure with **C2's unchanged πA/πB**, yielding all exact singleton coordinates. No aperiodicity or global irreducibility assumption is introduced.

The new `ExactSixStateMarginalOscillation.lean` proves whole-measure deterministic rows `K a0 = dirac a1` and `K a1 = dirac a0` using genuine typed singleton identities. It derives even/odd laws from the **actual** Ionescu–Tulcea trajectory and existing Chapman–Kolmogorov identity; the generic `CanonicalKernelMarginals.canonical_eval_eq_kernel_pow` identifies them with powers of K. It packages the true time-marginal pushforwards as `ProbabilityMeasure` and rules out every weak limit via cofinal parity subsequences and `T2Space (ProbabilityMeasure SixY)`. For the a.s. occupation claim, it first proves actual time-zero support from the real marginal, then invokes the established C2 canonical closed-class selector and occupation strong law; the horizon convention remains observations 0 through N-1.

**Existing originals retained:** `ExactSixState.lean`, `ExactSixStateClassLaws.lean`, `FiniteClassInvariantMeasure.lean`, `ExactSixStateFullRandomLaw.lean`, all frozen `PermanssonLean/` declarations, and C3's completed regime equivalence theorem.

## 3. Independent exact-rational adversaries

`verification/research/test_lane_c4_six_state_precision.py` is discovered by the existing `python -m unittest discover` research CI command, in addition to all historical suites. It covers:

1. All 36 typed-reference rational table entries against a **separately literal frozen** matrix and exact stochastic row checks.
2. All six πA coordinates, support, and normalization.
3. All six πB coordinates, support, and normalization.
4. Exact stationarity for both distributions.
5. a0 parity through powers n=0,…,40.
6. a1 opposite parity.
7. Exact finite empirical occupation counts at even and odd horizons.
8. Stationary πA initial law with constant marginals.
9. Valid stochastic row mutations that falsify periodic parity and/or stationary law.
10. Random physical class limit as a two-atom law distinct from its barycenter.
11. Parametric three-state q/A/B absorbing model with exact self-loop r=2/3, selecting A with arbitrarily small positive ε and A unreachable at ε=0.
12. Explicit strict input/matrix validation, rejection of invalid ε/rows and **no silent renormalization**.

These Python checks are independent computational counterexamples and regression controls, **not** deductive proofs of general Markov convergence or of unknown empirical kernels.

## 4. Review and trust boundary

**No theorem claim before exact-head CI.** The two new research modules must elaborate with their unweakened theorem statements. Root imports must include both *before* the module-level documentation comment. Research Lean must build the full target, audit transitive declarations only against `propext`, `Classical.choice`, `Quot.sound`, run the new and all previous regression tests, verify all root imports, and reject `sorry`/`admit`/custom axioms. The original Lean, Executable verification and Application contract workflows must independently succeed at the final synthetic merge.

**Protected:** `PermanssonLean/`, `PermanssonLean.lean`, `paper/`, `application/`, workflow definitions, Lean toolchain, Lake manifest, v0.1.8 provenance/history and C1/C2/C3 source proofs. No new original-v0.1.8 GR, confirmatory GR, constitutive PR, identification, control, robustness, or external-paper assertion is inferred.

A GitHub/assistant source review does not constitute independent scholarly peer review. The full C4 PR must remain draft until all formal and regression checks pass and a new source-level review is complete; merge needs subsequent explicit user authorization.

## 5. Final source checkpoint (to populate after verification)

- C4 theorem source SHA: **PENDING**.
- Tested exact GitHub synthetic-merge SHA: **PENDING**.
- Research Lean (build + axiom audit + regression count + imports): **PENDING**.
- Original Lean: **PENDING**.
- Executable verification: **PENDING**.
- Application contract: **PENDING**.
- Source review: **PENDING**.

If any additional documentation-only commit follows a verified code head, rerun and audit all four workflows at that **later final head**, distinguishing historical proof-source SHA from new documentation-only commits.
