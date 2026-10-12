# Lane C4 — exact six-state coordinates and periodic marginal nonconvergence

**Status (12 October 2026):** C4's theorem-source implementation is **compiled, axiom-audited, independently regression-tested, and source/hypothesis-reviewed** at the exact immutable source and synthetic-merge checkpoint recorded in Section 5. This is research-only verification, not independent scholarly peer review. [PR #55](https://github.com/HMarcusWH/PermanssonLean/pull/55) records the subsequent documentation-only final-head CI and author-controlled merge decision; do not mistake the proof-source SHA for a later documentation-head SHA.

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

**Verified theorem-source gate.** Both new research modules elaborate with their unweakened theorem statements. Both have direct root imports *before* the module-level documentation comment. Research Lean built the full root, audited transitive declarations against only `propext`, `Classical.choice`, `Quot.sound`, passed all 152 research regressions, confirmed 237 direct research-root imports, and rejected `sorry`/`admit`/custom axioms. Original Lean, Executable verification, and Application contract (Linux and Windows) independently succeeded on the same source head and synthetic merge. The exact evidence appears in Section 5; any **later documentation-only head must be rechecked** before merge.

**Protected:** `PermanssonLean/`, `PermanssonLean.lean`, `paper/`, `application/`, workflow definitions, Lean toolchain, Lake manifest, v0.1.8 provenance/history and C1/C2/C3 source proofs. No new original-v0.1.8 GR, confirmatory GR, constitutive PR, identification, control, robustness, or external-paper assertion is inferred.

An assistant-conducted GitHub review COMMENT on the exact source head checked the actual induced kernel, class-stationary uniqueness, canonical-path parity and occupation statements, declared hypotheses, tests, and protected-file boundaries. It found no blocking source-level defect; minor lint warnings are nonblocking. This is **not** an independent human APPROVED review or external scholarly peer review. Final promotion additionally requires the refreshed documentation-head four-workflow gate and the author's explicit merge authorization.

## 5. Reviewed mathematical-source checkpoint — 12 October 2026

- **Last C4 theorem-source HEAD:** `47772e8c3f5d2e503f1008ccf1fa9221653b711e`.
- **Exact GitHub PR synthetic merge tested:** `162e47b8cfd60977e0191e0b6333f0da98ae554d` against frozen `main@12cdd6c1e0fab5481f314e1d97b19d0c437d0936`. Checkout of this synthetic merge is visible in the Research Lean job log.
- **[Research Lean #38285576069](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38285576069): SUCCESS.** Full research target: **3,941** Lean jobs; **2,728** declarations passed transitive axiom audit with exactly the established `propext`, `Classical.choice`, `Quot.sound` allowlist; **152** exact-rational research regression tests passed, including all 12 C4 adversarial families; **237** directly imported research modules; default original target and source placeholder/custom-axiom firewall both passed.
- **[Original Lean #38285576023](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38285576023): SUCCESS.**
- **[Executable verification #38285575998](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38285575998): SUCCESS.**
- **[Application contract #38285576002](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38285576002): SUCCESS** on both Ubuntu and Windows jobs.
- **Source/hypothesis review: COMPLETED (assistant COMMENT review ID `5494948329` on the exact theorem-source HEAD).** Reviewed no-model-swap, mathematical quantifiers, weak-limit topology, a0-only start, genuine infinite-path convergence, exact rational controls, and protected-file diff. No blocking defect identified. Not an independent human approval.
- **Protected-file audit:** the six-file source diff changes only `PermanssonResearch.lean`, two new `PermanssonResearch/MultipleLimit/` modules, one `verification/research/` test and two research documents. No frozen `PermanssonLean/`, paper, application, existing C1–C3 source, toolchain, manifest, workflow or historical release change.

**Documentation-finalization gate:** This section records the *immutable proof-source checkpoint*, not the later documentation commit. After changing this ledger or the research build guide, rerun all four workflows on the **new PR head and exact synthetic merge**. Record the resulting final-head SHA, tested merge SHA, workflow URLs, and merger decision in [PR #55](https://github.com/HMarcusWH/PermanssonLean/pull/55) without retroactively changing the source checkpoint. No new empirical or constitutive certificate follows from any of these CI results.
