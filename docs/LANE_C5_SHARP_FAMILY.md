# Lane C5 — sharp positive-atom observed-limit families

**Research PR:** [#56](https://github.com/HMarcusWH/PermanssonLean/pull/56).
**Status (12 October 2026):** C5's mathematical source is **compiled, transitive-axiom-audited, independently regression-tested and reviewed** at the exact source head and tested synthetic merge in Section 6. This is a research-only proof checkpoint, **not** a new v0.1.8 release or independent scholarly peer review. A later documentation-only commit requires fresh four-workflow verification before merge. Consult [PR #56](https://github.com/HMarcusWH/PermanssonLean/pull/56) for that final-head and merge state.
**Frozen base:** `main@68bbb8025c931d0519621e4a827a50250945ddb7` (merged C4 PR #55).

## 1. Actual mathematical novelty

C2 already established finite homogeneous Markov recurrence, the canonical infinite path, almost-sure empirical occupation convergence for every initial probability law, class-stationary uniqueness, the full law of the resulting random measure, and basin-reachable class selection. C3 already established an Exact GR iff common reachable observed class target (under the original hypotheses). C4 already established true six-state stationary coordinates and periodic marginal oscillation.

C5 **does not repeat these**. The new subject is the exact minimal family of *attainable observed canonical limit atoms* under a predeclared nonempty basin.

For a genuine finite-state Markov kernel `K`, a `FrozenBasinFamily K H` with basin `B0` and measurable descriptor `h`, and the already-proved C2 canonical selected recurrent-class representative `I(w)`, define

```text
R(K,B0) := {i recurrent representative : ∃y∈B0, P_y[I=i] != 0}
V(K,B0,h) := { h_# π_class(i) : i∈R(K,B0) }
λ(w) := h_# π_class(I(w))
E_ν := {w : λ(w)=ν}
```

The finite image `V` deduplicates observationally equal physical classes. Its meaning is **positive-probability canonical atoms**; it is not arbitrary topological support or an executable solver.

Verified theorem declarations in `SharpObservedFamily.lean`:

- `sharpObservedFamily_nonempty`: the predeclared basin produces a nonempty finite observed family.
- `observedFamilyEvent_measurable` and `observedAtomEvent_measurable`: events `λ(w) ∈ V` and `λ(w)=ν` are measurable through the **finite-valued class selector**, even without globally assuming arbitrary singletons of `ProbabilityMeasure H` are measurable.
- `covers_iff_sharp_subset`: `∀ μ, μ(B0)=1 → P_μ(λ∈V)=1` iff `V(K,B0,h) ⊆ V`.
- `mem_sharp_iff_positive_atom`: `ν∈V(K,B0,h)` iff `∃y∈B0, P_y(E_ν) != 0`. No arbitrary minimum probability cutoff.
- `covers_and_noSpurious_iff_eq_sharp`: coverage and a positive basin witness for *every* claimed candidate member iff the finite candidate equals `V(K,B0,h)` exactly.

C2's existing `observedOccupationLimit_ae_correct` proves that this same canonical `λ` is the almost-sure weak limit of the *actual empirical occupation* under the original infinite path law. C5 reuses that theorem rather than claiming a new ergodic theorem or replacing the limit by a one-time marginal. `observedAtomEvent_mass_eq_class_sum` further proves the exact class-weight grouping at one observable atom by summing genuine canonical class-selector probabilities.

## 2. Conservative original GR bridge

`SharpFamilyExactGRBridge.exactGR_iff_sharp_singleton` is a compiled direct corollary of C3's existing `exactGR_iff_common_reachable_target`:

```text
IsExactGeneratedRegime M spec m
 ↔ sharpObservedFamily M.inducedKernel (frozenFamilyOfExactSpec ... h41 hinv)
   = {spec.target}
```

Keep the following gates **unweakened and literal**: `Assumption41 M spec m`, `IsExactlyInvariant M spec`, `spec.convergenceMode = ConvergenceMode.almostSureWeak ...`, `T2Space (ProbabilityMeasure H)`, and the finite/discrete measurable-world requirements of C3. `FrozenBasinFamily` alone does not imply original Assumption 4.1. The singleton `{wrong target}` must not pass merely because the family has one member.

## 3. Typed six-state witnesses

`ExactSixStateSharpFamily.lean` reuses the genuine `ExactSixStateTyped.typedModel.inducedKernel`, C3's canonical representatives `rA/rB`, and the previously proved positive selection weights. The proof never identifies those noncomputably chosen representatives with specific physical labels `a0/b0`.

For the identity descriptor with the original proper two-point basin `{u,a0}`, the sharp family contains BOTH distinct actual class stationary probability laws

`πA=(0,0,1/2,1/2,0,0)` and `πB=(0,0,0,0,1/3,2/3)`.

The frozen Boolean descriptor collapses the observed family to `{δ_true}`, despite the distinct physical class laws. This is a valid original Exact GR witness only because C2/C3 separately verify Assumption 4.1, exact invariance and the original convergence gate. No general PR/constitution claim follows.

## 4. Independent exact-Fraction adversaries

`verification/research/test_lane_c5_sharp_family.py` independently transcribes the six-state rational transition matrix and solves stationary and class-hitting equations using exact Gauss–Jordan rational arithmetic. All 15 tests passed, covering:

1. Six-state rows, real class stationary coordinates and genuine positive class-selection law.
2. Physical identity descriptor versus observed Boolean collapse.
3. Exact transient `u` class-selection probabilities `1/3` and `2/3`.
4. Mixed initial law `1/5 δ_u + 4/5 δ_a0` giving `13/15` for A and `2/15` for B.
5. Genuine A-only **two-state** basin `{a0,a1}`.
6. Overbroad candidate family: coverage passes but the no-spurious-atom gate fails.
7. Missing genuine atom: coverage fails.
8. Strict positive-vs-zero weight distinction at epsilon `10^-35`.
9. Nonstationary periodic marginals distinct from a converging empirical occupation.
10. Wrong singleton original target and invalid input rejection.

Computational regressions are falsification controls, **not proof of general stochastic convergence, Lean-to-Python program equivalence or external real-world model identification**.

## 5. Hypotheses and safety boundaries

- Finite nonempty state, genuinely normalized Markov kernel, canonical infinite path, finite recurrent classes, same frozen basin and descriptor on both sides.
- No assumed IID path sampling or aperiodicity.
- Canonical selected observed limits versus **all** possible weak limits: the latter requires topology sufficient for uniqueness, as explicitly assumed in C3. C5's basic atom theorem does not claim a unique weak limit in arbitrary non-Hausdorff descriptor spaces.
- Preserve distinct notions: original Exact GR, multiple-limit family, confirmatory GR, constitutive PR, finite persistence and empirical applications.
- No new `ROBUST_PR` application schema or retroactive v0.1.8 release hash.
- `PermanssonLean/`, paper, application, toolchain, manifest, workflows, C1–C4 proof sources and historical verification/release evidence remain frozen.
- Accept the research library's normal transitive allowlist `propext`, `Classical.choice`, `Quot.sound`; disallow `sorry`, `admit` or added custom axioms.
- An assistant code review or CI success is **not** independent human scholarly peer review.

## 6. Verified mathematical-source checkpoint — 12 October 2026

- **Last C5 mathematical-source HEAD:** `8ceaf2349620ee20c92ffeb1387ff5c08b0bdd3b` (11 commits in PR before release-record finalization).
- **Exact GitHub synthetic merge checked out and tested:** `c4dabe71c129c84ad1f2fe9317a39335d7c01390`, merging that source HEAD into frozen `main@68bbb8025c931d0519621e4a827a50250945ddb7`. This checkout is visible in the final Research Lean log.
- **[Research Lean #38304439645](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38304439645): SUCCESS.** Full root built **3,944 Lean jobs**. The transitive axiom audit checked **2,760** `PermanssonResearch` declarations, all within the only admitted `propext`, `Classical.choice`, `Quot.sound` allowlist. All **167** independent research tests passed (the prior **152** plus **15** C5 exact-`Fraction` adversaries). The **240** research modules were all directly imported; the research placeholder/custom-axiom source firewall passed, as did the original default-target build.
- **[Original Lean #38304439558](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38304439558): SUCCESS.**
- **[Executable verification #38304439616](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38304439616): SUCCESS.** Historical frozen-release provenance and destructive verification gates remained valid.
- **[Application contract #38304439602](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38304439602): SUCCESS**, including **Ubuntu and Windows** jobs. Structural contract PASS is not empirical certification.
- **Source/hypothesis review: COMPLETED** in [PR review #5495730329](https://github.com/HMarcusWH/PermanssonLean/pull/56#pullrequestreview-5495730329), an **assistant-conducted COMMENT** anchored to the exact source HEAD. No blocking mathematical/source finding or unresolved review threads. This is **not** an independent human `APPROVED` review or external scholarly peer review.
- **Protected-file audit:** Exactly eight PR files are affected: three new `PermanssonResearch/MultipleLimit/` modules, the direct-import root `PermanssonResearch.lean`, one `verification/research/` regression suite and the C5 research ledger/build-guide/roadmap. Original `PermanssonLean/`, `PermanssonLean.lean`, `paper/`, `application/`, existing C1–C4 proofs, workflow definitions, toolchain, Lake manifest, and historical release metadata are unchanged.
- **Nonblocking warnings:** existing Lean lint/unused-instance suggestions and GitHub Actions/Node deprecation notices. No additional axiom, unproved new theorem, or failed current-head workflow is reported in this checkpoint.

**Final documentation-head / merge gate:** The evidence above certifies the **immutable mathematical source checkpoint**, not a subsequent documentation-only HEAD. If this ledger, build guide or roadmap is committed after the verified source HEAD, re-run and check all **four workflows at the new final HEAD and exact synthetic merge**, and report their URLs and SHAs in [PR #56](https://github.com/HMarcusWH/PermanssonLean/pull/56). Promote/merge only after those checks pass and the author-controlled merge decision is satisfied. Do not represent CI or an assistant review as external peer review, empirical identification or generalized constitutive PR certification.
