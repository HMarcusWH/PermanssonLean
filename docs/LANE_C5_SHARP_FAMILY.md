# Lane C5 — sharp positive-atom observed-limit families

**Research PR:** [#56](https://github.com/HMarcusWH/PermanssonLean/pull/56).
**Status:** draft / source implementation undergoing Lean compilation, scientific review and independent regression verification. **Not a new v0.1.8 release.**
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

Headline candidate theorems in `SharpObservedFamily.lean`:

- `sharpObservedFamily_nonempty`: the predeclared basin produces a nonempty finite observed family.
- `observedFamilyEvent_measurable` and `observedAtomEvent_measurable`: events `λ(w) ∈ V` and `λ(w)=ν` are measurable through the **finite-valued class selector**, even without globally assuming arbitrary singletons of `ProbabilityMeasure H` are measurable.
- `covers_iff_sharp_subset`: `∀ μ, μ(B0)=1 → P_μ(λ∈V)=1` iff `V(K,B0,h) ⊆ V`.
- `mem_sharp_iff_positive_atom`: `ν∈V(K,B0,h)` iff `∃y∈B0, P_y(E_ν) != 0`. No arbitrary minimum probability cutoff.
- `covers_and_noSpurious_iff_eq_sharp`: coverage and a positive basin witness for *every* claimed candidate member iff the finite candidate equals `V(K,B0,h)` exactly.

The C2 `observedOccupationLimit_ae_correct` connects `λ` to the *actual empirical occupation limits* under the original infinite canonical law. The code must use this existing theorem for interpretation and must not silently replace the observed canonical limit by a one-time marginal.

## 2. Conservative original GR bridge

`SharpFamilyExactGRBridge.exactGR_iff_sharp_singleton` should be a small direct corollary of C3's `exactGR_iff_common_reachable_target`:

```text
IsExactGeneratedRegime M spec m
 ↔ sharpObservedFamily M.inducedKernel (frozenFamilyOfExactSpec ... h41 hinv)
   = {spec.target}
```

Keep the following gates **unweakened and literal**: `Assumption41 M spec m`, `IsExactlyInvariant M spec`, `spec.convergenceMode = ConvergenceMode.almostSureWeak ...`, `T2Space (ProbabilityMeasure H)`, and the finite/discrete measurable-world requirements of C3. `FrozenBasinFamily` alone does not imply original Assumption 4.1. The singleton `{wrong target}` must not pass merely because the family has one member.

## 3. Typed six-state witnesses

`ExactSixStateSharpFamily.lean` must reuse the genuine `ExactSixStateTyped.typedModel.inducedKernel`, `ExactSixStateC3Witness.rA/rB` and their previously proven positive class-selection weights. Never substitute `a0/b0` for noncomputable class representatives.

For the identity descriptor with the original proper two-point basin `{u,a0}`, the sharp family contains BOTH distinct actual class stationary probability laws

`πA=(0,0,1/2,1/2,0,0)` and `πB=(0,0,0,0,1/3,2/3)`.

The frozen Boolean descriptor collapses the observed family to `{δ_true}`, despite the distinct physical class laws. This is a valid original Exact GR witness only because C2/C3 separately verify Assumption 4.1, exact invariance and the original convergence gate. No general PR/constitution claim follows.

## 4. Independent exact-Fraction adversaries

`verification/research/test_lane_c5_sharp_family.py` independently transcribes the six-state rational transition matrix and solves stationary and class-hitting equations using exact Gauss–Jordan rational arithmetic. It must cover:

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

## 6. Final-source and CI checkpoint

**PENDING**, not to be called PROVED merely because source files exist.

- C5 theorem source HEAD: **PENDING**.
- Exact GitHub synthetic-merge SHA: **PENDING**.
- Research Lean full compilation, transitive axioms, regressions, direct imports and source firewall: **PENDING**.
- Original Lean: **PENDING**.
- Executable verification: **PENDING**.
- Application contract (Ubuntu and Windows): **PENDING**.
- Actual source/hypothesis review and any unresolved findings: **PENDING**.
- Reviewed author-controlled merge decision: **PENDING**.

Any additional source or documentation commit after a verified checkpoint **requires fresh four-workflow checks** at the later exact head. The PR remains draft until implementation, review and final-head CI are resolved.
