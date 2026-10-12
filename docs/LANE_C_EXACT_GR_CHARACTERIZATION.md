# Lane C3 — finite-state Exact GR characterization

**RESEARCH ONLY — not part of the frozen Permansson v0.1.8 paper.**
**Status:** C3 implementation under review in [PR #54](https://github.com/HMarcusWH/PermanssonLean/pull/54). No merge or formal release is claimed until the exact-head Research Lean, original Lean, executable verification, and application-contract gates all pass.

## The mathematical objective

C2 ([merged PR #53](https://github.com/HMarcusWH/PermanssonLean/pull/53)) proves the unconditional finite homogeneous Markov classwise strong law for the actual Ionescu–Tulcea infinite path, its measure-valued random occupation-limit law, and *sufficient* original Exact GR recovery when every basin-reachable class yields a common descriptor target.

C3 is the **necessary-and-sufficient** statement for the unchanged original original `RegimeSpecification` / `IsExactGeneratedRegime`:

\[
\mathrm{ExactGR}(M,\Sigma,m)
\quad\Longleftrightarrow\quad
\forall i\in\mathcal R_K(B_0),\ 
h_\#\pi_{C(i)}=\nu.
\]

This is conditioned on the original `Assumption41 M spec m`, `IsExactlyInvariant M spec`, the **literal equality** `spec.convergenceMode = ConvergenceMode.almostSureWeak Y H` and `T2Space (ProbabilityMeasure H)`. The finite physical state is `Y = JointState S X`. The actual path law is `M.pathLaw` identified with `FiniteCanonicalPath.canonicalPathLaw M.inducedKernel`.

The topology assumption cannot be erased: arbitrary Borel descriptor spaces do not ensure uniqueness of weak limits of probability measures. Pinned Mathlib v4.34.0 has `ProbabilityMeasure.t2Space` under `HasOuterApproxClosed H` and `BorelSpace H`, but the generic characterization exposes the required property directly.

## Dependency DAG

1. **`FiniteObservedLimitUniqueness.lean` — C54-01.** Original Exact GR implies empirical descriptor weak convergence to the frozen target for every admissible initial law. C2 supplies an independently proved a.s. limit for the *same empirical process*. Uniqueness of weak probability-measure limits forces a.s. equality of its random limit and the original target.
2. **`FiniteClassTargetNecessity.lean` — C54-02.** For each basin point and representative selected with **nonzero actual canonical probability**, the observed class stationary law equals the frozen target. The proof uses the positive event against the a.s. null set of failures, not an assumed uniform minimum class weight. It also proves that the reachable-class family depends only on the frozen basin.
3. **`FiniteExactGRCharacterization.lean` — C54-03.** Forward direction uses the necessity lemma over every basin-reachable class. Backward direction invokes the existing compiled C2 `recover_original_exactGR_of_common_class_target` unchanged. An additional theorem exposes `Assumption41` and exact invariance as explicit existential witnesses.
4. **`FiniteExactGRObstruction.lean` — C54-04.** One reachable observed class incompatible with the frozen target refutes Exact GR. Two reachable classes with distinct observed stationary laws refute **every** single target under the original gates and mode. Target-only updates require explicit transport of Assumption 4.1, invariance, mode and basin selection; a nonempty class family provides target uniqueness.
5. **`ExactSixStateC3Witness.lean` — C54-05.** Concrete true typed `α→P→U` six-state model from C2. The original nonconstant Boolean descriptor collapses distinct physical class laws and admits an Exact GR. The identity descriptor separates the two reachable physical laws and obstructs Exact GR for every target. The arbitrary `Classical.choose` representative of a class is **not assumed equal to any physical state label**; its singleton selection event is proved equivalent to whole-class selection before transporting exact 1/3 and 2/3 probabilities.

All modules must be imported directly by `PermanssonResearch.lean`, even if transitively reachable by other C3 modules.

## Axioms and hypotheses: scientific firewall

- Finite nonempty `JointState S X`, genuine stationary Markov kernel and arbitrary admissible initial probability measure; no aperiodicity, initial stationarity or rational entry assumption.
- `regimeSpec.convergenceMode` must equal the frozen `almostSureWeak` constructor. Arbitrary custom modes are **not** characterized by this theorem.
- Exact GR is not confirmatory GR or intervention-relative constitutive Permansson PR. No strategic action can be inferred to be constitutive solely from an observed limit classification.
- A random limit \(\pi_{I(\omega)}\) is not its barycenter \(\sum_i p_i\pi_i\). Both the necessity and the six-state obstruction use pathwise a.s. equality.
- Positive class probability is defined through actual `canonicalPathLaw`, not finite sampled reachability, and no positive threshold is imposed.
- Substituting a wrong target or post-hoc enlarged family is not authorized. The original basin, region, descriptor, model and mode remain fixed.
- The mathematical result assumes the *encoded* finite Markov model. It does not identify real-world transition kernels, validate preregistration chronology or provide a general decision algorithm for models given in arbitrary representations.
- Research modules may use the repository's transitive existing axiom allowlist `propext`, `Classical.choice`, and `Quot.sound`, never new custom axioms, placeholders or proof bypasses.

## Adversarial controls

`verification/research/test_lane_c3_characterization.py` independently recomputes six-state exact rational stochastic rows, stationary vectors and class-entry weights; it checks observed Boolean collapse vs physical identity separation, the A-only basin with identity descriptor, wrong target, tiny positive weights, zero probability/unreachable class, periodic marginals vs empirical occupation, failed nontriviality/invariance, and an always-true custom mode.

The tests are finite computational negative controls, **not** a proof of general almost-sure convergence. The Lean theorem/witness is the formal gate.

## Diff and release discipline

**Allowed:** new C3 modules under `PermanssonResearch/MultipleLimit/`, direct imports in `PermanssonResearch.lean`, the C3 research test, this ledger, and narrow research-roadmap references.

**Protected:** `PermanssonLean/`, `PermanssonLean.lean`, `paper/`, `application/`, original CI/workflow/Lean toolchain/manifest, historical evidence and provenance/release hashes. The immutable original source snapshot remains untouched.

**Merge criteria:** C54-01 through C54-05 compile with their **unweakened statements**; both Lean targets and full transitive axiom audit pass; all research regression tests pass; all four GitHub PR workflows pass on the final source SHA and exact synthetic merge; an independent source/hypothesis review completes; frozen-file audit passes; a deliberate user-controlled merge decision is recorded.

**Checkpoint evidence (to complete after verification):**

- Base main: `f2bbd96cb3e89dbc73d08bd675cd327b4fd752f2` (merged PR #53)
- Final proof head: **PENDING**
- Tested synthetic merge: **PENDING**
- Research Lean: **PENDING**
- Original Lean: **PENDING**
- Executable verification: **PENDING**
- Application contract: **PENDING**

Do not mark this ledger formally verified ahead of the checks.
