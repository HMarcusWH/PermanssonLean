# C11-A — Exact rational recurrent-class stationary certification

**Research-only draft PR #62**, base `main@57aa4eb3b58df770630f16b04940cb5933317709` (merged C10). This ledger describes implementation obligations and progress; no uncompiled theorem, generated fixture or CI count is claimed as verified.

## Objective and established dependencies

For each checked nonempty finite rational Markov matrix `L`, compute `C10.bottomClasses L`. A reported all-state rational vector `v_C : Fin n → ℚ` for a reported bottom class `C` must satisfy (i) `0 < n`, (ii) exact bottom-class membership, (iii) `v_C ≥ 0`, (iv) `∑ v_C = 1`, (v) zero mass off `C`, and (vi) the **complete** left-stationarity equation `v_C(y) = ∑_x v_C(x)*L(x,y)` for **every** state. Membership in a computed bottom SCC cannot be replaced by a nonchecked label.

C2 already proves the existence and uniqueness of a stationary probability measure *supported on each genuine recurrent class*: `FiniteClassInvariantMeasure.exists_unique_stationary_probability_on_class`. C10 already proves `RationalBSCCNative.bottomClasses_native_iff` for the actual D0 typed action-replacement model. C4 already identifies the original six-state class stationary vectors. C11-A must **reuse**, not reprove, these facts.

## New modules and theorem contract

- `C11ClassStationaryCertificate.lean`: `ClassStationaryCandidate`, `ClassStationaryConditions`, decidable `checkClassStationary`, `checkClassStationary_sound`, dimension/recurrent/positivity/support/balance extraction. No assumption that an arbitrary supplied vector is stationary.
- `C11StationaryFamily.lean`: class-key `List.Nodup`, exact equality with `bottomClasses`, and individual accepted entries. `checkStationaryFamily_sound` and `checked_family_complete` reject omitted, extra and repeated classes.
- `C11TypedStationaryBridge.lean`: rational-to-real reindexing on the **actual** `JointState Unit (Fin n)`, typed singleton kernel equality, whole-measure invariant and support transport, `checked_stationary_eq_native` for **each member matrix L and baseline K₀**. `checked_stationary_positive_on_class` must follow from irreducibility and C2's existing results, not an assumed strict-positivity flag.
- `C11ObservedStationary.lean`: exact Boolean stationary true share `q_C(h)`, complementary false share, zero/one/mixed-label trichotomy; a proof equating q with the original typed C2 class stationary descriptor-pushforward mass of `true`. No equivalence between stationary share and C10 eventually-always-true event is claimed for mixed classes; use C2's already-proved occupation strong law.
- `C11SixStateWitness.lean`: the **frozen** C4/C10 baseline matrices and observation descriptor, actual A={2,3} and B={4,5} stationary vectors `(0,0,1/2,1/2,0,0)` and `(0,0,0,0,1/3,2/3)` (share 1); an actual full-disruption member's false singleton {1} (share 0). Note baseline state 0 and 1 are **transient** and must not be reported as recurrent classes.

All five files must be directly imported by `PermanssonResearch.lean`. The branch contains candidate modules, but CI is the authority on their proof validity.

## Independent numerical implementation

- `c11_stationary_execution.py`: closed exact rational input; deterministic positive-edge closure and BSCC list; rational Gaussian elimination on `(I - L_Cᵀ)` with one row replaced by the unit-mass constraint; full-state extension and balance validation; canonical `Permansson.C11.stationary-research.v1` report.
- `c11_verify_stationary.py`: independent DFS SCC enumeration, exact nonnegative/unit-mass/off-class/all-state-balance/share verification and hash/schema checks. It never calls the producer's solver.
- `c11_emit_stationary_lean.py`: complete literal kernel, descriptor, class vectors and shares, genuine `checkStationaryFamily = true` theorem checked by `lake env lean` and transitive axioms printed. External JSON parsing and Python code are not Lean-verified.
- `test_lane_c11_stationary.py`, `test_lane_c11_lean_receipt.py`: discovered exact small-model, negative, state-relabeling, completeness and generated kernel-proof regressions.

No approximate float thresholds. Explicit operational limits are 1–12 states, 2 MB input, 256-bit input rationals, 8192-bit intermediate/result rationals; a resource limit is not a mathematical nonexistence result. Producer/checker input parsing is shared and outside the formal Lean proof.

## Frozen geometry and semantics

- `RationalMarkovMatrix` is not an arbitrary external strategic world. Actual alpha-only D0 realization must be proved using `inducedKernel_encodedEntry` and `rationalStrategicIntervention_applied` with P and U fixed.
- `C11` is a **class-stationary occupation** calculation. A periodic class may have stationary true-share `1/2` although C10's *eventually always true* probability is zero.
- No blanket Exact GR or PR certification: original Assumption 4.1, exact region invariance, basin, descriptor, target, `almostSureWeak` mode and original constitutive B₁ remain separately certified premises.
- No general total rational reference solver theorem in this PR (planned C11-B); no verified JSON decoder; no causal/empirical model identification.
- Original `PermanssonLean/`, C1–C10 sources and C10 v1.1 audited spec, v0.1.8 paper, application schema, pinned Lean/mathlib manifest and existing workflows must remain untouched.

## CI, review and release gates

Require the *actual final PR head and GitHub synthetic merge* to pass the four existing workflows: Research Lean (including all discovered C11 tests, 3-axiom transitive audit limited to `propext`, `Classical.choice`, `Quot.sound`, new root import check, source firewall, D0-F and C10 original/mixed generated receipt rechecks), Original Lean, Executable verification, and Application contract Ubuntu/Windows. The prior baseline was 552/552 research regressions, 309 directly imported modules and 3,582 audited declarations; new totals must be **observed**, not invented.

Review the actual C11 theorem statements and their hypotheses, independent checker, malformed-input adversaries, and the truth/mixed distinction. The author-approved Codex review waiver for PR #61 does not authorize waiving PR #62 review. PR #62 stays draft and unmerged until explicit author permission.

## Interim compiler/debugging checkpoints (historical)

- C11 root imports were initially appended after the library module documentation. This was a source-layout failure and was corrected by moving all five imports above that documentation.
- [Research Lean #38656112328](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38656112328) demonstrated that the new constructive class-condition decider compiled after repair; its remaining error was an incorrectly applied conjunction projection in `C11StationaryFamily.checked_family_no_extra`. That specific proof-application bug was corrected subsequently.
- [Research Lean #38656310783](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38656310783) likewise compiled the class checker but failed at the **same old family-checker source**, before the family fix commit.
- The theorem interface for actual C2 typed class stationary measures now exposes a checkable nonempty-state instance where the type itself requires it; strict class positivity derives nonemptiness internally from the accepted positive-dimension certificate.
- In a local, independent Python reconstruction of the committed numerical implementation, the 15 planned C11 exact-rational regression cases passed, including the six-state and adversarial cases. This **does not** certify GitHub's discovered Python tests, compiler-driven Lean fixture, or source provenance.
- **No final exact-head Research Lean success is claimed at this stage.** The current live PR head and its latest workflow records—not these earlier attempts—control release readiness.

