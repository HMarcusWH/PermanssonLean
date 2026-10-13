# Lane C6 — frozen observed-event strategic response

**Research PR:** [#57](https://github.com/HMarcusWH/PermanssonLean/pull/57)
**Base:** `main@ea821bb253cd25d038a4454ee4d833232c8d7b19` (merged C5 PR #56).
**Status (13 October 2026):** The mathematical-source checkpoint is **verified** by Research Lean, transitive axiom audit, 187 exact rational regressions, source firewall and an assistant-conducted source review. PR #57 remains **DRAFT / UNMERGED** until all four final documentation-head CI workflows pass; this is not external scholarly peer review.

## Mathematical objective

This research-only extension constructs the first typed Lane-C intervention whose effect is grounded in the **same predeclared observed regime descriptor** used in the baseline original Exact GR.

C2 proved the a.s. random class occupation law; C3 its exact original single-target GR characterization; C4 the genuine six-state class stationaries and periodic marginal nonconvergence; C5 sharp positive-probability observed-limit atoms. C6 neither re-proves those results nor modifies the original `IsExactGeneratedRegime` / `IsGeneralizedPermanssonRegimeRelative` definitions.

Freeze the original six-state `typedModel`, the original proper-region `observedSpec` with `h=observedDescriptor`, and the genuine ex-ante basin/comparison set `{u,a0}`. The global path event and property are:

```text
E_h      := {w : ∃N ∀n≥N, h(w n) = true}
ψ_h(ρ)  := (ρ.toMeasure E_h).toReal
```

**The event is chosen ONCE, independently of the baseline or intervened kernel.** Neither model's noncomputably chosen recurrent-class representative occurs in its definition. An unchanged descriptor's whole-path law, not merely a matrix, supplies the comparison.

## Exact intervention and witness

The source six-state rational transition matrix is the frozen C2 typed alpha/P/U model `sixStateMatrix`. The replacement `disruptedMatrix` changes **only these two action-selection rows**:

```text
u  -> u  with probability 1
a0 -> u  with probability 1
```

Every other row is unchanged, including the periodic a1→a0 transition and the physical B recurrent block. It is installed using `ReverseSolver.FiniteStrategicRealization.rationalStrategicIntervention` and `researchActionFamily`, under which alpha-selection changes are admissible by construction; the exact same P (world action-copy kernel) and U (Unit-memory update) are proved unchanged. This permissive constructed family is **not a claim about external intervention eligibility**.

For each original comparison state, the now compiled source proves:

| Start | Baseline P(E_h) | Intervened P(E_h) | constitutive effect |
|---|---:|---:|---:|
| u | 1 | 0 | 1 |
| a0 | 1 | 0 | 1 |

Thus the **proved** positive uniform margin is **1**; the original `IsUniformGeneralizedPermanssonRegimeRelative` is established using the separately proved original baseline Exact GR and the original typed intervention requirements.

The unchanged frozen Boolean observed sharp family in C5 has one baseline target `{δ_true}`. The changed intervention makes `u` absorbing; `u` is observed `false`. Class B remains a genuine recurrent class but is unreachable from the original comparison basin after intervention. An independently compiled C2/C5 proof establishes that the **intervened** sharp observed family is precisely `{δ_false}`. In particular, any attempted baseline-selector substitution is invalid. The intervened process also cannot satisfy the original frozen target `δ_true` and the identical original mode.

## Source theorem dependency graph

1. `FrozenObservedEvent.lean`: kernel-independent countable eventual-observation event and its measurability; the corresponding `RegimePropertyMap`; true/false-event disjointness and direct C2 recurrent-state bridge.
2. `ExactSixStateTargetDisruption.lean`: exact sparse rational replacement, nonnegative/normalized rows, canonical typed alpha/P/U matrix equality, held-P/U identities, u-absorbing singleton and original proper-region closure, genuine time-one canonical marginal and almost-sure eventual-u from both basin starts.
3. `TypedEventResponse.lean`: same frozen descriptor property evaluated under both actual infinite path laws; baseline event mass one for every point start and intervened event mass zero at u and a0.
4. `ExactSixStateConstitution.lean`: nontrivial original two-point comparison, exact effect 1 and margin 1, original unweakened `IsUniformGeneralizedPermanssonRegimeRelative`, ordinary relative and family-level original PR consequences.
5. `SharpFamilyResponseWitness.lean`: full independent intervened canonical occupation convergence to δ_false, original C5 sharp family change, and obstruction of the original single-target Exact GR under intervention. C5's previously proved baseline singleton remains unchanged.
6. `GroundedC6Response.lean`: frozen relevance map `g(y)=(1_B(y),h(y))`, global factorization of the same `ψ_h`, and original `IsGroundedPermanssonRegimeRelative` certificate. This does NOT automatically claim the stronger confirmatory `PR_g` subclass.

All new modules must be imported directly by `PermanssonResearch.lean`. The frozen existing C1–C5 theorem files cannot change.

## Independent exact rational adversarial suite

`verification/research/test_lane_c6_typed_response.py` must derive closed communicating classes and actual eventual class absorption weights using independent exact-`Fraction` positive-edge graph analysis and rational Gauss–Jordan solving, not by simulation or copying Lean proof claims.

Twenty tests check genuine source rows, exactly two changed alpha rows, baseline A/B recurrent classes, changed {u}/B recurrent classes, baseline/transformed destination weights, frozen label response, effect=1 and margin=1, baseline/intervened C5 sharp family, region closure, fixed P/U semantics, identity intervention zero effect, one-row-only zero uniform margin, B-destination physically changes but observation does not, rational mixed starts, still recurrent but unreachable physical B, finite hit versus eventual label, invalid baseline-selector transfer, invalid data, and tiny strictly positive atom weights.

Computational regressions are independent falsification controls, NOT Lean proof, real-world empirical certification or automatically verified Python-to-Lean equivalence.

## Scientific and release boundaries

- Finite-state homogeneous Markov kernels, literal canonical infinite Ionescu–Tulcea path laws and typed alpha/P/U model construction; arbitrary nonhomogeneous or infinite-state generality is NOT proved.
- Properties, observation, basin, comparison set and original Exact GR target are held fixed. No post-hoc property drift.
- The original baseline Exact GR must be independently established (from C2/C3). The intervened model is diagnostic; it is not assumed to remain a GR.
- Neither C5's sharp family nor the original C3 theorem is silently applied to the intervened chain before proving all needed new-chain hypotheses.
- A property-relative, grounded PR and a confirmatory `PR_g` have different logical gates; never infer the latter from the former.
- Original `PermanssonLean/`, paper, application, toolchain, manifest, workflows, C1–C5 proof sources and historical release hashes remain unchanged.
- Axiom allowlist: exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, or custom axioms. Compiler lint/deprecation warnings are separately audited.
- A GitHub assistant COMMENT review, if completed, is **not** independent human scholarly peer review.

## 6. Verified mathematical-source checkpoint — 13 October 2026

- **Mathematical-source HEAD:** `2f7a756bd1784c855039bd73d7c8c114b5817e36` (after two focused compiler-proof repair commits, `85c98f8d5107346d85f8603a19be0721953c69be` and `2f7a756bd1784c855039bd73d7c8c114b5817e36`).
- **GitHub PR synthetic merge actually checked out by Research Lean:** `5099e7b635efb21baacc9e113f13992a067fb561`, merging that source HEAD into `main@ea821bb253cd25d038a4454ee4d833232c8d7b19`. The checkout SHA is present in the Research Lean job log.
- **[Research Lean #38328602237](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38328602237): SUCCESS.** The complete research root compiled across **3,953** reported build jobs. Transitive axiom audit checked **2,865 declarations** with only `propext`, `Classical.choice`, `Quot.sound`. All **187/187** research regressions passed (167 inherited + **20 C6** independent exact-`Fraction` adversaries). D0-F deterministic golden regeneration and independent rechecks passed. Original default `lake build`, direct-import coverage (**246/246** modules), and the `sorry`/`admit`/custom-axiom source firewall passed.
- **[Executable verification #38328602271](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38328602271): SUCCESS** at the same mathematical-source head.
- **[Application contract #38328602384](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38328602384): SUCCESS** for both Ubuntu and Windows at the source head. These are software-contract tests, not empirical model identification.
- **Original Lean #38328602122** was still awaiting a GitHub-hosted runner at the source-checkpoint review. The original default build also passed within Research Lean; the four-workflow final-head gate below remains mandatory.
- **Source/hypothesis review:** [assistant-conducted COMMENT review #5497596039](https://github.com/HMarcusWH/PermanssonLean/pull/57#pullrequestreview-5497596039), explicitly anchored to the immutable mathematical-source head. No blocking issue found in the inspected C6 changes. It is **not** independent scholarly peer review or a GitHub APPROVE review.
- **Changed-file firewall:** The PR changes six C6 research modules, the direct research root, the exact-`Fraction` adversarial suite, this ledger and the research build guide. The original `PermanssonLean/`, `PermanssonLean.lean`, existing C1–C5 proof sources, paper, application, toolchain, manifest, workflows, original historical release records and schemas were not modified.
- **Nonblocking warnings:** existing Lean style/linter suggestions and GitHub Node deprecations. `SharpFamilyResponseWitness` retains one harmless `haveI` style warning. None weakens a theorem or adds an axiom.

**Final release-documentation gate: PENDING.** This ledger/build-guide update produces a NEW PR head after the verified mathematical-source commit. All four workflows (Research Lean, Original Lean, Executable verification, Application contract Ubuntu/Windows) must pass on the exact final documentation HEAD and its GitHub synthetic merge. Record those SHA/run links in PR #57, not by silently attributing old runs to a new commit. The PR remains draft and unmerged; merge requires separate explicit author authorization.
