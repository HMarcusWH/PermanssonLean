# Permansson v0.2.0 — Research Proof Acceptance Ledger

**Scope: additive mathematical research extensions only.** This ledger does
not modify the original v0.1.8 theorem corpus, proof manifests or paper.
Check merged [PR #64](https://github.com/HMarcusWH/PermanssonLean/pull/64), draft [PR #65](https://github.com/HMarcusWH/PermanssonLean/pull/65), and the exact HEAD for current status. A dated proof checkpoint proves only
the encoded declarations on its matching source SHA; it is not a v0.2.0 paper
release or independent third-party review.

## Current merge status and active C-Exit candidate (15 October 2026)

PR #65 merged `main@af9d1084664e9e51f7aba0045e98532e58c18829`, and all four post-merge main workflows passed. PR #66 remains **DRAFT, UNVERIFIED**. Its [C-Exit theorem-to-source ledger](LANE_C_EXIT_ROUTING.md) tracks `RegimeExit/ExitEvents`, `ExitSubkernel`, `ExitRouting`, `ExitConservation`, `QSDDestination`, `ExitModels`, 22 independent exact-Fraction adversaries, and the focused smoke workflow. Do not promote v0.2.0 Definition 4.2d or Theorem 4.2e or QSD corollary while any proof/CI gate is incomplete. PR #67 switch/PR constitution remains OPEN.

## Historical source-to-theorem ledgers (dated snapshots)

## Current merged baseline and B2 draft

Main `a9d914520c68741a23cda89357499f3cf3f1500a` has merged A2. All four post-merge main workflows passed on this exact SHA; this is not an acceptance of the new B2 branch.

**B2 source crosswalk (PR #65; unverified until exact-head CI):**

| Obligation | Source declarations | Firewall |
|---|---|---|
| Four genuine 00/10/01/11 path-law corners | `GrammarRobust/SequentialEffects.lean`: `FourCornerProtocol`, `jointEffect_le_action_add_condUpdate`, `jointEffect_abs_action_sub_condUpdate_le`, symmetric theorems | Three independently admitted strategic interventions; identical frozen P and ψ |
| Uniform conditional bounds | `GrammarRobust/ConditionalMargins.lean`: `condUpdateMargin_ge_joint_sub_action`, symmetric bound, strict-positivity corollaries | Uniform singleton *upper bounds*, original certified B₁; no zero-infimum promotion |
| Original baseline bridges | `ConditionalMargins.lean`: `jointMargin_eq_constitutiveMargin`, action/update counterparts | Only baseline-relative effects identify original PR constitution |
| Strong singleton-null identity | `jointOnly_conditionalMargins_eq_jointMargin` | Pointwise zero on every original comparison state |
| Vector subclass | `GrammarRobust/InteractionVector.lean`: `interactionVector_norm_le_condUpdate_add_update`, symmetric bound, `uniformInteractionMagnitude_le` | Normed additive output, explicit finite supremum bound |
| Admissible block grammar repair | `GrammarRobust/SequentialBlockBridge.lean`: `fromAllowed`, effect/margin bridges | Independent accepted blocks and four physical action/update atom equations; no downward closure |
| Canonical Boolean witness | `GrammarRobust/SequentialBooleanBridge.lean` | Original `BooleanPersistence` and `BooleanEffects` reused, not re-proved as new discovery |
| False-claim witnesses | `GrammarRobust/SequentialAdversaries.lean` | Two-time path-law property: zero singleton infima, joint margin one, conditional update margin zero; real vector I=2 versus scalar remainder 0 |
| Exact deterministic independent checks | `verification/research/test_lane_b2_sequential_effects.py` | 18 exact-rational model-executed cases; Python is not a Lean theorem |

See [B2 verification ledger](LANE_B2_SEQUENTIAL_EFFECTS.md). Do not promote a green earlier commit to a later source head.

## A2 source-to-theorem crosswalk

| Proposed v0.2.0 claim | Exact research declarations / source | Mandatory limits |
|---|---|---|
| Proposition 5.5 primitive row errors | `Perturbation/PrimitiveTV.lean`: `inducedKernel_tv_le_primitive_sum` and the common-subkernel construction | Actual typed α→P→U; each row bounded; suitable `CountableOrCountablyGenerated` instances; event-supremum TV |
| Frozen matched strategic protocol | `Perturbation/PrimitiveModelPair.lean`: `PrimitiveModelPair`, world-fixed lemmas and transported comparison-set states | P may differ *between* models; both interventions separately admissible and fixed-P within model; target and component equality is necessary, not empirical equivalence |
| Finite-prefix propagation | `Perturbation/PrimitiveMargin.lean`: `PrimitiveErrorBounds.finitePrefix_tv`, `finitePrefix_tv_le_linear` | T transitions, common point start, not an infinite-path bound |
| Factor-one bounded score margin | `PrimitiveMargin.lean`: `primitive_constitutiveMargin_abs_le`, `primitive_positive_finiteMargin` | Only actual measurable [0,1] bounded finite-prefix score under frozen B₁ |
| Full conditional CQ-1 transfer | `PrimitiveMargin.lean`: `transportPrimitiveFiniteConstitutiveCertificate` | Original finite-persistence certificate, full region-wide persistence, κ greater than both errors, `clampedPersistenceError`; still not Exact GR/PR |
| Generic metric-valued Lψ subclass | `Perturbation/PrimitiveLipschitz.lean`: `TVLipschitzPrefixProperty`, `primitiveLipschitz_constitutiveMargin_abs_le`, `primitiveLipschitz_constitutiveMargin_le_linear`, `primitiveLipschitz_positive_finiteMargin` | Lipschitz property is a *hypothesis* over genuine probability laws; not all regime properties satisfy it |
| Numerical reporting error | `PrimitiveMargin.lean`: `reportedPrimitiveMargin_abs_le` | Independent b₀/bJ uncertainty for a reported profile; not equality to exact second-model margin |
| Adversarial boundaries | `Perturbation/PrimitiveAdversaries.lean` and `verification/research/test_a2_primitive_tv.py` | Typed zero-horizon, changed-world same-P rejection, and QSD firewall; 18 proposed finite exact-fraction tests, with the added off-graph and non-Lipschitz controls pending final-head CI |

All `Perturbation/*.lean` modules must be imported *directly* in
`PermanssonResearch.lean`, and compiled with the pinned Lean 4.34.0/mathlib.
Do not insert custom axioms, `sorry`, `admit`, or hidden `native_decide`.

## Dated verification checkpoints

- Source `fe38bd4d1fa7f77e8997fec27ad91e1b3d3e1bbb`: [Research Lean #38728397965](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38728397965) **PASS**; 4,034 jobs, 3,802 declarations with only `propext/Classical.choice/Quot.sound`, 594/594 tests, 319 direct imports, C10 bound-source evidence, D0-F golden and source firewall. Also [Original Lean](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38728399023), [Executable](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38728398041), [Application contract](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38728397983), and [A2 smoke](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38728392060) **PASS**.
- Source `db1c7e78ed910ee590201ea01518ce50bad44d52`: [focused A2 smoke #38728807954](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38728807954) **PASS**, including 16/16 exact-rational adversaries. This is a *focused* checkpoint; the separately triggered Research Lean gate must be checked independently.
- Later source additions to `PrimitiveLipschitz.lean`, this ledger and any other files: **no PASS is inherited**. Verify the actual final source SHA, the GitHub synthetic merge, all four mandatory workflows, original build, A2 smoke, axiom audit, source firewall, and substantive code review before marking the release head certified.

## Negative claims and nonvacuity firewall

- Positive finite-horizon constitutive margin does **not** certify Exact GR, exact invariance, long-run convergence or generalized PR status.
- The converted persistence error may equal one. Reporting **nonvacuous** persistence requires independent proof of strict survival floor, not merely clamped `η' ≤ 1`.
- A model error `P ≠ Ptilde` is not a strategic intervention. Global row controls must include intervention-reachable rows, not merely observed baseline support.
- No theorem establishes identification of primitive errors, causal efficacy, empirical model selection, political predictions, safety, or originality.
- The optional sharper sequential-product/common-coupling primitive bound, A3 Wasserstein long-run closure and other v0.2.0 lanes are **OPEN**.

**Merge gate:** maintain draft until every required final-head proof and test is green, any source findings are resolved, and the author explicitly authorizes merge. Review by this assistant must not be labeled independent Codex/human peer review.
