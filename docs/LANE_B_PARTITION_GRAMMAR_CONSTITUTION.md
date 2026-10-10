# Lane B — Finite partition-grammar strategic constitution

**Release scope:** finite disjoint, measurable α/U physical atoms; finite semantic
component partitions; admissible finite blocks; real canonical α→P→U Markov
kernels; genuine nonbijective coarse/fine component changes.

**Research PR:** [#51](https://github.com/HMarcusWH/PermanssonLean/pull/51).
**Status:** draft; B1–B13 concrete Lean witnesses have compiled on the
prior code head. Final-head CI and substantive independent review remain
gates before promotion. The frozen
Permansson v0.1.8 mathematical core and application claim schema remain intact.

## Mathematical implementation

The physical atom bank supplies measurable row-local replacement Markov
kernels, together with disjointness of masks within each primitive. A separate
partition grammar groups these immutable atoms into semantic components, and
freezes an arbitrary (not necessarily downward-closed) allowed-block predicate.

An admitted block constructs a full typed strategic-world model:
`atomicBlockModel` and `blockModel` apply the selected α/U row patches,
retain the exact world primitive P, and expose an admissible original typed
jointStrategic intervention via `OriginalInterventionBridge`. `AtomicSelection`
proves the selected-row result and order-independent construction.
`EmptyBridge` and `SingleTargetBridge` prove whole-model baseline and typed
singleton correspondence. The original path-law `RegimePropertyMap` and
`constitutiveMargin` are reused, not replaced.

`Minimality` proves existence of a minimal allowed positive block inside
any given allowed positive block. `IsomorphicTransport` requires an exact
proper-subblock order isomorphism. `Refinement`, `RefinementTransport`,
`EffectTransport`, `ConstitutionTransport` and `ImageMinimality` prove
what survives real many-to-one component coarsening, and distinguish
image-relative minimality from global fine minimality.

`BooleanBaseline`/`BooleanOccupation` give the nontrivial finite Boolean
baseline's actual canonical almost-sure weak occupation-law proof and exact GR.
`BooleanDynamics` computes the genuine α/P/U intervened kernels.
`BooleanPersistence` proves the infinite-path persistence property and
original relative typed PR certificate; `ConstantDynamics`,
`BooleanOneStepEvents`, `MarginFromEffects`, and `BooleanEffects` derive
actual path-law OR/AND/XOR diagnostic values and margins.

## B1–B13 independent adversarial acceptance matrix

The matrix below identifies **intended concrete proof sites**. For newly
added witness modules, check the actual final-head Research Lean build and
axiom audit before marking the release certified. The concrete proof package
compiled on the immediate pre-release head.

| Case | Scientific failure being tested | Compiled-proof target / exact fixture |
|---|---|---|
| B1 | Joint-only OR effect, even with null singleton effects | `BooleanEffects.or_singleton_margins_zero`; `or_joint_margin_one`; `BooleanMinimalityCases.or_joint_minimal` |
| B2 | AND has two incomparable fine minimal constitutive blocks | `BooleanMinimalityCases.and_action_minimal`, `and_update_minimal`, `and_joint_not_minimal` |
| B3 | XOR loses a positive singleton effect when adding a second atom | `BooleanEffects.xor_nonmonotone_margins` |
| B4 | Identical baseline does not fix an atom-bank intervention response | `AlternativeBankWitness.same_baseline_different_joint_laws` on two real banks and same P |
| B5 | Effect-matched arbitrary block-label bijection need not preserve minimality | `InvalidBijectionWitness.equal_margin_but_invalid_minimality` and `invalid_swap_does_not_preserve_proper_inclusion` |
| B6 | Fine/coarse with different component counts can select the same physical intervention law | `BooleanModel.true_refinement_equality`; `Coarsening.pathLaw_lift_eq` |
| B7 | A coarse minimal block may lift to a fine nonminimal block | `BooleanMinimalityCases.B7_minimality_not_preserved_by_refinement` |
| B8 | Coarse XOR-null block can hide fine positive singleton blocks | `BooleanMinimalityCases.B8_coarse_hides_positive_fine_singleton` |
| B9 | Overlapping full-row α patches are inadmissible in the disjoint atom bank | `AdversarialAdmission.overlapping_action_rows_rejected` |
| B10 | Selecting one action-row patch leaves another row unchanged | `TwoActionRows.row_false_selected`, `row_true_unchanged` |
| B11 | A syntactic block can be rejected by the frozen grammar | `AdversarialAdmission.forbidden_block_has_no_certificate` |
| B12 | Real nonidentity order-compatible relabeling, not just identity matching | `RelabelingWitness.relabeled_update_model_eq` and `relabeled_zero_not_original_zero`; generic minimality transport in `IsomorphicTransport` |
| B13 | Exact GR and typed PR on infinite-path persistence, not an arbitrary time-one proxy | `BooleanOccupation.exactGR`, `BooleanPersistence.genuineRelativePR` |

**B12 scope:** The concrete relabeling witnesses prove nonidentity component
semantics, exact full-model equality for a matched singleton, preservation and
reflection of proper-subblock order for **every** finite subset, and an
original-path-law minimal constitutive AND block. The generic order-isomorphism
transport theorem remains conditional on the proved matching property profile.
**B5 scope:** The invalid block-label swap now has a theorem proving that the
**entire** AND constitutive-margin profile is invariant over every admissible
fine block, while its proper-subblock order and minimality preservation fail.

The independent exact-rational Python witness regression lives in
`verification/research/test_lane_b.py`; it never substitutes for the Lean
theorems listed above.

## Promotion and safety gates

1. All B1–B13 concrete tests must compile on the final-head source, with
   the B5/B12 scope restricted to the exact demonstrated theorems.
2. Final-head `lake build` and `lake build PermanssonResearch` succeed.
3. Research-root import coverage and original application contract pass.
4. All transitive axioms are in `propext, Classical.choice, Quot.sound`.
5. Neither `sorry`, `admit`, custom axiom nor world-kernel modification exists.
6. Both the research regressions and all original-core verification pass.
7. Review resolves whether the examples substantiate the contract's claimed
   classification and whether any formally different grammar is mislabelled
   as a semantics-preserving intervention mapping.
8. A **recorded substantive mathematical/code review** is required before
   marking PR #51 ready and merging. CI passing is not a substitute.

The release asserts only the finite **disjoint component-partition** subclass.
It does not establish overlapping-patch conflict resolution, causal
identifiability, arbitrary quotients, all grammar changes, or deployment
readiness. Historical v0.1.8 statements and papers remain frozen.
