# Lane B — finite partition-grammar strategic constitution

**Research-only, draft PR #51. Not part of the frozen v0.1.8 mathematical core.**

This is the implementation ledger for the audited v2 Lane B design. All
claims remain incomplete until the theorem source, nontrivial witnesses,
adversarial tests, final-head CI and substantive review satisfy the
acceptance contract. A compilable structure without the downstream
certificates is *not* a completed mathematical lane.

## Paper and scientific boundary

Permansson v0.1.8 Section 5.4 treats strategic component attribution as
grammar-relative. A compound block may change a regime-defining property
even when its singleton parts do not. The new finite subclass uses a bank of
disjoint measurable row-local changes to action-selection alpha or strategic
update U. All worlds share the original world-transition kernel P. It makes
no equilibrium, empirical-identification, or arbitrary intervention claim.

## Distinguish physical atoms from semantic components

An `AtomicBank` stores the measurable row masks and genuine replacement
Markov kernels for action and update atoms, with disjointness required
within each primitive. A `PartitionGrammar` allocates every atom to
exactly one semantic component. The grammar also fixes the admitted blocks;
it does not assume admission is downward-closed.

`atomicBlockModel` constructs both replacement strategic kernels from
the physical selection, and copies P from the frozen baseline. The same
expanded physical atom selection must give the exact same strategic-world
model independent of the semantic component partition.

## Implemented source modules (subject to final-head Lean check)

- `AtomicBank.lean`: measurable physical row-patch bank and target typing
- `AtomicApply.lean`: actual piecewise Markov-kernel construction
- `AtomicLocality.lean`: untouched-row preservation for finite patch folds
- `PartitionGrammar.lean`: admitted blocks and exact atom expansion
- `BlockModels.lean`: real induced model with world P held fixed
- `OriginalInterventionBridge.lean`: constructed original `.jointStrategic` intervention
- `BlockConstitution.lean`: original constitutive effects and uniform margins
- `Minimality.lean`: finite least-cardinality admitted positive subblock
- `Refinement.lean`: true many-to-one component grouping and atom expansion
- `RefinementTransport.lean`: equality of actual typed models and canonical laws
- `EffectTransport.lean`: effect and margin equality under matched refinement
- `IsomorphicTransport.lean`: preservation of minimality under proper-subblock order equivalence
- `BooleanModel.lean`: independently constructed finite alpha/P/U witness and coarse/fine grammar
- `BooleanBaseline.lean`: nontriviality and invariance gates for the baseline GR

All source declarations must compile before any of these are credited as proved.

## Mandatory remaining full-release gates

1. Prove selected-row behavior and ordering independence for the actual patched kernels.
2. Prove empty-block *whole-model* identity and typed singleton target bridges.
3. Prove effects/margins equal original v0.1.8 path-law semantics, not a second definition.
4. Prove full fine/coarse image-relative minimality and order-isomorphic global minimality.
5. Prove the baseline Boolean example's genuine almost-sure weak occupation limit.
6. Prove a valid `IsExactGeneratedRegime` and original typed `IsGeneralizedPermanssonRegimeRelative` with an infinite-path persistence property.
7. Prove complete OR/AND/XOR countermodels, disjoint action-row fixture, and B1–B13 adversarial claims.
8. Run independent finite-state exact regressions in `verification/research/test_lane_b.py`.
9. Verify `lake build`, `lake build PermanssonResearch`, root direct imports, placeholder/custom-axiom scan, transitive axiom audit, and the four final-head workflows.
10. Obtain substantive PR review; preserve v0.1.8 core, toolchain, paper, application schema and historical proof snapshot.

Do not mark the PR ready or merge solely because its first source files compile.
Do not infer real-world identification or causal feasibility from a formally
admitted row patch.
