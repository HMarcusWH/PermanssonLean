# Guide ↔ source module crosswalk

[Reference guide v1.1.1](Permansson_Mathematical_Reference_Guide_v1.1.1.md) · [full path-level manifest](MODULE_MANIFEST_v1.1.1.json) · [case routes](CASE_SOURCE_CROSSWALK.md)

**Direct reference** means a path or unambiguous basename actually occurs in that chapter. **Not cited** means this extractor found no direct path; see the folder-based suggestions in the complete manifest. Linking a module does not certify its theorem scope.

| Chapter | Heading | Direct existing source files | Lean / Python among them |
|---|---|---:|---:|
| A01 | A01. What Permansson is, and is not | 5 | 2 |
| A02 | A02. Declare a property before computing | 2 | 2 |
| A03 | A03. Source, release and authority map | 7 | 2 |
| A04 | A04. Installation and the first independently checked calculation | 3 | 0 |
| B01 | B01. The typed strategic-world model | 2 | 2 |
| B02 | B02. Induced kernel, initial law, and path law | 4 | 4 |
| B03 | B03. Frozen regime specification and descriptor occupation | 2 | 1 |
| B04 | B04. Survival, killing, quasi-regimes and exact invariance | 0 | 0 |
| B05 | B05. Typed strategic interventions and constitutive dependence | 1 | 1 |
| B06 | B06. Perturbation margins and representation discipline | 7 | 6 |
| B07 | B07. Canonical finite probability laws and exact-rational bridges | 6 | 6 |
| B08 | B08. Recurrent classes, multiple limits and stationary families | 2 | 1 |
| C01 | C01. D0: fixed finite menus of admissible interventions | 7 | 6 |
| C02 | C02. D1: state-dependent finite-horizon Bellman control | 8 | 6 |
| C03 | C03. D1: histories, nonstationarity, and typed path-law transport | 13 | 11 |
| C04 | C04. D2: reaching, residing, avoiding, and switching | 7 | 5 |
| C05 | C05. Risk constraints, occupancy flows, exact LP and infeasibility | 6 | 5 |
| C06 | C06. Beliefs, partial observation, information chronology and private draws | 9 | 6 |
| C07 | C07. Robust alternatives, rectangular uncertainty and metric perturbation | 6 | 4 |
| C08 | C08. Intervention grammars, interaction and constitution | 6 | 4 |
| C09 | C09. Quotients, abstract states, nonlinear properties and scope-specific witnesses | 12 | 9 |
| C10 | C10. Exact rational evaluation and proof-carrying receipts | 7 | 6 |
| C11 | C11. Exact graph reachability, recurrent classes and absorption | 8 | 7 |
| C12 | C12. Infinite-horizon safety and controlled invariant cores | 6 | 6 |
| C13 | C13. Occupancy polytopes, rational extreme points and certificates | 10 | 8 |
| C14 | C14. Multiagent protocols, autonomy and observation boundaries | 15 | 13 |
| C15 | C15. Economic examples, X1 and specialized theorem scopes | 23 | 18 |
| D01 | D01. Executing the released application and validating input | 8 | 6 |
| D02 | D02. Finite dynamics: kernels, survival, occupation, exit and perturbation | 6 | 0 |
| D03 | D03. Finite optimizers: menus, feedback, safety, residence and stationary objectives | 0 | 0 |
| D04 | D04. Linear certificates, one-step risk, and independent infeasibility | 4 | 0 |
| D05 | D05. Information, robust uncertainty, private draws and finite protocols | 5 | 0 |
| D06 | D06. Typed intervention structure, constitutive certificates and special numerical analysis | 0 | 0 |
| D07 | D07. Separate native C10/C11 providers, source pins and proof replay | 10 | 6 |
| E01 | E01. Independent numerical checking and exact receipts | 1 | 0 |
| E02 | E02. Lean source-bound correspondence and replay | 3 | 2 |
| E03 | E03. Evidence, scientific reports, and independent acceptance | 0 | 0 |
| E04 | E04. Case-artifact intake, chronology and provenance | 2 | 1 |
| E05 | E05. Federation, detached integrity, and release boundaries | 6 | 4 |
| E06 | E06. Verification workflows and adversarial test design | 6 | 5 |
| E07 | E07. Historical releases, archives, and provenance | 8 | 0 |
| E08 | E08. Legacy Application Standard versus successor contracts | 4 | 1 |
| F01 | F01. Historical evidence: a read-only casebook | 4 | 3 |
| F02 | F02. Reproducible neutral exercises and answer keys | 27 | 1 |
| F03 | F03. Scientific and engineering boundary matrix | 3 | 0 |
| F04 | F04. Deferred engineering and research roadmap | 6 | 1 |

## Exact chapter source paths

### A01. What Permansson is, and is not

- [`PermanssonLean/Regime/GeneratedRegime.lean`](../../PermanssonLean/Regime/GeneratedRegime.lean)
- [`PermanssonLean/Regime/Permansson.lean`](../../PermanssonLean/Regime/Permansson.lean)
- [`docs/APPLICATION_BOUNDARY.md`](../../docs/APPLICATION_BOUNDARY.md)
- [`docs/GLOSSARY.md`](../../docs/GLOSSARY.md)
- [`paper/README.md`](../../paper/README.md)

### A02. Declare a property before computing

- [`PermanssonLean/Regime/Property.lean`](../../PermanssonLean/Regime/Property.lean)
- [`PermanssonLean/Regime/Specification.lean`](../../PermanssonLean/Regime/Specification.lean)

### A03. Source, release and authority map

- [`PermanssonLean.lean`](../../PermanssonLean.lean)
- [`PermanssonResearch.lean`](../../PermanssonResearch.lean)
- [`apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md`](../../apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md)
- [`docs/RESEARCH_BUILD.md`](../../docs/RESEARCH_BUILD.md)
- [`docs/V020_IMPLEMENTATION_INDEX.md`](../../docs/V020_IMPLEMENTATION_INDEX.md)
- [`lake-manifest.json`](../../lake-manifest.json)
- [`release/v0.2.0/README.md`](../../release/v0.2.0/README.md)

### A04. Installation and the first independently checked calculation

- [`apps/permansson/application-successor/README.md`](../../apps/permansson/application-successor/README.md)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json)
- [`docs/RESEARCH_BUILD.md`](../../docs/RESEARCH_BUILD.md)

### B01. The typed strategic-world model

- [`PermanssonLean/StrategicWorld/InducedKernel.lean`](../../PermanssonLean/StrategicWorld/InducedKernel.lean)
- [`PermanssonLean/StrategicWorld/Model.lean`](../../PermanssonLean/StrategicWorld/Model.lean)

### B02. Induced kernel, initial law, and path law

- [`PermanssonLean/StrategicWorld/InducedKernel.lean`](../../PermanssonLean/StrategicWorld/InducedKernel.lean)
- [`PermanssonLean/StrategicWorld/PathLaw.lean`](../../PermanssonLean/StrategicWorld/PathLaw.lean)
- [`PermanssonResearch/ReverseSolver/CanonicalFiniteKernel.lean`](../../PermanssonResearch/ReverseSolver/CanonicalFiniteKernel.lean)
- [`PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean`](../../PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean)

### B03. Frozen regime specification and descriptor occupation

- [`PermanssonLean/Regime/Specification.lean`](../../PermanssonLean/Regime/Specification.lean)
- [`docs/FORMALIZATION_MAP.md`](../../docs/FORMALIZATION_MAP.md)

### B04. Survival, killing, quasi-regimes and exact invariance

No exact existing path was extracted from this chapter. Use related module families in the JSON manifest.

### B05. Typed strategic interventions and constitutive dependence

- [`PermanssonLean/Regime/Property.lean`](../../PermanssonLean/Regime/Property.lean)

### B06. Perturbation margins and representation discipline

- [`PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean`](../../PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean)
- [`PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean`](../../PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean)
- [`PermanssonResearch/Quotient/Q05ActualOriginalMarginWitnessFixture.lean`](../../PermanssonResearch/Quotient/Q05ActualOriginalMarginWitnessFixture.lean)
- [`docs/FORMALIZATION_MAP.md`](../../docs/FORMALIZATION_MAP.md)
- [`verification/research/tranche10_q04_scope_receipt_addendum.lean`](../../verification/research/tranche10_q04_scope_receipt_addendum.lean)
- [`verification/research/tranche6_q05_whole_path_identification.lean`](../../verification/research/tranche6_q05_whole_path_identification.lean)
- [`verification/research/tranche7_q05_original_margin_addendum.lean`](../../verification/research/tranche7_q05_original_margin_addendum.lean)

### B07. Canonical finite probability laws and exact-rational bridges

- [`PermanssonResearch/Perturbation/PrimitiveProductTV.lean`](../../PermanssonResearch/Perturbation/PrimitiveProductTV.lean)
- [`PermanssonResearch/Probability/DependentHistoryCommonMass.lean`](../../PermanssonResearch/Probability/DependentHistoryCommonMass.lean)
- [`PermanssonResearch/Probability/DependentThreeStageSaturation.lean`](../../PermanssonResearch/Probability/DependentThreeStageSaturation.lean)
- [`PermanssonResearch/ReverseSolver/CanonicalFiniteKernel.lean`](../../PermanssonResearch/ReverseSolver/CanonicalFiniteKernel.lean)
- [`PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean`](../../PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean)
- [`verification/research/tranche10_q03_scope_receipt_addendum.lean`](../../verification/research/tranche10_q03_scope_receipt_addendum.lean)

### B08. Recurrent classes, multiple limits and stationary families

- [`PermanssonResearch/ReverseSolver/C11StationaryFamily.lean`](../../PermanssonResearch/ReverseSolver/C11StationaryFamily.lean)
- [`apps/permansson/closure-successor-c11/README.md`](../../apps/permansson/closure-successor-c11/README.md)

### C01. D0: fixed finite menus of admissible interventions

- [`PermanssonResearch/ReverseSolver/EndToEndCertificate.lean`](../../PermanssonResearch/ReverseSolver/EndToEndCertificate.lean)
- [`PermanssonResearch/ReverseSolver/FiniteEvaluation.lean`](../../PermanssonResearch/ReverseSolver/FiniteEvaluation.lean)
- [`PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean`](../../PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean)
- [`PermanssonResearch/ReverseSolver/FrozenMenu.lean`](../../PermanssonResearch/ReverseSolver/FrozenMenu.lean)
- [`PermanssonResearch/ReverseSolver/RationalKernel.lean`](../../PermanssonResearch/ReverseSolver/RationalKernel.lean)
- [`docs/D0_FROZEN_MENU.md`](../../docs/D0_FROZEN_MENU.md)
- [`verification/research/d0_finite_solver.py`](../../verification/research/d0_finite_solver.py)

### C02. D1: state-dependent finite-horizon Bellman control

- [`PermanssonResearch/ReverseSolver/Bellman.lean`](../../PermanssonResearch/ReverseSolver/Bellman.lean)
- [`PermanssonResearch/ReverseSolver/BellmanOptimality.lean`](../../PermanssonResearch/ReverseSolver/BellmanOptimality.lean)
- [`PermanssonResearch/ReverseSolver/ControlledKernel.lean`](../../PermanssonResearch/ReverseSolver/ControlledKernel.lean)
- [`PermanssonResearch/ReverseSolver/NonstationaryForward.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryForward.lean)
- [`PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean)
- [`PermanssonResearch/ReverseSolver/NonstationaryPrefixKernel.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryPrefixKernel.lean)
- [`docs/D1_BELLMAN.md`](../../docs/D1_BELLMAN.md)
- [`docs/D1_CONTROLLED_KERNEL.md`](../../docs/D1_CONTROLLED_KERNEL.md)

### C03. D1: histories, nonstationarity, and typed path-law transport

- [`PermanssonResearch/ReverseSolver/HistoryContinuation.lean`](../../PermanssonResearch/ReverseSolver/HistoryContinuation.lean)
- [`PermanssonResearch/ReverseSolver/HistoryForwardMeasure.lean`](../../PermanssonResearch/ReverseSolver/HistoryForwardMeasure.lean)
- [`PermanssonResearch/ReverseSolver/HistoryPathAtoms.lean`](../../PermanssonResearch/ReverseSolver/HistoryPathAtoms.lean)
- [`PermanssonResearch/ReverseSolver/HistoryPolicy.lean`](../../PermanssonResearch/ReverseSolver/HistoryPolicy.lean)
- [`PermanssonResearch/ReverseSolver/HistoryPrefixKernel.lean`](../../PermanssonResearch/ReverseSolver/HistoryPrefixKernel.lean)
- [`PermanssonResearch/ReverseSolver/HistoryTypedAtoms.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedAtoms.lean)
- [`PermanssonResearch/ReverseSolver/HistoryTypedFeedback.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedFeedback.lean)
- [`PermanssonResearch/ReverseSolver/HistoryTypedHitting.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedHitting.lean)
- [`PermanssonResearch/ReverseSolver/HistoryTypedKernel.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedKernel.lean)
- [`PermanssonResearch/ReverseSolver/HistoryTypedPrefix.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedPrefix.lean)
- [`PermanssonResearch/ReverseSolver/HistoryTypedTransport.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedTransport.lean)
- [`docs/D1_HISTORY_DEPENDENT.md`](../../docs/D1_HISTORY_DEPENDENT.md)
- [`docs/D1_TYPED_HISTORY_DEPENDENT.md`](../../docs/D1_TYPED_HISTORY_DEPENDENT.md)

### C04. D2: reaching, residing, avoiding, and switching

- [`PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean`](../../PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean)
- [`PermanssonResearch/ReverseSolver/FirstEntryMonitor.lean`](../../PermanssonResearch/ReverseSolver/FirstEntryMonitor.lean)
- [`PermanssonResearch/ReverseSolver/ResidenceContracts.lean`](../../PermanssonResearch/ReverseSolver/ResidenceContracts.lean)
- [`PermanssonResearch/ReverseSolver/ResidenceEvent.lean`](../../PermanssonResearch/ReverseSolver/ResidenceEvent.lean)
- [`PermanssonResearch/ReverseSolver/ResidenceValue.lean`](../../PermanssonResearch/ReverseSolver/ResidenceValue.lean)
- [`apps/permansson/application-successor/docs/NUMERIC_RESIDENCE_NONLINEAR.md`](../../apps/permansson/application-successor/docs/NUMERIC_RESIDENCE_NONLINEAR.md)
- [`docs/D2_RESIDENCE_OBJECTIVE.md`](../../docs/D2_RESIDENCE_OBJECTIVE.md)

### C05. Risk constraints, occupancy flows, exact LP and infeasibility

- [`PermanssonResearch/ReverseSolver/FiniteOccupancyModel.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyModel.lean)
- [`PermanssonResearch/ReverseSolver/FiniteOccupancyReconstruction.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyReconstruction.lean)
- [`PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean`](../../PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean)
- [`PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean`](../../PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean)
- [`PermanssonResearch/ReverseSolver/PolytopeOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PolytopeOptimizer.lean)
- [`apps/permansson/application-successor/docs/NUMERIC_RISK_OCCUPANCY.md`](../../apps/permansson/application-successor/docs/NUMERIC_RISK_OCCUPANCY.md)

### C06. Beliefs, partial observation, information chronology and private draws

- [`PermanssonResearch/ReverseSolver/BeliefChronology.lean`](../../PermanssonResearch/ReverseSolver/BeliefChronology.lean)
- [`PermanssonResearch/ReverseSolver/BeliefFilter.lean`](../../PermanssonResearch/ReverseSolver/BeliefFilter.lean)
- [`PermanssonResearch/ReverseSolver/BeliefHistory.lean`](../../PermanssonResearch/ReverseSolver/BeliefHistory.lean)
- [`PermanssonResearch/ReverseSolver/PrivateControlStageModel.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageModel.lean)
- [`PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean)
- [`apps/permansson/application-successor/docs/NUMERIC_BELIEF_CONTROL.md`](../../apps/permansson/application-successor/docs/NUMERIC_BELIEF_CONTROL.md)
- [`apps/permansson/application-successor/docs/NUMERIC_MULTISTAGE_BELIEF.md`](../../apps/permansson/application-successor/docs/NUMERIC_MULTISTAGE_BELIEF.md)
- [`apps/permansson/application-successor/docs/NUMERIC_PRIVATE_STAGE.md`](../../apps/permansson/application-successor/docs/NUMERIC_PRIVATE_STAGE.md)
- [`verification/research/tranche9_d06_scope_receipt_addendum.lean`](../../verification/research/tranche9_d06_scope_receipt_addendum.lean)

### C07. Robust alternatives, rectangular uncertainty and metric perturbation

- [`PermanssonResearch/ReverseSolver/CommittedVsRectangularPathFixture.lean`](../../PermanssonResearch/ReverseSolver/CommittedVsRectangularPathFixture.lean)
- [`PermanssonResearch/ReverseSolver/RectangularFiniteGame.lean`](../../PermanssonResearch/ReverseSolver/RectangularFiniteGame.lean)
- [`PermanssonResearch/ReverseSolver/RectangularGameLaw.lean`](../../PermanssonResearch/ReverseSolver/RectangularGameLaw.lean)
- [`apps/permansson/application-successor/docs/NUMERIC_METRIC.md`](../../apps/permansson/application-successor/docs/NUMERIC_METRIC.md)
- [`apps/permansson/application-successor/docs/NUMERIC_ROBUST_NATURE.md`](../../apps/permansson/application-successor/docs/NUMERIC_ROBUST_NATURE.md)
- [`verification/research/tranche10_d05_scope_receipt_addendum.lean`](../../verification/research/tranche10_d05_scope_receipt_addendum.lean)

### C08. Intervention grammars, interaction and constitution

- [`PermanssonResearch/ReverseSolver/ConstitutiveCertificateCheck.lean`](../../PermanssonResearch/ReverseSolver/ConstitutiveCertificateCheck.lean)
- [`PermanssonResearch/ReverseSolver/ExecutableConstitutiveSelection.lean`](../../PermanssonResearch/ReverseSolver/ExecutableConstitutiveSelection.lean)
- [`docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md`](../../docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md)
- [`docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md`](../../docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md)
- [`verification/research/tranche10_b02_scope_receipt_addendum.lean`](../../verification/research/tranche10_b02_scope_receipt_addendum.lean)
- [`verification/research/tranche9_d08_scope_receipt_addendum.lean`](../../verification/research/tranche9_d08_scope_receipt_addendum.lean)

### C09. Quotients, abstract states, nonlinear properties and scope-specific witnesses

- [`PermanssonResearch/Quotient/ApproxPrefix.lean`](../../PermanssonResearch/Quotient/ApproxPrefix.lean)
- [`PermanssonResearch/Quotient/DiscountedCanonicalBridge.lean`](../../PermanssonResearch/Quotient/DiscountedCanonicalBridge.lean)
- [`PermanssonResearch/Quotient/GeometricQuotient.lean`](../../PermanssonResearch/Quotient/GeometricQuotient.lean)
- [`PermanssonResearch/Quotient/Q01NonLumpableProjectionCountermodel.lean`](../../PermanssonResearch/Quotient/Q01NonLumpableProjectionCountermodel.lean)
- [`PermanssonResearch/Quotient/Q05ActualOriginalMarginAdapter.lean`](../../PermanssonResearch/Quotient/Q05ActualOriginalMarginAdapter.lean)
- [`PermanssonResearch/ReverseSolver/NonlinearBooleanClassFunctional.lean`](../../PermanssonResearch/ReverseSolver/NonlinearBooleanClassFunctional.lean)
- [`PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean`](../../PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean)
- [`PermanssonResearch/ReverseSolver/NonlinearPolicyClassComparison.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPolicyClassComparison.lean)
- [`apps/permansson/application-successor/docs/NUMERIC_GRAMMAR_QUOTIENT.md`](../../apps/permansson/application-successor/docs/NUMERIC_GRAMMAR_QUOTIENT.md)
- [`apps/permansson/application-successor/docs/NUMERIC_RESIDENCE_NONLINEAR.md`](../../apps/permansson/application-successor/docs/NUMERIC_RESIDENCE_NONLINEAR.md)
- [`docs/LANE_E1_APPROX_QUOTIENT.md`](../../docs/LANE_E1_APPROX_QUOTIENT.md)
- [`verification/research/tranche8_d09_scope_receipt_addendum.lean`](../../verification/research/tranche8_d09_scope_receipt_addendum.lean)

### C10. Exact rational evaluation and proof-carrying receipts

- [`PermanssonResearch/ReverseSolver/C10ReceiptSemantics.lean`](../../PermanssonResearch/ReverseSolver/C10ReceiptSemantics.lean)
- [`PermanssonResearch/ReverseSolver/CheckedRationalInput.lean`](../../PermanssonResearch/ReverseSolver/CheckedRationalInput.lean)
- [`PermanssonResearch/ReverseSolver/EndToEndCertificate.lean`](../../PermanssonResearch/ReverseSolver/EndToEndCertificate.lean)
- [`PermanssonResearch/ReverseSolver/FiniteEvaluation.lean`](../../PermanssonResearch/ReverseSolver/FiniteEvaluation.lean)
- [`PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean`](../../PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean)
- [`PermanssonResearch/ReverseSolver/RationalKernel.lean`](../../PermanssonResearch/ReverseSolver/RationalKernel.lean)
- [`docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`](../../docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md)

### C11. Exact graph reachability, recurrent classes and absorption

- [`PermanssonResearch/ReverseSolver/C11StationaryFamily.lean`](../../PermanssonResearch/ReverseSolver/C11StationaryFamily.lean)
- [`PermanssonResearch/ReverseSolver/RationalAbsorptionSolve.lean`](../../PermanssonResearch/ReverseSolver/RationalAbsorptionSolve.lean)
- [`PermanssonResearch/ReverseSolver/RationalBSCCPartition.lean`](../../PermanssonResearch/ReverseSolver/RationalBSCCPartition.lean)
- [`PermanssonResearch/ReverseSolver/RationalCramerCertification.lean`](../../PermanssonResearch/ReverseSolver/RationalCramerCertification.lean)
- [`PermanssonResearch/ReverseSolver/RationalDirichletUniqueness.lean`](../../PermanssonResearch/ReverseSolver/RationalDirichletUniqueness.lean)
- [`PermanssonResearch/ReverseSolver/RationalSupportGraph.lean`](../../PermanssonResearch/ReverseSolver/RationalSupportGraph.lean)
- [`PermanssonResearch/ReverseSolver/TypedStoppedClassSelection.lean`](../../PermanssonResearch/ReverseSolver/TypedStoppedClassSelection.lean)
- [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](../../docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md)

### C12. Infinite-horizon safety and controlled invariant cores

- [`PermanssonResearch/ReverseSolver/GreatestControlledInvariant.lean`](../../PermanssonResearch/ReverseSolver/GreatestControlledInvariant.lean)
- [`PermanssonResearch/ReverseSolver/InfiniteSafetyBellman.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyBellman.lean)
- [`PermanssonResearch/ReverseSolver/InfiniteSafetyFiniteEvaluation.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyFiniteEvaluation.lean)
- [`PermanssonResearch/ReverseSolver/InfiniteSafetyLeakage.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyLeakage.lean)
- [`PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean)
- [`PermanssonResearch/ReverseSolver/InfiniteSafetyPathSemantics.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyPathSemantics.lean)

### C13. Occupancy polytopes, rational extreme points and certificates

- [`PermanssonResearch/ReverseSolver/FiniteOccupancyHistory.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyHistory.lean)
- [`PermanssonResearch/ReverseSolver/FiniteOccupancyMarginals.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyMarginals.lean)
- [`PermanssonResearch/ReverseSolver/FiniteOccupancyModel.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyModel.lean)
- [`PermanssonResearch/ReverseSolver/FiniteOccupancyReconstruction.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyReconstruction.lean)
- [`PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean`](../../PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean)
- [`PermanssonResearch/ReverseSolver/FlowPolytope.lean`](../../PermanssonResearch/ReverseSolver/FlowPolytope.lean)
- [`PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean`](../../PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean)
- [`PermanssonResearch/ReverseSolver/PolytopeOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PolytopeOptimizer.lean)
- [`apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/docs/NUMERIC_RISK_OCCUPANCY.md`](../../apps/permansson/application-successor/docs/NUMERIC_RISK_OCCUPANCY.md)

### C14. Multiagent protocols, autonomy and observation boundaries

- [`PermanssonResearch/MultiAgent/AdaptationBound.lean`](../../PermanssonResearch/MultiAgent/AdaptationBound.lean)
- [`PermanssonResearch/MultiAgent/AutonomousMarginalLaw.lean`](../../PermanssonResearch/MultiAgent/AutonomousMarginalLaw.lean)
- [`PermanssonResearch/MultiAgent/AutonomousMarkedKernel.lean`](../../PermanssonResearch/MultiAgent/AutonomousMarkedKernel.lean)
- [`PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean`](../../PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean)
- [`PermanssonResearch/MultiAgent/FiniteProductProtocols.lean`](../../PermanssonResearch/MultiAgent/FiniteProductProtocols.lean)
- [`PermanssonResearch/MultiAgent/M02ActualMarkedHistoryFixture.lean`](../../PermanssonResearch/MultiAgent/M02ActualMarkedHistoryFixture.lean)
- [`PermanssonResearch/MultiAgent/MarkedStrategicPathCountermodel.lean`](../../PermanssonResearch/MultiAgent/MarkedStrategicPathCountermodel.lean)
- [`PermanssonResearch/MultiAgent/NatPrivateClock.lean`](../../PermanssonResearch/MultiAgent/NatPrivateClock.lean)
- [`PermanssonResearch/MultiAgent/PrivateClock.lean`](../../PermanssonResearch/MultiAgent/PrivateClock.lean)
- [`PermanssonResearch/MultiAgent/ProductGame.lean`](../../PermanssonResearch/MultiAgent/ProductGame.lean)
- [`PermanssonResearch/MultiAgent/Protocols.lean`](../../PermanssonResearch/MultiAgent/Protocols.lean)
- [`PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean`](../../PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean)
- [`apps/permansson/application-successor/docs/NUMERIC_MULTIAGENT.md`](../../apps/permansson/application-successor/docs/NUMERIC_MULTIAGENT.md)
- [`docs/LANE_F1_MULTIAGENT_PROTOCOLS.md`](../../docs/LANE_F1_MULTIAGENT_PROTOCOLS.md)
- [`verification/research/tranche8_f01_scope_receipt_addendum.lean`](../../verification/research/tranche8_f01_scope_receipt_addendum.lean)

### C15. Economic examples, X1 and specialized theorem scopes

- [`PermanssonResearch/EconomicWitness/ExactRegime.lean`](../../PermanssonResearch/EconomicWitness/ExactRegime.lean)
- [`PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean`](../../PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean)
- [`PermanssonResearch/ReverseSolver/BellmanOptimality.lean`](../../PermanssonResearch/ReverseSolver/BellmanOptimality.lean)
- [`PermanssonResearch/ReverseSolver/EndToEndCertificate.lean`](../../PermanssonResearch/ReverseSolver/EndToEndCertificate.lean)
- [`PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean`](../../PermanssonResearch/ReverseSolver/FinitePrefixBridge.lean)
- [`PermanssonResearch/ReverseSolver/GreatestControlledInvariant.lean`](../../PermanssonResearch/ReverseSolver/GreatestControlledInvariant.lean)
- [`PermanssonResearch/ReverseSolver/HistoryTypedTransport.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedTransport.lean)
- [`PermanssonResearch/ReverseSolver/NonlinearPolicyClassComparison.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPolicyClassComparison.lean)
- [`PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean`](../../PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean)
- [`PermanssonResearch/ReverseSolver/PolytopeOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PolytopeOptimizer.lean)
- [`PermanssonResearch/ReverseSolver/PrivateControlStageModel.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageModel.lean)
- [`PermanssonResearch/ReverseSolver/RationalKernel.lean`](../../PermanssonResearch/ReverseSolver/RationalKernel.lean)
- [`PermanssonResearch/ReverseSolver/RectangularGameLaw.lean`](../../PermanssonResearch/ReverseSolver/RectangularGameLaw.lean)
- [`PermanssonResearch/ReverseSolver/ResidenceValue.lean`](../../PermanssonResearch/ReverseSolver/ResidenceValue.lean)
- [`PermanssonResearch/ReverseSolver/TypedStoppedClassSelection.lean`](../../PermanssonResearch/ReverseSolver/TypedStoppedClassSelection.lean)
- [`PermanssonResearch/X1/ExactMargins.lean`](../../PermanssonResearch/X1/ExactMargins.lean)
- [`PermanssonResearch/X1/FullStrategyCertificate.lean`](../../PermanssonResearch/X1/FullStrategyCertificate.lean)
- [`PermanssonResearch/X1/InterventionNumerics.lean`](../../PermanssonResearch/X1/InterventionNumerics.lean)
- [`apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md`](../../apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md)
- [`apps/permansson/application-successor/docs/REVIEWER_GUIDE.md`](../../apps/permansson/application-successor/docs/REVIEWER_GUIDE.md)
- [`apps/permansson/application-successor/src/permansson_app/data/capabilities.json`](../../apps/permansson/application-successor/src/permansson_app/data/capabilities.json)
- [`docs/FORMALIZATION_MAP.md`](../../docs/FORMALIZATION_MAP.md)
- [`docs/V020_IMPLEMENTATION_INDEX.md`](../../docs/V020_IMPLEMENTATION_INDEX.md)

### D01. Executing the released application and validating input

- [`apps/permansson/application-successor/docs/EXAMPLES_AND_LIMITS.md`](../../apps/permansson/application-successor/docs/EXAMPLES_AND_LIMITS.md)
- [`apps/permansson/application-successor/src/permansson_app/__main__.py`](../../apps/permansson/application-successor/src/permansson_app/__main__.py)
- [`apps/permansson/application-successor/src/permansson_app/budget.py`](../../apps/permansson/application-successor/src/permansson_app/budget.py)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json)
- [`apps/permansson/application-successor/src/permansson_app/report.py`](../../apps/permansson/application-successor/src/permansson_app/report.py)
- [`apps/permansson/application-successor/src/permansson_app/schema_validate.py`](../../apps/permansson/application-successor/src/permansson_app/schema_validate.py)
- [`apps/permansson/application-successor/src/permansson_app/semantics.py`](../../apps/permansson/application-successor/src/permansson_app/semantics.py)
- [`apps/permansson/application-successor/src/permansson_app/strict_json.py`](../../apps/permansson/application-successor/src/permansson_app/strict_json.py)

### D02. Finite dynamics: kernels, survival, occupation, exit and perturbation

- [`apps/permansson/application-successor/docs/EXIT_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/EXIT_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/docs/MENU_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/MENU_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/docs/OCCUPATION_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/OCCUPATION_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/docs/PERTURBATION_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/PERTURBATION_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_region.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_region.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json)

### D03. Finite optimizers: menus, feedback, safety, residence and stationary objectives

No exact existing path was extracted from this chapter. Use related module families in the JSON manifest.

### D04. Linear certificates, one-step risk, and independent infeasibility

- [`apps/permansson/application-successor/docs/FLOW_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/FLOW_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/docs/RISK_INFEASIBILITY_LEAN_BRIDGE.md`](../../apps/permansson/application-successor/docs/RISK_INFEASIBILITY_LEAN_BRIDGE.md)
- [`apps/permansson/application-successor/src/permansson_app/data/schemas/lp.v1.schema.json`](../../apps/permansson/application-successor/src/permansson_app/data/schemas/lp.v1.schema.json)

### D05. Information, robust uncertainty, private draws and finite protocols

- [`apps/permansson/application-successor/docs/NUMERIC_BELIEF_CONTROL.md`](../../apps/permansson/application-successor/docs/NUMERIC_BELIEF_CONTROL.md)
- [`apps/permansson/application-successor/docs/NUMERIC_MULTIAGENT.md`](../../apps/permansson/application-successor/docs/NUMERIC_MULTIAGENT.md)
- [`apps/permansson/application-successor/docs/NUMERIC_MULTISTAGE_BELIEF.md`](../../apps/permansson/application-successor/docs/NUMERIC_MULTISTAGE_BELIEF.md)
- [`apps/permansson/application-successor/docs/NUMERIC_PRIVATE_STAGE.md`](../../apps/permansson/application-successor/docs/NUMERIC_PRIVATE_STAGE.md)
- [`apps/permansson/application-successor/docs/NUMERIC_ROBUST_NATURE.md`](../../apps/permansson/application-successor/docs/NUMERIC_ROBUST_NATURE.md)

### D06. Typed intervention structure, constitutive certificates and special numerical analysis

No exact existing path was extracted from this chapter. Use related module families in the JSON manifest.

### D07. Separate native C10/C11 providers, source pins and proof replay

- [`apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md`](../../apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md)
- [`apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md`](../../apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md)
- [`apps/permansson/application-successor/docs/REVIEWER_GUIDE.md`](../../apps/permansson/application-successor/docs/REVIEWER_GUIDE.md)
- [`apps/permansson/application-successor/scripts/end_to_end.py`](../../apps/permansson/application-successor/scripts/end_to_end.py)
- [`apps/permansson/application-successor/src/permansson_app/capabilities.py`](../../apps/permansson/application-successor/src/permansson_app/capabilities.py)
- [`apps/permansson/application-successor/src/permansson_app/replay.py`](../../apps/permansson/application-successor/src/permansson_app/replay.py)
- [`apps/permansson/application-successor/src/permansson_app/report.py`](../../apps/permansson/application-successor/src/permansson_app/report.py)
- [`apps/permansson/application-successor/src/permansson_app/runner.py`](../../apps/permansson/application-successor/src/permansson_app/runner.py)
- [`apps/permansson/application-successor/src/permansson_app/source.py`](../../apps/permansson/application-successor/src/permansson_app/source.py)
- [`apps/permansson/closure-successor/README.md`](../../apps/permansson/closure-successor/README.md)

### E01. Independent numerical checking and exact receipts

- [`apps/permansson/application-successor/docs/REVIEWER_GUIDE.md`](../../apps/permansson/application-successor/docs/REVIEWER_GUIDE.md)

### E02. Lean source-bound correspondence and replay

- [`PermanssonResearch.lean`](../../PermanssonResearch.lean)
- [`apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md`](../../apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md)
- [`verification/lean/PermanssonLean_root_imports_snapshot.lean`](../../verification/lean/PermanssonLean_root_imports_snapshot.lean)

### E03. Evidence, scientific reports, and independent acceptance

No exact existing path was extracted from this chapter. Use related module families in the JSON manifest.

### E04. Case-artifact intake, chronology and provenance

- [`apps/permansson/application-successor/docs/DOMAIN_IMPORTS.md`](../../apps/permansson/application-successor/docs/DOMAIN_IMPORTS.md)
- [`apps/permansson/application-successor/src/permansson_app/domain/registry.py`](../../apps/permansson/application-successor/src/permansson_app/domain/registry.py)

### E05. Federation, detached integrity, and release boundaries

- [`apps/permansson/application-successor/docs/FEDERATION_CONTRACT.md`](../../apps/permansson/application-successor/docs/FEDERATION_CONTRACT.md)
- [`apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md`](../../apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md)
- [`apps/permansson/application-successor/src/permansson_app/federation/compatibility.py`](../../apps/permansson/application-successor/src/permansson_app/federation/compatibility.py)
- [`apps/permansson/application-successor/src/permansson_app/federation/exchange.py`](../../apps/permansson/application-successor/src/permansson_app/federation/exchange.py)
- [`apps/permansson/application-successor/src/permansson_app/federation/local_engine.py`](../../apps/permansson/application-successor/src/permansson_app/federation/local_engine.py)
- [`verification/application_successor/release_gate.py`](../../verification/application_successor/release_gate.py)

### E06. Verification workflows and adversarial test design

- [`apps/permansson/application-successor/scripts/end_to_end.py`](../../apps/permansson/application-successor/scripts/end_to_end.py)
- [`apps/permansson/application-successor/scripts/inventory.py`](../../apps/permansson/application-successor/scripts/inventory.py)
- [`verification/README.md`](../../verification/README.md)
- [`verification/application_gate.py`](../../verification/application_gate.py)
- [`verification/destructive/suite/run_all.py`](../../verification/destructive/suite/run_all.py)
- [`verification/repository_gate.py`](../../verification/repository_gate.py)

### E07. Historical releases, archives, and provenance

- [`archival/v0.2.0/README.md`](../../archival/v0.2.0/README.md)
- [`archival/v0.2.0/supplement-1/OFFLINE_REPRODUCTION.md`](../../archival/v0.2.0/supplement-1/OFFLINE_REPRODUCTION.md)
- [`archival/v0.2.0/supplement-1/refs.json`](../../archival/v0.2.0/supplement-1/refs.json)
- [`provenance/README.md`](../../provenance/README.md)
- [`release/mathematical-closure-1/README.md`](../../release/mathematical-closure-1/README.md)
- [`release/v0.2.0/README.md`](../../release/v0.2.0/README.md)
- [`release/v0.2.0/manuscript.json`](../../release/v0.2.0/manuscript.json)
- [`release/v0.2.0/output/pdf/theorem-map.json`](../../release/v0.2.0/output/pdf/theorem-map.json)

### E08. Legacy Application Standard versus successor contracts

- [`application/APPLICATION_STANDARD.md`](../../application/APPLICATION_STANDARD.md)
- [`application/examples/grounded_pr_minimal/application.json`](../../application/examples/grounded_pr_minimal/application.json)
- [`application/requirements.txt`](../../application/requirements.txt)
- [`application/validator/validate_application.py`](../../application/validator/validate_application.py)

### F01. Historical evidence: a read-only casebook

- [`apps/permansson/application-successor/docs/DOMAIN_IMPORTS.md`](../../apps/permansson/application-successor/docs/DOMAIN_IMPORTS.md)
- [`apps/permansson/application-successor/src/permansson_app/domain/clock.py`](../../apps/permansson/application-successor/src/permansson_app/domain/clock.py)
- [`apps/permansson/application-successor/src/permansson_app/domain/importer.py`](../../apps/permansson/application-successor/src/permansson_app/domain/importer.py)
- [`apps/permansson/application-successor/src/permansson_app/domain/registry.py`](../../apps/permansson/application-successor/src/permansson_app/domain/registry.py)

### F02. Reproducible neutral exercises and answer keys

- [`apps/permansson/application-successor/docs/EXAMPLES_AND_LIMITS.md`](../../apps/permansson/application-successor/docs/EXAMPLES_AND_LIMITS.md)
- [`apps/permansson/application-successor/docs/REVIEWER_GUIDE.md`](../../apps/permansson/application-successor/docs/REVIEWER_GUIDE.md)
- [`apps/permansson/application-successor/scripts/end_to_end.py`](../../apps/permansson/application-successor/scripts/end_to_end.py)
- [`apps/permansson/application-successor/src/permansson_app/data/capabilities.json`](../../apps/permansson/application-successor/src/permansson_app/data/capabilities.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/adaptive.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/adaptive.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/algebra.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/algebra.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/belief.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/belief.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/belief_tree.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/belief_tree.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/control_hitting.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/control_hitting.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/cq1.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/cq1.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/cq1_transport.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/cq1_transport.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_menu.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_menu.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_perturbation.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_perturbation.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_safety.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_safety.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_survival.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_survival.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/finite_world.v1.model.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/grammar.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/grammar.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/lp.v1.model.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/lp.v1.model.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/metric.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/metric.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/multiagent.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/multiagent.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/nonlinear.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/nonlinear.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/private_stage.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/private_stage.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/quotient.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/quotient.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/residence.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/residence.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/risk_infeasibility.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/risk_infeasibility.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/risk_occupancy.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/risk_occupancy.v1.json)
- [`apps/permansson/application-successor/src/permansson_app/data/examples/robust_nature.v1.json`](../../apps/permansson/application-successor/src/permansson_app/data/examples/robust_nature.v1.json)

### F03. Scientific and engineering boundary matrix

- [`apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md`](../../apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md)
- [`docs/APPLICATION_BOUNDARY.md`](../../docs/APPLICATION_BOUNDARY.md)
- [`docs/FORMALIZATION_MAP.md`](../../docs/FORMALIZATION_MAP.md)

### F04. Deferred engineering and research roadmap

- [`apps/permansson/application-successor/IMPLEMENTATION_MANIFEST.json`](../../apps/permansson/application-successor/IMPLEMENTATION_MANIFEST.json)
- [`apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md`](../../apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md)
- [`apps/permansson/application-successor/docs/ROADMAP.md`](../../apps/permansson/application-successor/docs/ROADMAP.md)
- [`docs/FUTURE_THEORY_ROADMAP.md`](../../docs/FUTURE_THEORY_ROADMAP.md)
- [`research/certification/target_intent.json`](../../research/certification/target_intent.json)
- [`verification/research/final_closure_case_method_routes.py`](../../verification/research/final_closure_case_method_routes.py)

## Appendix source-path coverage

| Appendix | Exact existing source paths |
|---|---:|
| Appendix D-A | 11 |
| Appendix D-B | 27 |
| Appendix D-C | 7 |
| Appendix E-A | 3 |
| Appendix E-B | 0 |
| Appendix E-C | 0 |
| Appendix F-A | 0 |
| Appendix F-B | 0 |
| Appendix F-C | 0 |
| Appendix F-D | 1 |
| Appendix G | 1 |
| Appendix H | 25 |
| Appendix I | 0 |
| Appendix J | 166 |
| Appendix K | 0 |

All 166 Appendix J S-numbers and 56 case-specific source-route joins are recorded in the manifest. The same file stores every tracked module's Git blob SHA, verified root-import relationship, and navigational chapter-family suggestions.
