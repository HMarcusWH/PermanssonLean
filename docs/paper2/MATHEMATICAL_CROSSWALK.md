# Paper v2.0.1: mathematical crosswalk

[Current documentation](README.md) · [Publication hub](../../paper2/README.md) · [Earlier-paper concordance](EARLIER_PAPER_CONCORDANCE.md) · [Residual status](RESIDUAL_STATUS.md)

This is the current reading map for **Permansson Regimes: Structure, Intervention, and Computation Beyond Equilibrium**, reviewed manuscript draft **v2.0.1**. It accounts for all **31 main sections, 16 appendices and 147 numbered mathematical items**. It preserves the manuscript's **538 printed source-anchor occurrences** and links the complete **798-file Lean written-connections index**.

The mathematical source is commit `c5a36cd6189e2a249d5f4bc11f31698917dc8b10`. The documentation baseline after PR #127 is `f0dee1c11a20f96c9a11b380e942b9252e6ebe44`. The actual uploaded artifact identity is maintained in the [publication manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json). These commits have different roles; see [version lineage](VERSION_LINEAGE.md).

## How to read this map

The paper label identifies an item in the reviewed PDF/source. The links below lead to the corresponding section of this map; the exact label is retained so it can be searched in the source or label index. A manuscript source path such as `sections/C14.tex` is a member of the [source/concordance ZIP](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip), not a separate tracked repository path.

The section tables list literal citations from the reviewed manuscript. They identify the cited file and declaration or producer label, without asserting that every cited interface is identical to the full prose theorem. The **scope boundary** and **proof role** state how the material is used. A paper proof, a formal specialization, a numerical example, and a source-presence check remain different evidence objects.

| Record | What it provides |
|---|---|
| [Numbered statement index](../../paper2/v2.0.1/indices/statement_index.json) | 147 numbered definitions, lemmas, propositions, theorems, corollaries, examples and other indexed mathematical items. |
| [Manuscript label index](../../paper2/v2.0.1/indices/manuscript_label_index.json) | 603 exact labels and manuscript source locations. |
| [Source citation index](../../paper2/v2.0.1/indices/source_citation_index.json) | 538 printed citation occurrences, including repeated uses of a source endpoint. |
| [Lean written-connections index](../../paper2/v2.0.1/indices/all_lean_written_connections.json) | 798 unique Lean paths, source hashes, reviewed proof-group routes and explicit non-certification fields. |
| [Review findings](../../paper2/v2.0.1/indices/review_findings.json) | 58 applied corrections/clarifications in the internal draft 2.0-to-2.0.1 manuscript revision. |

## Section and appendix index

| Destination | Title | Literal source-anchor occurrences |
|---|---|---|
| [C01](#c01) | Lineage, question and contribution boundaries | 0 |
| [C02](#c02) | Probability, measurable structure, and convergence | 5 |
| [C03](#c03) | Chronological strategic-world dynamics and canonical laws | 4 |
| [C04](#c04) | Generated regimes, persistence, and quasi-stationarity | 9 |
| [C05](#c05) | Constitution, grounding, and representation | 9 |
| [C06](#c06) | The equilibrium predecessor: models, mechanisms and exact recovery | 5 |
| [C07](#c07) | Finite recurrence and the complete law of random occupations | 4 |
| [C08](#c08) | Exact finite GR and property-specific PR characterizations | 11 |
| [C09](#c09) | Nonfinite occupation: stationary, compact Feller and regenerative routes | 12 |
| [C10](#c10) | Exit destinations, full-future restart and intervention-driven switching | 23 |
| [C11](#c11) | Admitted grammars, interaction and minimality | 14 |
| [C12](#c12) | Finite constitutive certificates and primitive error budgets | 13 |
| [C13](#c13) | Finite, localized and whole-path probability bounds | 8 |
| [C14](#c14) | Transport metrics, contraction and invariant-law construction | 12 |
| [C15](#c15) | Frozen occupation properties and original-margin robustness | 17 |
| [C16](#c16) | Exact and approximate intervention-compatible quotients | 10 |
| [C17](#c17) | Finite histories, monitors, and adaptive feedback | 13 |
| [C18](#c18) | Belief control and nonstationary dynamics | 15 |
| [C19](#c19) | Occupation flows, risk constraints, and infinite safety | 13 |
| [C20](#c20) | Total rational construction and recovery of the original semantics | 9 |
| [C21](#c21) | Nonlinear occupation objectives and stationary policy optimization | 12 |
| [C22](#c22) | Robust control, rectangular Nature, and private randomization | 10 |
| [C23](#c23) | Discounted full-history verification and the X1 model | 20 |
| [C24](#c24) | Measurable multi-agent mechanisms, autonomy, clocks, and mediators | 22 |
| [C25](#c25) | Finite structural causal models and mediation identification | 9 |
| [C26](#c26) | Specialized finite algebra, detection and source rigidity | 12 |
| [C27](#c27) | Constructed examples and counterexamples | 9 |
| [C28](#c28) | Measurement, earlier applications, and confirmatory inference | 0 |
| [C29](#c29) | Exact algorithms, reflection, and executable evidence | 6 |
| [C30](#c30) | Formalization, reproducibility, and source concordance | 0 |
| [C31](#c31) | Limitations, corrected claims, and further mathematical questions | 0 |
| [A](#appendix-a) | Measurable and probabilistic conventions | 9 |
| [B](#appendix-b) | Earlier-paper lineage and mathematical reconciliation | 0 |
| [C](#appendix-c) | Canonical dynamics, original predicates and EGR derivations | 17 |
| [D](#appendix-d) | Finite occupation proofs and exact absorbing and recurrent witnesses | 31 |
| [E](#appendix-e) | Ergodic, regenerative and nonfinite proof details | 29 |
| [F](#appendix-f) | Grammar proofs and finite-certificate details | 28 |
| [G](#appendix-g) | Path transport and discounted-score proofs | 5 |
| [H](#appendix-h) | Transport, completeness and occupation proofs | 14 |
| [I](#appendix-i) | Exact and geometric quotient derivations | 2 |
| [J](#appendix-j) | History laws, monitor invariants, belief reduction, and safety | 20 |
| [K](#appendix-k) | Exact rational algorithms and their semantic proofs | 36 |
| [L](#appendix-l) | Game laws, X1 arithmetic, multi-agent transport, and causal identification | 31 |
| [M](#appendix-m) | Specialized dictionary, shell and source proofs | 10 |
| [N](#appendix-n) | Application derivations, exact examples, and the confirmatory workflow | 0 |
| [O](#appendix-o) | Mathematical index and source-concordance conventions | 0 |
| [P](#appendix-p) | Precise residual obligations and extension criteria | 0 |

## C01

**Lineage, question and contribution boundaries**\
Paper label: `sec:C01` · Source ZIP member: `sections/C01.tex`.

**Proof role.** Lineage and contribution framing; historical claims retain their original evidence status.

**Scope boundary.** Earlier-paper lineage is preserved; manuscript v2.0.1, formal release v0.2.0 and mathematical guide v1.1.1 are different artifacts.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/PERMANSSON_RESEARCH_ARCHITECTURE.md`](../PERMANSSON_RESEARCH_ARCHITECTURE.md); [`docs/FUTURE_THEORY_ROADMAP.md`](../FUTURE_THEORY_ROADMAP.md). These documents retain their original source/date scope.

**Manuscript review references.** `ROOT-16` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## C02

**Probability, measurable structure, and convergence**\
Paper label: `sec:C02` · Source ZIP member: `sections/C02.tex`.

**Proof role.** Probability definitions and manuscript lemmas, with cited formal operations and convergence endpoints.

**Scope boundary.** State the actual measurable/Borel/nonempty and metric profiles; empirical weak limits, W1 limits, deterministic limits and laws of random limits remain distinct.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/CQ1_FINITE_PATH_BRIDGE.md`](../CQ1_FINITE_PATH_BRIDGE.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/Regime/Occupation.lean`](../../PermanssonLean/Regime/Occupation.lean) | `empiricalOccupation` |
| [`PermanssonResearch/RegimeExit/OccupationPrefixDeletion.lean`](../../PermanssonResearch/RegimeExit/OccupationPrefixDeletion.lean) | `tendsto_empiricalOccupation_of_tailShift` |
| [`PermanssonLean/Regime/ConvergenceMode.lean`](../../PermanssonLean/Regime/ConvergenceMode.lean) | `almostSureWeak` |
| [`PermanssonLean/Probability/TotalVariation.lean`](../../PermanssonLean/Probability/TotalVariation.lean) | `eventTotalVariation` |
| [`PermanssonLean/Probability/CommonPartKernel.lean`](../../PermanssonLean/Probability/CommonPartKernel.lean) | `commonPartKernel` |

## C03

**Chronological strategic-world dynamics and canonical laws**\
Paper label: `sec:C03` · Source ZIP member: `sections/C03.tex`.

**Proof role.** Original typed generator construction and canonical-law results.

**Scope boundary.** Chronology is alpha then physical P then update U; original canonical laws and fixed physical-world intervention semantics are retained.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/StrategicWorld/InducedKernel.lean`](../../PermanssonLean/StrategicWorld/InducedKernel.lean) | `inducedKernel_isMarkov` |
| [`PermanssonLean/StrategicWorld/InducedKernel.lean`](../../PermanssonLean/StrategicWorld/InducedKernel.lean) | `inducedKernel_apply_indicator` |
| [`PermanssonLean/StrategicWorld/WellPosedness.lean`](../../PermanssonLean/StrategicWorld/WellPosedness.lean) | `pathLaw_existsUnique` |
| [`PermanssonResearch/RegimeExit/RandomEntryOccupation.lean`](../../PermanssonResearch/RegimeExit/RandomEntryOccupation.lean) | `pathLaw_eq_bind` |

## C04

**Generated regimes, persistence, and quasi-stationarity**\
Paper label: `sec:C04` · Source ZIP member: `sections/C04.tex`.

**Proof role.** Original regime predicates, killed-kernel results and separately scoped quasi-stationary conclusions.

**Scope boundary.** Original Exact GR requires all-state invariance and original nontriviality; finite retention and QSD statements have separate hypotheses.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/LANE_C_ABSORBING_REGIME_FAMILIES.md`](../LANE_C_ABSORBING_REGIME_FAMILIES.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-010` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/Regime/Assumption41.lean`](../../PermanssonLean/Regime/Assumption41.lean) | `Assumption41` |
| [`PermanssonLean/Regime/Assumption41.lean`](../../PermanssonLean/Regime/Assumption41.lean) | `basinHasTwoStates_iff_pathLawNontrivial` |
| [`PermanssonLean/Regime/GeneratedRegime.lean`](../../PermanssonLean/Regime/GeneratedRegime.lean) | `IsExactGeneratedRegime` |
| [`PermanssonLean/Regime/KilledKernel.lean`](../../PermanssonLean/Regime/KilledKernel.lean) | `killedKernel` |
| [`PermanssonLean/Regime/ExitTimeExpectation.lean`](../../PermanssonLean/Regime/ExitTimeExpectation.lean) | `expectedExitTime_eq_greenSeries` |
| [`PermanssonLean/Regime/SurvivalBridge.lean`](../../PermanssonLean/Regime/SurvivalBridge.lean) | `survivingEndpointMeasure_eq_killedPow` |
| [`PermanssonLean/Regime/QuasiStationary.lean`](../../PermanssonLean/Regime/QuasiStationary.lean) | `qsd_killedMeasureIterate_eq_smul` |
| [`PermanssonLean/Regime/QuasiStationary.lean`](../../PermanssonLean/Regime/QuasiStationary.lean) | `qsd_survivalProbability` |
| [`PermanssonLean/Examples/QSDCounterexample.lean`](../../PermanssonLean/Examples/QSDCounterexample.lean) | `qsd_does_not_imply_uniform_finitePersistence` |

## C05

**Constitution, grounding, and representation**\
Paper label: `sec:C05` · Source ZIP member: `sections/C05.tex`.

**Proof role.** Original constitutive and grounded predicates; paper representation argument alongside narrower formal interfaces.

**Scope boundary.** Keep measurable grounding maps, original comparison-set requirements, and the paper coordinate-change proof distinct from same-space formal endpoints.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md`](../LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-001`, `FND-005` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/Regime/Constitution.lean`](../../PermanssonLean/Regime/Constitution.lean) | `IsStrategicallyConstitutive` |
| [`PermanssonLean/Regime/UniformPermansson.lean`](../../PermanssonLean/Regime/UniformPermansson.lean) | `IsUniformGeneralizedPermanssonRegimeRelative` |
| [`PermanssonLean/Regime/GroundedProperty.lean`](../../PermanssonLean/Regime/GroundedProperty.lean) | `IsGroundedPropertyRelative` |
| [`PermanssonLean/Regime/NuisancePadding.lean`](../../PermanssonLean/Regime/NuisancePadding.lean) | `nuisancePadding_cannot_create_grounded_change` |
| [`PermanssonLean/Regime/RepresentationEquivalence.lean`](../../PermanssonLean/Regime/RepresentationEquivalence.lean) | `exactGR_iff_of_inducedKernel_eq` |
| [`PermanssonLean/Regime/FamilyEquivalence.lean`](../../PermanssonLean/Regime/FamilyEquivalence.lean) | `frozenFamilyPR_iff_of_signature_match` |
| [`PermanssonLean/Regime/GroundedFamilyEquivalence.lean`](../../PermanssonLean/Regime/GroundedFamilyEquivalence.lean) | `groundedFrozenFamilyUniformPR_iff_of_signature_match` |
| [`PermanssonLean/Examples/ConstitutiveNoninvariance.lean`](../../PermanssonLean/Examples/ConstitutiveNoninvariance.lean) | `constitutive_noninvariance_under_baseline_equivalence` |
| [`PermanssonResearch/EconomicWitness/Constitution.lean`](../../PermanssonResearch/EconomicWitness/Constitution.lean) | `original_grounded_confirmatory_uniformPR` |

## C06

**The equilibrium predecessor: models, mechanisms and exact recovery**\
Paper label: `sec:C06` · Source ZIP member: `sections/C06.tex`.

**Proof role.** Substantive EGR predecessor models and formal embedding/transport results.

**Scope boundary.** Original equilibrium predecessor is reconciled by the actual product embedding including both reference-mass and nonempty-interior branches.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-002`, `ROOT-18` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/EGR/RegimeEmbedding.lean`](../../PermanssonLean/EGR/RegimeEmbedding.lean) | `paperIEGR_iff_embeddedExactGR` |
| [`PermanssonLean/EGR/PermanssonTransport.lean`](../../PermanssonLean/EGR/PermanssonTransport.lean) | `paperIUniformPermansson_iff_embeddedRelativePR` |
| [`PermanssonLean/EGR/RecordedPropertyTransport.lean`](../../PermanssonLean/EGR/RecordedPropertyTransport.lean) | `paperIRecordedUniformPermansson_iff_embeddedRelativePR` |
| [`PermanssonLean/EGR/GroundedTransport.lean`](../../PermanssonLean/EGR/GroundedTransport.lean) | `paperIGroundedUniformPermansson_iff_embeddedGroundedUniformPR` |
| [`PermanssonLean/EGR/RecordedGroundedTransport.lean`](../../PermanssonLean/EGR/RecordedGroundedTransport.lean) | `paperIRecordedGroundedUniformPermansson_iff_embeddedGroundedUniformPR` |

## C07

**Finite recurrence and the complete law of random occupations**\
Paper label: `sec:C07` · Source ZIP member: `sections/C07.tex`.

**Proof role.** Finite recurrence and random occupation law results, with exact constructed witnesses.

**Scope boundary.** Random class-dependent joint-state occupations are not replaced by their barycenter; descriptor pushforwards can agree while joint-state limits differ.

**Documentary predecessors.** [`docs/LANE_C_RECURRENT_CLASSES.md`](../LANE_C_RECURRENT_CLASSES.md); [`docs/LANE_C_ABSORBING_REGIME_FAMILIES.md`](../LANE_C_ABSORBING_REGIME_FAMILIES.md); [`docs/LANE_C4_SIX_STATE_PRECISION.md`](../LANE_C4_SIX_STATE_PRECISION.md); [`docs/LANE_C5_SHARP_FAMILY.md`](../LANE_C5_SHARP_FAMILY.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean`](../../PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean) | `physicalOccupationLimit_ae_correct` |
| [`PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean`](../../PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean) | `physicalOccupationLimit_full_law` |
| [`PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean`](../../PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean) | `observedOccupationLimit_ae_correct` |
| [`PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean`](../../PermanssonResearch/MultipleLimit/FiniteOccupationRandomLaw.lean) | `observedOccupationLimit_full_law` |

## C08

**Exact finite GR and property-specific PR characterizations**\
Paper label: `sec:C08` · Source ZIP member: `sections/C08.tex`.

**Proof role.** Finite characterization and property-specific constitutive results under original gates.

**Scope boundary.** Property-specific PR and exact finite GR have different gates; deterministic descriptor target does not remove original nontriviality or invariance.

**Documentary predecessors.** [`docs/LANE_C_EXACT_GR_CHARACTERIZATION.md`](../LANE_C_EXACT_GR_CHARACTERIZATION.md); [`docs/LANE_C6_TYPED_OBSERVED_RESPONSE.md`](../LANE_C6_TYPED_OBSERVED_RESPONSE.md); [`docs/LANE_C7_FINITE_EVENT_RESPONSE.md`](../LANE_C7_FINITE_EVENT_RESPONSE.md); [`docs/LANE_C8_SUPPORT_GRAPH_CONSTITUTION.md`](../LANE_C8_SUPPORT_GRAPH_CONSTITUTION.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/MultipleLimit/FiniteExactGRCharacterization.lean`](../../PermanssonResearch/MultipleLimit/FiniteExactGRCharacterization.lean) | `exactGR_iff_common_reachable_target` |
| [`PermanssonResearch/MultipleLimit/FiniteExactGRCharacterization.lean`](../../PermanssonResearch/MultipleLimit/FiniteExactGRCharacterization.lean) | `exactGR_iff_exists_gates_common_reachable_target` |
| [`PermanssonResearch/MultipleLimit/SharpFamilyExactGRBridge.lean`](../../PermanssonResearch/MultipleLimit/SharpFamilyExactGRBridge.lean) | `exactGR_iff_sharp_singleton` |
| [`PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean`](../../PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean) | `opposingMass_eq_event_probability` |
| [`PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean`](../../PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean) | `effect_eq_opposingMass` |
| [`PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean`](../../PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean) | `finite_opposingMargin_attained` |
| [`PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean`](../../PermanssonResearch/MultipleLimit/OppositeClassConstitutiveMargin.lean) | `original_uniformRelativePR_iff_opposingReachability` |
| [`PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean`](../../PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean) | `SamePositiveSupport` |
| [`PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean`](../../PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean) | `recurrentClasses_eq` |
| [`PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean`](../../PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean) | `goodReachability_iff` |
| [`PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean`](../../PermanssonResearch/MultipleLimit/ObservedSupportInvariance.lean) | `badReachability_iff` |

## C09

**Nonfinite occupation: stationary, compact Feller and regenerative routes**\
Paper label: `sec:C09` · Source ZIP member: `sections/C09.tex`.

**Proof role.** Several nonfinite occupation proof profiles; a cited specialization does not certify the entire general paper argument.

**Scope boundary.** Stationary random-limit, compact Feller, initial-AC, and regenerative all-initial profiles have different premises; general L1 paper result exceeds one constant-approximant formal endpoint.

**Documentary predecessors.** [`research/paper_closures/README.md`](../../research/paper_closures/README.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/05_long_run.md`](../../research/paper_closures/spec/chapters/05_long_run.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/MultipleLimit/PolishStationaryRandomOccupation.lean`](../../PermanssonResearch/MultipleLimit/PolishStationaryRandomOccupation.lean) | `empirical_tendsto_randomLaw` |
| [`PermanssonResearch/MultipleLimit/PolishStationaryRandomOccupation.lean`](../../PermanssonResearch/MultipleLimit/PolishStationaryRandomOccupation.lean) | `exists_measurable_random_limit` |
| [`PermanssonResearch/MultipleLimit/PolishStationaryRandomOccupation.lean`](../../PermanssonResearch/MultipleLimit/PolishStationaryRandomOccupation.lean) | `descriptor_random_family` |
| [`PermanssonResearch/MultipleLimit/CompactFellerKernel.lean`](../../PermanssonResearch/MultipleLimit/CompactFellerKernel.lean) | `cluster_invariant` |
| [`PermanssonResearch/MultipleLimit/CompactFellerEmpirical.lean`](../../PermanssonResearch/MultipleLimit/CompactFellerEmpirical.lean) | `empirical_clusters_invariant_ae` |
| [`PermanssonResearch/MultipleLimit/CompactFellerEmpirical.lean`](../../PermanssonResearch/MultipleLimit/CompactFellerEmpirical.lean) | `empirical_descriptor_unique_ae` |
| [`PermanssonResearch/MultipleLimit/CompactFellerDistance.lean`](../../PermanssonResearch/MultipleLimit/CompactFellerDistance.lean) | `empirical_invariant_distance_ae` |
| [`PermanssonResearch/MultipleLimit/CompactFellerEmpirical.lean`](../../PermanssonResearch/MultipleLimit/CompactFellerEmpirical.lean) | `original_occupation_of_invariant_descriptor` |
| [`PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean`](../../PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean) | `canonical_descriptor_empirical_tendsto` |
| [`PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean`](../../PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean) | `canonical_descriptor_weak_tendsto` |
| [`PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean`](../../PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean) | `canonical_property_factor` |
| [`PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean) | `four_actual_factorizations` |

## C10

**Exit destinations, full-future restart and intervention-driven switching**\
Paper label: `sec:C10` · Source ZIP member: `sections/C10.tex`.

**Proof role.** Exit and restart laws, occupation transport and intervention-switching results.

**Scope boundary.** Restart uses actual full-future laws and correct same-T empirical comparison; exit, entry, retention and constitutive switching remain separate events.

**Documentary predecessors.** [`docs/LANE_C_EXIT_ROUTING.md`](../LANE_C_EXIT_ROUTING.md); [`docs/LANE_C_EXIT_SWITCHING.md`](../LANE_C_EXIT_SWITCHING.md); [`docs/LANE_C_EXIT_RESTART.md`](../LANE_C_EXIT_RESTART.md); [`docs/LANE_C_EXIT_RANDOM_ENTRY.md`](../LANE_C_EXIT_RANDOM_ENTRY.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-011` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/RegimeExit/ExitRouting.lean`](../../PermanssonResearch/RegimeExit/ExitRouting.lean) | `exitRoutingInfiniteMeasure` |
| [`PermanssonResearch/RegimeExit/ExitConservation.lean`](../../PermanssonResearch/RegimeExit/ExitConservation.lean) | `exitRoutingInfinite_eq_prob_exit_in` |
| [`PermanssonResearch/RegimeExit/StoppedFutureRestart.lean`](../../PermanssonResearch/RegimeExit/StoppedFutureRestart.lean) | `firstExitStepMeasure_restrict_diff_region` |
| [`PermanssonResearch/RegimeExit/QSDDestination.lean`](../../PermanssonResearch/RegimeExit/QSDDestination.lean) | `qsdRoutingInfinite_eq_fraction` |
| [`PermanssonResearch/RegimeExit/QSDExitBoundary.lean`](../../PermanssonResearch/RegimeExit/QSDExitBoundary.lean) | `qsdThetaOne_no_exit` |
| [`PermanssonResearch/RegimeExit/ShiftedPrefixStationarity.lean`](../../PermanssonResearch/RegimeExit/ShiftedPrefixStationarity.lean) | `hasCanonicalLastStateRestart` |
| [`PermanssonResearch/RegimeExit/StoppedFutureRestart.lean`](../../PermanssonResearch/RegimeExit/StoppedFutureRestart.lean) | `firstExit_shift_event_restart` |
| [`PermanssonResearch/RegimeExit/StoppedFutureRestart.lean`](../../PermanssonResearch/RegimeExit/StoppedFutureRestart.lean) | `infiniteStoppedFutureMeasure_eq_bind` |
| [`PermanssonResearch/RegimeExit/RandomEntryOccupation.lean`](../../PermanssonResearch/RegimeExit/RandomEntryOccupation.lean) | `randomEntry_occupation_ae` |
| [`PermanssonResearch/RegimeExit/InProbabilityOccupation.lean`](../../PermanssonResearch/RegimeExit/InProbabilityOccupation.lean) | `randomEntry_occupation_inProbability` |
| [`PermanssonResearch/RegimeExit/InProbabilityOccupation.lean`](../../PermanssonResearch/RegimeExit/InProbabilityOccupation.lean) | `inProbability_deviation_eventually_le` |
| [`PermanssonResearch/RegimeExit/Proposition42f.lean`](../../PermanssonResearch/RegimeExit/Proposition42f.lean) | `proposition_4_2f_almostSure` |
| [`PermanssonResearch/RegimeExit/Proposition42f.lean`](../../PermanssonResearch/RegimeExit/Proposition42f.lean) | `proposition_4_2f_inProbability` |
| [`PermanssonResearch/RegimeExit/SwitchGrounded.lean`](../../PermanssonResearch/RegimeExit/SwitchGrounded.lean) | `switch_grounded_confirmatory_uniformPR` |
| [`PermanssonResearch/RegimeExit/SwitchWitnessModels.lean`](../../PermanssonResearch/RegimeExit/SwitchWitnessModels.lean) | `full_world_fixed` |
| [`PermanssonResearch/RegimeExit/SwitchWitnessExactGR.lean`](../../PermanssonResearch/RegimeExit/SwitchWitnessExactGR.lean) | `source_exactGR` |
| [`PermanssonResearch/RegimeExit/SwitchWitnessExactGR.lean`](../../PermanssonResearch/RegimeExit/SwitchWitnessExactGR.lean) | `target_exactGR` |
| [`PermanssonResearch/RegimeExit/SwitchWitnessMargin.lean`](../../PermanssonResearch/RegimeExit/SwitchWitnessMargin.lean) | `full_constitutive_margin_ge_half` |
| [`PermanssonResearch/RegimeExit/SwitchWitnessOccupation.lean`](../../PermanssonResearch/RegimeExit/SwitchWitnessOccupation.lean) | `actual_successful_switch_occupation_ae` |
| [`PermanssonResearch/RegimeExit/ExitModels.lean`](../../PermanssonResearch/RegimeExit/ExitModels.lean) | `f2Matrix` |
| [`PermanssonResearch/RegimeExit/ExitFiniteWitness.lean`](../../PermanssonResearch/RegimeExit/ExitFiniteWitness.lean) | `f1_two_step_to_a` |
| [`PermanssonResearch/RegimeExit/ExitAdversaries.lean`](../../PermanssonResearch/RegimeExit/ExitAdversaries.lean) | `f4_destination_arrival_not_exact_persistence` |
| [`PermanssonResearch/RegimeExit/ExitLongHorizonWitness.lean`](../../PermanssonResearch/RegimeExit/ExitLongHorizonWitness.lean) | `actual_typed_thetaOne_QSD_and_leaking_other_state` |

## C11

**Admitted grammars, interaction and minimality**\
Paper label: `sec:C11` · Source ZIP member: `sections/C11.tex`.

**Proof role.** Admitted grammar definitions, order results and finite interaction examples.

**Scope boundary.** Least-positive requires positivity and lower-bound inclusion; minimality transport needs actual strict lower-set coverage, and inverse-image strictness needs nonempty fibres.

**Documentary predecessors.** [`docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md`](../LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md); [`docs/LANE_B2_SEQUENTIAL_EFFECTS.md`](../LANE_B2_SEQUENTIAL_EFFECTS.md); [`research/paper_closures/post_merge_79/NEXT06_B01_OVERLAP.md`](../../research/paper_closures/post_merge_79/NEXT06_B01_OVERLAP.md); [`research/paper_closures/spec/chapters/08_grammar_economic.md`](../../research/paper_closures/spec/chapters/08_grammar_economic.md). These documents retain their original source/date scope.

**Manuscript review references.** `Q01`, `Q02` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/GrammarRobust/AtomicBank.lean`](../../PermanssonResearch/GrammarRobust/AtomicBank.lean) | `AtomicBank` |
| [`PermanssonResearch/GrammarRobust/PartitionGrammar.lean`](../../PermanssonResearch/GrammarRobust/PartitionGrammar.lean) | `PartitionGrammar` |
| [`PermanssonResearch/GrammarRobust/CompatibleOverlap.lean`](../../PermanssonResearch/GrammarRobust/CompatibleOverlap.lean) | `applyCompatiblePatches_eq_of_membership` |
| [`PermanssonResearch/GrammarRobust/OverlapKernelAssembly.lean`](../../PermanssonResearch/GrammarRobust/OverlapKernelAssembly.lean) | `overlapModel_pathLaw_eq_of_membership` |
| [`PermanssonResearch/GrammarRobust/OverlapCanonicalBridge.lean`](../../PermanssonResearch/GrammarRobust/OverlapCanonicalBridge.lean) | `overlapIntervention_margin_eq` |
| [`PermanssonResearch/GrammarRobust/OriginalInterventionBridge.lean`](../../PermanssonResearch/GrammarRobust/OriginalInterventionBridge.lean) | `admittedBlockIntervention_apply` |
| [`PermanssonResearch/GrammarRobust/EffectTransport.lean`](../../PermanssonResearch/GrammarRobust/EffectTransport.lean) | `Coarsening.blockMargin_lift_eq` |
| [`PermanssonResearch/GrammarRobust/PRStatusTransport.lean`](../../PermanssonResearch/GrammarRobust/PRStatusTransport.lean) | `Coarsening.uniformRelativePR_lift_iff` |
| [`PermanssonResearch/GrammarRobust/ConditionalMargins.lean`](../../PermanssonResearch/GrammarRobust/ConditionalMargins.lean) | `jointOnly_conditionalMargins_eq_jointMargin` |
| [`PermanssonResearch/GrammarRobust/InteractionVector.lean`](../../PermanssonResearch/GrammarRobust/InteractionVector.lean) | `interactionVector_norm_le_condUpdate_add_update` |
| [`PermanssonResearch/GrammarRobust/Minimality.lean`](../../PermanssonResearch/GrammarRobust/Minimality.lean) | `exists_minimal_allowed_subblock` |
| [`PermanssonResearch/GrammarRobust/LowerSetTransport.lean`](../../PermanssonResearch/GrammarRobust/LowerSetTransport.lean) | `minimalPositive_iff_of_lowerSet_lifting` |
| [`PermanssonResearch/GrammarRobust/B02ActualOriginalMarginFixture.lean`](../../PermanssonResearch/GrammarRobust/B02ActualOriginalMarginFixture.lean) | `actual_coarsening_does_not_preserve_minimality` |
| [`PermanssonResearch/GrammarRobust/B02LocalOriginalMarginClosure.lean`](../../PermanssonResearch/GrammarRobust/B02LocalOriginalMarginClosure.lean) | `original_local_minimality_without_global_isomorphism` |

## C12

**Finite constitutive certificates and primitive error budgets**\
Paper label: `sec:C12` · Source ZIP member: `sections/C12.tex`.

**Proof role.** Finite certificate and error-budget results; actual common-kernel and comparison-domain hypotheses matter.

**Scope boundary.** Separate primitive additive and common-mass product routes; formal finite-prefix interface also requests the joint-state (Y,Y) common-kernel instance.

**Documentary predecessors.** [`docs/CQ1_FINITE_PATH_BRIDGE.md`](../CQ1_FINITE_PATH_BRIDGE.md); [`docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md`](../CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md); [`docs/CQ1_CERTIFICATE_TRANSPORT.md`](../CQ1_CERTIFICATE_TRANSPORT.md); [`docs/LANE_A2_PRIMITIVE_TV.md`](../LANE_A2_PRIMITIVE_TV.md); [`research/paper_closures/spec/chapters/04_robustness.md`](../../research/paper_closures/spec/chapters/04_robustness.md). These documents retain their original source/date scope.

**Manuscript review references.** `Q03` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ConstitutiveQuasi/Certificate.lean`](../../PermanssonResearch/ConstitutiveQuasi/Certificate.lean) | `FiniteConstitutiveCertificate.uniformConstitution` |
| [`PermanssonResearch/ConstitutiveQuasi/CertificateTransport.lean`](../../PermanssonResearch/ConstitutiveQuasi/CertificateTransport.lean) | `transportFiniteConstitutiveCertificate` |
| [`PermanssonResearch/Perturbation/PrimitiveMargin.lean`](../../PermanssonResearch/Perturbation/PrimitiveMargin.lean) | `transportPrimitiveFiniteConstitutiveCertificate` |
| [`PermanssonResearch/Perturbation/PrimitiveMargin.lean`](../../PermanssonResearch/Perturbation/PrimitiveMargin.lean) | `PrimitiveErrorBounds.kernelBudget` |
| [`PermanssonResearch/Perturbation/PrimitiveProductTV.lean`](../../PermanssonResearch/Perturbation/PrimitiveProductTV.lean) | `inducedKernel_tv_le_primitive_product` |
| [`PermanssonResearch/Perturbation/PrimitiveLipschitz.lean`](../../PermanssonResearch/Perturbation/PrimitiveLipschitz.lean) | `primitiveLipschitz_constitutiveMargin_abs_le` |
| [`PermanssonResearch/Perturbation/PrimitiveMargin.lean`](../../PermanssonResearch/Perturbation/PrimitiveMargin.lean) | `reportedPrimitiveMargin_abs_le` |
| [`PermanssonResearch/Perturbation/FinitePrimitiveMetric.lean`](../../PermanssonResearch/Perturbation/FinitePrimitiveMetric.lean) | `PrimitiveMetricBounds.exists_weighted_coupling` |
| [`PermanssonResearch/ConstitutiveQuasi/AdversarialExamples.lean`](../../PermanssonResearch/ConstitutiveQuasi/AdversarialExamples.lean) | `noZeroHorizonFiniteConstitutiveCertificate` |
| [`PermanssonResearch/ConstitutiveQuasi/CertificateExamples.lean`](../../PermanssonResearch/ConstitutiveQuasi/CertificateExamples.lean) | `positiveFiniteCertificate` |
| [`PermanssonResearch/ConstitutiveQuasi/NonzeroErrorExample.lean`](../../PermanssonResearch/ConstitutiveQuasi/NonzeroErrorExample.lean) | `randomizedPair` |
| [`PermanssonResearch/ConstitutiveQuasi/AdversarialExamples.lean`](../../PermanssonResearch/ConstitutiveQuasi/AdversarialExamples.lean) | `noStrategicApproximationPair_of_world_ne` |
| [`PermanssonResearch/Perturbation/PrimitiveAdversaries.lean`](../../PermanssonResearch/Perturbation/PrimitiveAdversaries.lean) | `qsd_is_not_uniform_persistence_witness` |

## C13

**Finite, localized and whole-path probability bounds**\
Paper label: `sec:C13` · Source ZIP member: `sections/C13.tex`.

**Proof role.** Common-mass and path/score estimates with distinct finite, localized and whole-path premises.

**Scope boundary.** Probability normalization, initial mismatch and conditional histories stay explicit; a unit defect or unit initial mismatch trivializes the infinite product even when defects are summable.

**Documentary predecessors.** [`docs/LANE_A2_PRIMITIVE_TV.md`](../LANE_A2_PRIMITIVE_TV.md); [`docs/LANE_E1_APPROX_QUOTIENT.md`](../LANE_E1_APPROX_QUOTIENT.md); [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_79/NEXT03_Q03_DEPENDENT_HISTORY_SCOPE.md`](../../research/paper_closures/post_merge_79/NEXT03_Q03_DEPENDENT_HISTORY_SCOPE.md). These documents retain their original source/date scope.

**Retained obligations.** [Later-Q1](RESIDUAL_STATUS.md#later-q1).

**Manuscript review references.** `Q04`, `Q05` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Probability/DependentHistoryCommonMass.lean`](../../PermanssonResearch/Probability/DependentHistoryCommonMass.lean) | `prefix_tv_le_product` |
| [`PermanssonResearch/Probability/LocalizedHistoryTV.lean`](../../PermanssonResearch/Probability/LocalizedHistoryTV.lean) | `historyEvolution_tv_le_sum` |
| [`PermanssonResearch/Probability/GoodHistoryVisit.lean`](../../PermanssonResearch/Probability/GoodHistoryVisit.lean) | `historyEvolution_tv_le_goodVisits` |
| [`PermanssonResearch/Probability/FullPathProductTV.lean`](../../PermanssonResearch/Probability/FullPathProductTV.lean) | `path_tv_le_product` |
| [`PermanssonResearch/Probability/DiscountedInitialBudget.lean`](../../PermanssonResearch/Probability/DiscountedInitialBudget.lean) | `discounted_output_score_error_initial` |
| [`PermanssonResearch/Probability/DependentThreeStageSaturation.lean`](../../PermanssonResearch/Probability/DependentThreeStageSaturation.lean) | `dependent_three_stage_halfL1_exact` |
| [`verification/research/tranche10_q04_scope_receipt_addendum.lean`](../../verification/research/tranche10_q04_scope_receipt_addendum.lean) | `original_margin_error_equals_charged_budget` |
| [`verification/research/tranche7_q05_original_margin_addendum.lean`](../../verification/research/tranche7_q05_original_margin_addendum.lean) | `fine_original_margin` |

## C14

**Transport metrics, contraction and invariant-law construction**\
Paper label: `sec:C14` · Source ZIP member: `sections/C14.tex`.

**Proof role.** Metric transport, duality and invariant-law construction under the stated finite/first-moment profiles.

**Scope boundary.** Dual calculus may use pseudometrics; uniqueness uses a metric. First-moment KR does not need completeness, Banach invariants do; both compared laws must be supplied/constructed under their own premises.

**Documentary predecessors.** [`docs/LANE_A3_CONTRACTIVE.md`](../LANE_A3_CONTRACTIVE.md); [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/05_long_run.md`](../../research/paper_closures/spec/chapters/05_long_run.md). These documents retain their original source/date scope.

**Retained obligations.** [A-01](RESIDUAL_STATUS.md#a-01).

**Manuscript review references.** `Q06` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Probability/FiniteKantorovichDuality.lean`](../../PermanssonResearch/Probability/FiniteKantorovichDuality.lean) | `exists_plan_of_w1DualLE` |
| [`PermanssonResearch/Probability/FirstMomentKantorovichDuality.lean`](../../PermanssonResearch/Probability/FirstMomentKantorovichDuality.lean) | `firstMoment_couplingW1_le_of_w1DualLE` |
| [`PermanssonResearch/Probability/FirstMomentCompleteness.lean`](../../PermanssonResearch/Probability/FirstMomentCompleteness.lean) | `cauchySeq_has_limit` |
| [`PermanssonResearch/Perturbation/DirectDualContraction.lean`](../../PermanssonResearch/Perturbation/DirectDualContraction.lean) | `isW1Contraction_of_test_images` |
| [`PermanssonResearch/Perturbation/DobrushinContraction.lean`](../../PermanssonResearch/Perturbation/DobrushinContraction.lean) | `isW1Contraction_dobrushin` |
| [`PermanssonResearch/Perturbation/DobrushinContraction.lean`](../../PermanssonResearch/Perturbation/DobrushinContraction.lean) | `isW1Contraction_doeblin` |
| [`PermanssonResearch/Perturbation/FiniteStateMetricContraction.lean`](../../PermanssonResearch/Perturbation/FiniteStateMetricContraction.lean) | `StateMetricBounds.weighted_isW1Contraction` |
| [`PermanssonResearch/Perturbation/FirstMomentKernel.lean`](../../PermanssonResearch/Perturbation/FirstMomentKernel.lean) | `preservesFirstMoment_of_drift` |
| [`PermanssonResearch/Perturbation/FirstMomentInvariant.lean`](../../PermanssonResearch/Perturbation/FirstMomentInvariant.lean) | `automatic_invariant_and_convergence` |
| [`PermanssonResearch/Perturbation/ContractiveOccupation.lean`](../../PermanssonResearch/Perturbation/ContractiveOccupation.lean) | `invariantLaw_wasserstein_le` |
| [`PermanssonResearch/Perturbation/GeneratedInvariantPerturbation.lean`](../../PermanssonResearch/Perturbation/GeneratedInvariantPerturbation.lean) | `generated_coupling_bound` |
| [`PermanssonResearch/Perturbation/ContractiveAdversaries.lean`](../../PermanssonResearch/Perturbation/ContractiveAdversaries.lean) | `contraction_does_not_transfer_survival` |

## C15

**Frozen occupation properties and original-margin robustness**\
Paper label: `sec:C15` · Source ZIP member: `sections/C15.tex`.

**Proof role.** Occupation property and robustness adapters requiring the actual four process factorizations.

**Scope boundary.** One globally fixed property, fallback and four actual path-law factorizations; complete separable metric/Borel selector profile, continuous descriptor for weak regenerative route, distinct measurable-descriptor P1 route.

**Documentary predecessors.** [`docs/LANE_A3_CONTRACTIVE.md`](../LANE_A3_CONTRACTIVE.md); [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md). These documents retain their original source/date scope.

**Retained obligations.** [A-04](RESIDUAL_STATUS.md#a-04).

**Manuscript review references.** `Q07`, `Q08`, `Q09`, `Q10` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Perturbation/FiniteOccupationProperty.lean`](../../PermanssonResearch/Perturbation/FiniteOccupationProperty.lean) | `property_factor_unique_class` |
| [`PermanssonResearch/Perturbation/FirstMomentOccupationProperty.lean`](../../PermanssonResearch/Perturbation/FirstMomentOccupationProperty.lean) | `property_factor_of_ae_empirical_limit` |
| [`PermanssonResearch/Perturbation/FiniteOccupationFactorization.lean`](../../PermanssonResearch/Perturbation/FiniteOccupationFactorization.lean) | `recurrentClass_unique_of_contraction` |
| [`PermanssonResearch/Perturbation/RegenerativeData.lean`](../../PermanssonResearch/Perturbation/RegenerativeData.lean) | `Data.stationary_invariant` |
| [`PermanssonResearch/Perturbation/RegenerativeOccupationProperty.lean`](../../PermanssonResearch/Perturbation/RegenerativeOccupationProperty.lean) | `property_factor_regenerative` |
| [`PermanssonResearch/Perturbation/RegenerativeCompactOccupation.lean`](../../PermanssonResearch/Perturbation/RegenerativeCompactOccupation.lean) | `numericLimit_eq_functional_lawLimit` |
| [`PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean`](../../PermanssonResearch/MultipleLimit/RegenerativeFirstMomentOccupation.lean) | `canonical_descriptor_empirical_tendsto` |
| [`PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean) | `StateBudget` |
| [`PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean) | `DescriptorBudget` |
| [`PermanssonResearch/Perturbation/FiniteOccupationFactorization.lean`](../../PermanssonResearch/Perturbation/FiniteOccupationFactorization.lean) | `four_actual_factorizations` |
| [`PermanssonResearch/Perturbation/RegenerativeOccupationFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeOccupationFactorization.lean) | `four_actual_factorizations` |
| [`PermanssonResearch/Perturbation/RegenerativeCompactFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeCompactFactorization.lean) | `four_actual_factorizations` |
| [`PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean) | `four_actual_factorizations` |
| [`PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean) | `generated_occupationMargin_robust` |
| [`PermanssonResearch/Perturbation/FiniteMetricProtocol.lean`](../../PermanssonResearch/Perturbation/FiniteMetricProtocol.lean) | `MetricProtocolBounds.original_occupationMargin` |
| [`PermanssonResearch/Perturbation/A04FourOutputNecessityCountermodel.lean`](../../PermanssonResearch/Perturbation/A04FourOutputNecessityCountermodel.lean) | `no_general_three_output_margin_formula` |
| [`PermanssonResearch/Perturbation/A05SurvivalOccupationCountermodel.lean`](../../PermanssonResearch/Perturbation/A05SurvivalOccupationCountermodel.lean) | `cannot_replace_full_path_survival_by_stationary_mass` |

## C16

**Exact and approximate intervention-compatible quotients**\
Paper label: `sec:C16` · Source ZIP member: `sections/C16.tex`.

**Proof role.** Intervention-compatible quotient constructions and conditional property transport.

**Scope boundary.** Projected process need not be Markov; geometric common-mass/RN profile is stronger than old linear general-measurable profile; canonical positive initial mismatch adapter remains separately scoped.

**Documentary predecessors.** [`docs/LANE_E1_APPROX_QUOTIENT.md`](../LANE_E1_APPROX_QUOTIENT.md); [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`research/paper_closures/post_merge_102/NEXT04_ORIGINAL_MARGIN_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT04_ORIGINAL_MARGIN_V2_SCOPE.md); [`research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md`](../../research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md). These documents retain their original source/date scope.

**Retained obligations.** [Later-Q1](RESIDUAL_STATUS.md#later-q1).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/Quotient/PathLaw.lean`](../../PermanssonLean/Quotient/PathLaw.lean) | `pathLaw_map_eq_of_kernelIntertwines` |
| [`PermanssonLean/Quotient/Preservation.lean`](../../PermanssonLean/Quotient/Preservation.lean) | `InterventionCompatibleStateQuotient` |
| [`PermanssonLean/Quotient/Preservation.lean`](../../PermanssonLean/Quotient/Preservation.lean) | `quotient_frozenFamilyUniformPR_iff` |
| [`PermanssonLean/Quotient/GroundedPreservation.lean`](../../PermanssonLean/Quotient/GroundedPreservation.lean) | `quotient_groundedFrozenFamilyUniformPR_iff` |
| [`PermanssonResearch/Quotient/GeometricQuotient.lean`](../../PermanssonResearch/Quotient/GeometricQuotient.lean) | `approxQuotient_prefix_tv_le_geometric` |
| [`PermanssonResearch/Quotient/GeometricMargin.lean`](../../PermanssonResearch/Quotient/GeometricMargin.lean) | `geometricQuotient_margin_abs_le` |
| [`PermanssonResearch/Quotient/NonstationaryProjectedTransport.lean`](../../PermanssonResearch/Quotient/NonstationaryProjectedTransport.lean) | `projected_evolution_tv_le_product` |
| [`PermanssonResearch/Quotient/DiscountedCanonicalMarginClosure.lean`](../../PermanssonResearch/Quotient/DiscountedCanonicalMarginClosure.lean) | `actual_canonical_discounted_original_margin` |
| [`PermanssonResearch/Quotient/Q01NonLumpableProjectionCountermodel.lean`](../../PermanssonResearch/Quotient/Q01NonLumpableProjectionCountermodel.lean) | `no_autonomous_coarse_transition` |
| [`PermanssonResearch/Quotient/ApproxAdversaries.lean`](../../PermanssonResearch/Quotient/ApproxAdversaries.lean) | `small_defect_does_not_preserve_invariance` |

## C17

**Finite histories, monitors, and adaptive feedback**\
Paper label: `sec:C17` · Source ZIP member: `sections/C17.tex`.

**Proof role.** Finite history-law and monitor control results with behavioral-policy quantifiers.

**Scope boundary.** Finite legal menus, history chronology, success/risk monitor separation and m+1 observations for m transitions; residence block index is j+m<=t.

**Documentary predecessors.** [`docs/D1_CONTROLLED_KERNEL.md`](../D1_CONTROLLED_KERNEL.md); [`docs/D1_HISTORY_DEPENDENT.md`](../D1_HISTORY_DEPENDENT.md); [`docs/D1_TYPED_HISTORY_DEPENDENT.md`](../D1_TYPED_HISTORY_DEPENDENT.md); [`docs/D2_RESIDENCE_OBJECTIVE.md`](../D2_RESIDENCE_OBJECTIVE.md); [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md). These documents retain their original source/date scope.

**Manuscript review references.** `CTRL-12` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/ControlledKernel.lean`](../../PermanssonResearch/ReverseSolver/ControlledKernel.lean) | `feedback_preserves_world` |
| [`PermanssonResearch/ReverseSolver/ControlledKernel.lean`](../../PermanssonResearch/ReverseSolver/ControlledKernel.lean) | `feedback_preserves_update` |
| [`PermanssonResearch/ReverseSolver/ControlledKernel.lean`](../../PermanssonResearch/ReverseSolver/ControlledKernel.lean) | `feedbackMatrix_constant` |
| [`PermanssonResearch/ReverseSolver/MonitorOptimality.lean`](../../PermanssonResearch/ReverseSolver/MonitorOptimality.lean) | `monitor_optimal_and_attained` |
| [`PermanssonResearch/ReverseSolver/MonitorOptimality.lean`](../../PermanssonResearch/ReverseSolver/MonitorOptimality.lean) | `monitor_trace_value_dominates_behavioral_history` |
| [`PermanssonResearch/ReverseSolver/MonitorHistoryBridge.lean`](../../PermanssonResearch/ReverseSolver/MonitorHistoryBridge.lean) | `monitor_history_probability_optimal_and_attained` |
| [`PermanssonResearch/ReverseSolver/ResidenceEvent.lean`](../../PermanssonResearch/ReverseSolver/ResidenceEvent.lean) | `hit_does_not_imply_stay` |
| [`PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean`](../../PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean) | `avoidScan_success_iff_block` |
| [`PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean`](../../PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean) | `danger_precedes_simultaneous_success` |
| [`PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean`](../../PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean) | `danger_after_success_does_not_undo` |
| [`PermanssonResearch/ReverseSolver/MonitorEventOptimality.lean`](../../PermanssonResearch/ReverseSolver/MonitorEventOptimality.lean) | `behavioralResidence_optimal_and_attained` |
| [`PermanssonResearch/ReverseSolver/AdaptiveGrammarControl.lean`](../../PermanssonResearch/ReverseSolver/AdaptiveGrammarControl.lean) | `typedChronologicalLaw_eq` |
| [`PermanssonResearch/ReverseSolver/AdaptiveGrammarControl.lean`](../../PermanssonResearch/ReverseSolver/AdaptiveGrammarControl.lean) | `adaptive_block_optimal_and_attained` |

## C18

**Belief control and nonstationary dynamics**\
Paper label: `sec:C18` · Source ZIP member: `sections/C18.tex`.

**Proof role.** Finite belief/control reductions and chronological nonstationary models.

**Scope boundary.** Finite nonempty hidden/observation/decision sets and common legal menu; belief reduction is for the stated observation-admissible history class.

**Documentary predecessors.** [`docs/D1_BELLMAN.md`](../D1_BELLMAN.md); [`docs/D1_NONSTATIONARY_RATIONAL.md`](../D1_NONSTATIONARY_RATIONAL.md); [`docs/D1_TYPED_NONSTATIONARY.md`](../D1_TYPED_NONSTATIONARY.md); [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md). These documents retain their original source/date scope.

**Manuscript review references.** `CTRL-01`, `CTRL-02`, `CTRL-03` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/BeliefFilter.lean`](../../PermanssonResearch/ReverseSolver/BeliefFilter.lean) | `forward_belief` |
| [`PermanssonResearch/ReverseSolver/BeliefFilter.lean`](../../PermanssonResearch/ReverseSolver/BeliefFilter.lean) | `observed_filter_law` |
| [`PermanssonResearch/ReverseSolver/BeliefFilter.lean`](../../PermanssonResearch/ReverseSolver/BeliefFilter.lean) | `zero_word_mass` |
| [`PermanssonResearch/ReverseSolver/BeliefAlpha.lean`](../../PermanssonResearch/ReverseSolver/BeliefAlpha.lean) | `alpha_envelope` |
| [`PermanssonResearch/ReverseSolver/BeliefAlpha.lean`](../../PermanssonResearch/ReverseSolver/BeliefAlpha.lean) | `optimalTree_attains` |
| [`PermanssonResearch/ReverseSolver/BeliefAlpha.lean`](../../PermanssonResearch/ReverseSolver/BeliefAlpha.lean) | `value_convex` |
| [`PermanssonResearch/ReverseSolver/BeliefMonitor.lean`](../../PermanssonResearch/ReverseSolver/BeliefMonitor.lean) | `monitored_history_dominated` |
| [`PermanssonResearch/ReverseSolver/BeliefMonitor.lean`](../../PermanssonResearch/ReverseSolver/BeliefMonitor.lean) | `monitored_history_attained` |
| [`verification/research/tranche9_d06_scope_receipt_addendum.lean`](../../verification/research/tranche9_d06_scope_receipt_addendum.lean) | `one_prior_reachable_completion_values` |
| [`verification/research/tranche9_d06_scope_receipt_addendum.lean`](../../verification/research/tranche9_d06_scope_receipt_addendum.lean) | `no_readout_only_reachable_completion_value` |
| [`PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean) | `successProbability_eq_policyValue` |
| [`PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean) | `successProbability_le_bellman` |
| [`PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryOptimality.lean) | `maximizingSchedule_actual_probability` |
| [`PermanssonResearch/ReverseSolver/NonstationaryTypedTransport.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryTypedTransport.lean) | `typed_prefix_atom_transport` |
| [`PermanssonResearch/ReverseSolver/NonstationaryTypedTransport.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryTypedTransport.lean) | `typed_prefixLaw_map` |

## C19

**Occupation flows, risk constraints, and infinite safety**\
Paper label: `sec:C19` · Source ZIP member: `sections/C19.tex`.

**Proof role.** Finite occupation-flow optimization, risk constraints and a separate infinite-safety argument.

**Scope boundary.** Exact flow reconstruction quantifies over stated behavioral policies; through-horizon danger survives completed success; infinite safety uses actual infinite law.

**Documentary predecessors.** [`docs/D0_FROZEN_MENU.md`](../D0_FROZEN_MENU.md); [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/06_solver.md`](../../research/paper_closures/spec/chapters/06_solver.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean`](../../PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean) | `solveRiskFlow_none_iff_no_behavioral_policy` |
| [`PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean`](../../PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean) | `solveRiskFlow_some_actual_optimal` |
| [`PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean`](../../PermanssonResearch/ReverseSolver/FlowPolicyOptimality.lean) | `actualTerminalScore_eq_flowValue` |
| [`PermanssonResearch/ReverseSolver/FlowRiskWitness.lean`](../../PermanssonResearch/ReverseSolver/FlowRiskWitness.lean) | `actual_half_attains` |
| [`PermanssonResearch/ReverseSolver/FlowRiskWitness.lean`](../../PermanssonResearch/ReverseSolver/FlowRiskWitness.lean) | `all_actual_feasible_success_le` |
| [`PermanssonResearch/ReverseSolver/FlowRiskWitness.lean`](../../PermanssonResearch/ReverseSolver/FlowRiskWitness.lean) | `full_risky_choice_is_infeasible` |
| [`PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean`](../../PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean) | `actual_risk_integral_eq_literal` |
| [`PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean`](../../PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean) | `actual_risk_probability_eq_occupancy` |
| [`PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean`](../../PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean) | `actual_success_integral_eq_original` |
| [`PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean) | `deterministic_stationary_infinite_optimum` |
| [`PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean) | `infiniteSafety_isGreatest` |
| [`PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean) | `invariantCore_iff_almostSureSafety` |
| [`PermanssonResearch/ReverseSolver/InfiniteSafetyLeakage.lean`](../../PermanssonResearch/ReverseSolver/InfiniteSafetyLeakage.lean) | `high_actual_finite_survival_zero_infinite` |

## C20

**Total rational construction and recovery of the original semantics**\
Paper label: `sec:C20` · Source ZIP member: `sections/C20.tex`.

**Proof role.** Total rational construction and recovery of original model semantics under typed gates.

**Scope boundary.** Total rational constructors retain positive dimensions, nonempty menus/comparison sets and path-law nontriviality; worst starts minimize absolute effects, not treated event probabilities.

**Documentary predecessors.** [`docs/D0_FROZEN_MENU.md`](../D0_FROZEN_MENU.md); [`docs/LANE_C9_CERTIFIED_MENU_SYNTHESIS.md`](../LANE_C9_CERTIFIED_MENU_SYNTHESIS.md); [`docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`](../LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md); [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](../LANE_C11_CLASS_STATIONARY_CERTIFICATION.md). These documents retain their original source/date scope.

**Manuscript review references.** `CTRL-04`, `CTRL-05`, `CTRL-14` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/RationalGraphCompleteness.lean`](../../PermanssonResearch/ReverseSolver/RationalGraphCompleteness.lean) | `reachesB_iff_rationalReachable` |
| [`PermanssonResearch/ReverseSolver/RationalCramerCertification.lean`](../../PermanssonResearch/ReverseSolver/RationalCramerCertification.lean) | `referenceDirichlet_check_true` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceStationaryFamily.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceStationaryFamily.lean) | `referenceStationaryFamily_check` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceTypedBridge.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceTypedBridge.lean) | `referenceClassCandidate_eq_native` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceProbability.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceProbability.lean) | `referenceWeights_probability` |
| [`PermanssonResearch/ReverseSolver/TypedOriginalMenuMargin.lean`](../../PermanssonResearch/ReverseSolver/TypedOriginalMenuMargin.lean) | `typed_numericMargin_eq_original` |
| [`PermanssonResearch/ReverseSolver/TypedOriginalMenuMargin.lean`](../../PermanssonResearch/ReverseSolver/TypedOriginalMenuMargin.lean) | `realized_numeric_menu_selected_dominates` |
| [`PermanssonResearch/ReverseSolver/C10ReleaseRegimeEquivalences.lean`](../../PermanssonResearch/ReverseSolver/C10ReleaseRegimeEquivalences.lean) | `checkedFullReceipt_positive_iff_original_uniformPR_of_exactGR` |
| [`PermanssonResearch/ReverseSolver/C10ReleaseRegimeEquivalences.lean`](../../PermanssonResearch/ReverseSolver/C10ReleaseRegimeEquivalences.lean) | `checkedFullReceipt_originalPR_iff_exactGR_and_support_of_literalMode` |

## C21

**Nonlinear occupation objectives and stationary policy optimization**\
Paper label: `sec:C21` · Source ZIP member: `sections/C21.tex`.

**Proof role.** Classwise nonlinear occupation objectives and stationary-policy optimization.

**Scope boundary.** Nonlinear optimizer is for deterministic stationary policies; phase-aware and multichain examples do not establish unrestricted randomized/history optimality.

**Documentary predecessors.** [`docs/D2_RESIDENCE_OBJECTIVE.md`](../D2_RESIDENCE_OBJECTIVE.md); [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](../LANE_C11_CLASS_STATIONARY_CERTIFICATION.md); [`research/paper_closures/post_merge_102/NEXT06_NATIVE_POLICY_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT06_NATIVE_POLICY_V2_SCOPE.md); [`research/paper_closures/post_merge_112/README.md`](../../research/paper_closures/post_merge_112/README.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/StationaryOccupationObjective.lean`](../../PermanssonResearch/ReverseSolver/StationaryOccupationObjective.lean) | `rationalObjective_eq_actual` |
| [`PermanssonResearch/ReverseSolver/StationaryOccupationObjective.lean`](../../PermanssonResearch/ReverseSolver/StationaryOccupationObjective.lean) | `occupation_functional_integrable` |
| [`PermanssonResearch/ReverseSolver/StationaryMenuOptimization.lean`](../../PermanssonResearch/ReverseSolver/StationaryMenuOptimization.lean) | `stationary_menu_actual_optimal_and_attained` |
| [`PermanssonResearch/ReverseSolver/StationaryMenuOptimization.lean`](../../PermanssonResearch/ReverseSolver/StationaryMenuOptimization.lean) | `computedStationaryChoice_attains` |
| [`PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean`](../../PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean) | `certified_boolean_score_exact` |
| [`PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean`](../../PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean) | `boolean_rational_objective_eq_actual` |
| [`PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean`](../../PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean) | `actual_two_absorbing_full_path_mixture` |
| [`PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean`](../../PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean) | `actual_equal_mixture_original_nonlinear_score` |
| [`PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean`](../../PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean) | `actual_mixed_nonlinear_half_not_barycenter` |
| [`PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean) | `native_phase_blind_actual_le_five_sixths` |
| [`PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean) | `native_phase_blind_actual_attained` |
| [`PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean) | `native_actual_phase_aware_strictly_beats_phase_blind` |

## C22

**Robust control, rectangular Nature, and private randomization**\
Paper label: `sec:C22` · Source ZIP member: `sections/C22.tex`.

**Proof role.** Robust and private-randomization control profiles; chronology and Nature commitment remain distinct.

**Scope boundary.** Nature observing the realized control, private-current-draw stage play and a model fixed at time zero are distinct games.

**Documentary predecessors.** [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_79/NEXT06_D05_CHRONOLOGICAL_SCOPE.md`](../../research/paper_closures/post_merge_79/NEXT06_D05_CHRONOLOGICAL_SCOPE.md). These documents retain their original source/date scope.

**Manuscript review references.** `CTRL-06` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/RectangularGameLaw.lean`](../../PermanssonResearch/ReverseSolver/RectangularGameLaw.lean) | `rectangular_game_law_saddle` |
| [`PermanssonResearch/ReverseSolver/CommittedVsRectangularPathFixture.lean`](../../PermanssonResearch/ReverseSolver/CommittedVsRectangularPathFixture.lean) | `committed_vs_rectangular_separate_on_path_laws` |
| [`verification/research/tranche10_d05_scope_receipt_addendum.lean`](../../verification/research/tranche10_d05_scope_receipt_addendum.lean) | `rectangular_actual_minimum` |
| [`verification/research/tranche10_d05_scope_receipt_addendum.lean`](../../verification/research/tranche10_d05_scope_receipt_addendum.lean) | `committed_game_minimum` |
| [`PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean) | `solvePrivateStage_returns` |
| [`PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean) | `returned_isGreatest` |
| [`PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean) | `returned_value_attained` |
| [`PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageOptimizer.lean) | `returned_actual_strategic_value` |
| [`PermanssonResearch/ReverseSolver/PrivateControlStageFixture.lean`](../../PermanssonResearch/ReverseSolver/PrivateControlStageFixture.lean) | `timing_and_randomization_boundary` |
| [`PermanssonResearch/ReverseSolver/ResidenceContracts.lean`](../../PermanssonResearch/ReverseSolver/ResidenceContracts.lean) | `robust_quantifier_order_separation` |

## C23

**Discounted full-history verification and the X1 model**\
Paper label: `sec:C23` · Source ZIP member: `sections/C23.tex`.

**Proof role.** Discounted verification plus actual X1 calculations, regime obstructions and source interfaces.

**Scope boundary.** X1 DescriptorHasTwoValues fails on replete B; IsDescriptorNondegenerate holds from times 0/1 with true masses 1 and 13/20; invariance fails. These paper-derived predicate observations are not new compiled X1 declarations.

**Documentary predecessors.** [`docs/LANE_X1_COMMONS.md`](../LANE_X1_COMMONS.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/01_x1.md`](../../research/paper_closures/spec/chapters/01_x1.md); [`research/paper_closures/spec/chapters/02_strategies.md`](../../research/paper_closures/spec/chapters/02_strategies.md). These documents retain their original source/date scope.

**Retained obligations.** [X-01](RESIDUAL_STATUS.md#x-01).

**Manuscript review references.** `CTRL-07`, `CTRL-08` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Games/DiscountedVerification.lean`](../../PermanssonResearch/Games/DiscountedVerification.lean) | `infinite_performance_difference` |
| [`PermanssonResearch/Games/DiscountedVerification.lean`](../../PermanssonResearch/Games/DiscountedVerification.lean) | `discounted_verification` |
| [`PermanssonResearch/Games/DiscountedVerification.lean`](../../PermanssonResearch/Games/DiscountedVerification.lean) | `discounted_attainment` |
| [`PermanssonResearch/Games/DiscountedTraceExpectation.lean`](../../PermanssonResearch/Games/DiscountedTraceExpectation.lean) | `payoff_eq_expected_path_sum` |
| [`PermanssonResearch/StrategicWorld/InformationBoundary.lean`](../../PermanssonResearch/StrategicWorld/InformationBoundary.lean) | `actual_step_fair_matching` |
| [`PermanssonResearch/StrategicWorld/InformationBoundary.lean`](../../PermanssonResearch/StrategicWorld/InformationBoundary.lean) | `no_unobserved_draw_copy` |
| [`PermanssonResearch/X1/OccupationTargets.lean`](../../PermanssonResearch/X1/OccupationTargets.lean) | `transitionEntry_eq_numerical` |
| [`PermanssonResearch/X1/InterventionNumerics.lean`](../../PermanssonResearch/X1/InterventionNumerics.lean) | `elementaryUpdate_eq_updateL` |
| [`PermanssonResearch/X1/FullStrategyCertificate.lean`](../../PermanssonResearch/X1/FullStrategyCertificate.lean) | `exact_behavioral_performance_difference` |
| [`PermanssonResearch/X1/FullStrategyTrace.lean`](../../PermanssonResearch/X1/FullStrategyTrace.lean) | `expected_exact_behavioral_performance_difference` |
| [`PermanssonResearch/X1/StrategyOriginalBridge.lean`](../../PermanssonResearch/X1/StrategyOriginalBridge.lean) | `baseline_trace_stateLaw_eq_original` |
| [`PermanssonResearch/X1/ExactMargins.lean`](../../PermanssonResearch/X1/ExactMargins.lean) | `exactEffect_attainers` |
| [`PermanssonResearch/X1/ExactMargins.lean`](../../PermanssonResearch/X1/ExactMargins.lean) | `component_original_margin` |
| [`PermanssonResearch/X1/TiedStartDomainFixture.lean`](../../PermanssonResearch/X1/TiedStartDomainFixture.lean) | `omitted_domain_same_numeric_inf` |
| [`PermanssonResearch/X1/TiedStartDomainFixture.lean`](../../PermanssonResearch/X1/TiedStartDomainFixture.lean) | `omitted_domain_not_original` |
| [`PermanssonResearch/X1/OccupationTargets.lean`](../../PermanssonResearch/X1/OccupationTargets.lean) | `actual_poisson_identity` |
| [`PermanssonResearch/X1/OccupationTargets.lean`](../../PermanssonResearch/X1/OccupationTargets.lean) | `canonical_occupation_target_ae` |
| [`PermanssonResearch/X1/Comparison.lean`](../../PermanssonResearch/X1/Comparison.lean) | `replete_not_exactGR` |
| [`PermanssonLean/Regime/Assumption41.lean`](../../PermanssonLean/Regime/Assumption41.lean) | `DescriptorHasTwoValues` |
| [`PermanssonLean/Regime/Occupation.lean`](../../PermanssonLean/Regime/Occupation.lean) | `IsDescriptorNondegenerate` |

## C24

**Measurable multi-agent mechanisms, autonomy, clocks, and mediators**\
Paper label: `sec:C24` · Source ZIP member: `sections/C24.tex`.

**Proof role.** Measurable mechanism, autonomy, clock and mediator results under their exact information profiles.

**Scope boundary.** Strict anchors/common exogeneity, all-history model-specified rows including null histories, actual advancing clock, and whole marked laws must retain their precise separate profiles.

**Documentary predecessors.** [`docs/LANE_F1_MULTIAGENT_PROTOCOLS.md`](../LANE_F1_MULTIAGENT_PROTOCOLS.md); [`research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md`](../../research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md); [`research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md`](../../research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md); [`research/paper_closures/post_merge_102/NEXT05_FULL_MARGIN_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT05_FULL_MARGIN_V2_SCOPE.md). These documents retain their original source/date scope.

**Retained obligations.** [F-02](RESIDUAL_STATUS.md#f-02), [M-02](RESIDUAL_STATUS.md#m-02).

**Manuscript review references.** `CTRL-09`, `CTRL-10`, `CTRL-11` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/MultiAgent/MeasurableFiniteProduct.lean`](../../PermanssonResearch/MultiAgent/MeasurableFiniteProduct.lean) | `actual_transition` |
| [`PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean`](../../PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean) | `matched_closed_loop_all_initial_paths` |
| [`PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean`](../../PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean) | `matched_open_loop_all_initial_paths` |
| [`PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean`](../../PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean) | `matched_closed_loop_original_margin` |
| [`PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean`](../../PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean) | `matched_open_loop_original_margin` |
| [`PermanssonResearch/MultiAgent/AdaptationBound.lean`](../../PermanssonResearch/MultiAgent/AdaptationBound.lean) | `abs_closedLoop_sub_openLoop_le_adapt` |
| [`PermanssonResearch/MultiAgent/MeasurableProductProtocols.lean`](../../PermanssonResearch/MultiAgent/MeasurableProductProtocols.lean) | `original_margin_comparison` |
| [`PermanssonResearch/MultiAgent/BehavioralAutonomy.lean`](../../PermanssonResearch/MultiAgent/BehavioralAutonomy.lean) | `row_iff_all_histories` |
| [`PermanssonResearch/MultiAgent/BehavioralAutonomy.lean`](../../PermanssonResearch/MultiAgent/BehavioralAutonomy.lean) | `exists_row_iff_all_histories` |
| [`PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean`](../../PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean) | `strict_anchors_pathLaw_eq` |
| [`PermanssonResearch/MultiAgent/AutonomousAEMechanisms.lean`](../../PermanssonResearch/MultiAgent/AutonomousAEMechanisms.lean) | `ae_anchors_pathLaw_eq` |
| [`PermanssonResearch/MultiAgent/M02ActualMarkedHistoryFixture.lean`](../../PermanssonResearch/MultiAgent/M02ActualMarkedHistoryFixture.lean) | `actual_marked_diagonal_separation` |
| [`PermanssonResearch/MultiAgent/MarkedStrategicPathCountermodel.lean`](../../PermanssonResearch/MultiAgent/MarkedStrategicPathCountermodel.lean) | `original_strict_anchor_premise_rejected` |
| [`PermanssonResearch/MultiAgent/FeasibleAnchors.lean`](../../PermanssonResearch/MultiAgent/FeasibleAnchors.lean) | `keyLaw_feasible_iff` |
| [`PermanssonResearch/MultiAgent/FeasibleAnchors.lean`](../../PermanssonResearch/MultiAgent/FeasibleAnchors.lean) | `exists_feasible_keyKernel_iff` |
| [`PermanssonResearch/MultiAgent/FeasibleAnchors.lean`](../../PermanssonResearch/MultiAgent/FeasibleAnchors.lean) | `exists_feasible_strictAnchor_iff` |
| [`PermanssonResearch/MultiAgent/F03ActualInfeasibleAnchor.lean`](../../PermanssonResearch/MultiAgent/F03ActualInfeasibleAnchor.lean) | `all_pointwise_menus_nonempty_but_global_anchor_impossible` |
| [`PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean`](../../PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean) | `natural_scheduled_row` |
| [`PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean`](../../PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean) | `natural_projection` |
| [`PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean`](../../PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean) | `protocol_world_eq` |
| [`PermanssonResearch/MultiAgent/CorrelatedMediator.lean`](../../PermanssonResearch/MultiAgent/CorrelatedMediator.lean) | `mediator_mixture_eq` |
| [`PermanssonResearch/MultiAgent/CorrelatedMediator.lean`](../../PermanssonResearch/MultiAgent/CorrelatedMediator.lean) | `withMediatedActions_action` |

## C25

**Finite structural causal models and mediation identification**\
Paper label: `sec:C25` · Source ZIP member: `sections/C25.tex`.

**Proof role.** Finite structural causal identification results conditional on the declared structural model and support.

**Scope boundary.** Finite SCM identification requires the declared independent noise/positivity/information assumptions; no observation-only unrestricted causal identification or dynamic mediation follows.

**Documentary predecessors.** [`docs/LANE_F1_MULTIAGENT_PROTOCOLS.md`](../LANE_F1_MULTIAGENT_PROTOCOLS.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/03_autonomy.md`](../../research/paper_closures/spec/chapters/03_autonomy.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/MultiAgent/FiniteMediation.lean`](../../PermanssonResearch/MultiAgent/FiniteMediation.lean) | `mediation_identification_on_support` |
| [`PermanssonResearch/MultiAgent/FiniteMediation.lean`](../../PermanssonResearch/MultiAgent/FiniteMediation.lean) | `mediation_identification` |
| [`PermanssonResearch/MultiAgent/FiniteMediation.lean`](../../PermanssonResearch/MultiAgent/FiniteMediation.lean) | `signed_effect_decomposition` |
| [`PermanssonResearch/MultiAgent/PositiveMediationWitness.lean`](../../PermanssonResearch/MultiAgent/PositiveMediationWitness.lean) | `observationalMass_pos` |
| [`PermanssonResearch/MultiAgent/PositiveMediationWitness.lean`](../../PermanssonResearch/MultiAgent/PositiveMediationWitness.lean) | `identified_for_every_treatment` |
| [`PermanssonResearch/MultiAgent/PositiveMediationWitness.lean`](../../PermanssonResearch/MultiAgent/PositiveMediationWitness.lean) | `four_intervention_values` |
| [`PermanssonResearch/MultiAgent/FiniteMediation.lean`](../../PermanssonResearch/MultiAgent/FiniteMediation.lean) | `two_SCMs_same_observational_law` |
| [`PermanssonResearch/MultiAgent/FiniteMediation.lean`](../../PermanssonResearch/MultiAgent/FiniteMediation.lean) | `two_SCMs_different_joint_do` |
| [`PermanssonResearch/MultiAgent/FiniteMediation.lean`](../../PermanssonResearch/MultiAgent/FiniteMediation.lean) | `two_SCMs_positivity_failure` |

## C26

**Specialized finite algebra, detection and source rigidity**\
Paper label: `sec:C26` · Source ZIP member: `sections/C26.tex`.

**Proof role.** Conditional specialized finite algebra and source-rigidity arguments; analytic source identification retains its premises.

**Scope boundary.** Raw shell c requires normalization e=c/||c|| and b_e=b/||c||; scalar r=1 result is not arbitrary-shell matrix monotonicity; conditional finite algebra does not establish full analytic source identification.

**Documentary predecessors.** [`research/paper_closures/spec/chapters/09_specialized.md`](../../research/paper_closures/spec/chapters/09_specialized.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_112/acceptance_obligations_report.md`](../../research/paper_closures/post_merge_112/acceptance_obligations_report.md). These documents retain their original source/date scope.

**Retained obligations.** [E-05](RESIDUAL_STATUS.md#e-05).

**Manuscript review references.** `ROOT-06`, `ROOT-07`, `ROOT-09` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Specialized/SeamReduction.lean`](../../PermanssonResearch/Specialized/SeamReduction.lean) | `seam_rank_le_two` |
| [`PermanssonResearch/Specialized/SeamReduction.lean`](../../PermanssonResearch/Specialized/SeamReduction.lean) | `seam_constant_diagonal` |
| [`PermanssonResearch/Specialized/FiniteDetection.lean`](../../PermanssonResearch/Specialized/FiniteDetection.lean) | `exists_legal_negative_of_approximation` |
| [`PermanssonResearch/Specialized/ShellSchur.lean`](../../PermanssonResearch/Specialized/ShellSchur.lean) | `shell_equations_iff` |
| [`PermanssonResearch/Specialized/ShellResolvent.lean`](../../PermanssonResearch/Specialized/ShellResolvent.lean) | `scalarShellSecular_hasDerivAt` |
| [`PermanssonResearch/Specialized/SingularCompatibility.lean`](../../PermanssonResearch/Specialized/SingularCompatibility.lean) | `negative_resolvent_kernel_projection` |
| [`PermanssonResearch/Specialized/SingularCompatibility.lean`](../../PermanssonResearch/Specialized/SingularCompatibility.lean) | `denominator_free_kernel_rigidity` |
| [`PermanssonResearch/Specialized/GramSeparation.lean`](../../PermanssonResearch/Specialized/GramSeparation.lean) | `gram_operator_perturbation_negative` |
| [`PermanssonResearch/Specialized/E05FullGramMaskingCountermodel.lean`](../../PermanssonResearch/Specialized/E05FullGramMaskingCountermodel.lean) | `original_signed_negative_but_total_positive` |
| [`PermanssonResearch/Specialized/SeamReduction.lean`](../../PermanssonResearch/Specialized/SeamReduction.lean) | `constitutiveMargin_commonMode` |
| [`PermanssonResearch/Specialized/GramSeparation.lean`](../../PermanssonResearch/Specialized/GramSeparation.lean) | `constitutiveEffect_gram_witness` |
| [`PermanssonResearch/Specialized/FiniteDetection.lean`](../../PermanssonResearch/Specialized/FiniteDetection.lean) | `actual_effect_pos_of_legal_approximation` |

## C27

**Constructed examples and counterexamples**\
Paper label: `sec:C27` · Source ZIP member: `sections/C27.tex`.

**Proof role.** Constructed examples and counterexamples, not empirical validation.

**Scope boundary.** Each fixture is tied to actual primitives, comparison domain and expected obstruction; a similarly named example does not discharge a different historical acceptance requirement.

**Documentary predecessors.** [`docs/LANE_C4_SIX_STATE_PRECISION.md`](../LANE_C4_SIX_STATE_PRECISION.md); [`docs/LANE_C5_SHARP_FAMILY.md`](../LANE_C5_SHARP_FAMILY.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md`](../../research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md). These documents retain their original source/date scope.

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/Examples/PeriodicExactGR.lean`](../../PermanssonLean/Examples/PeriodicExactGR.lean) | `proposition_8_1` |
| [`PermanssonLean/Examples/FactorizationCounterexample.lean`](../../PermanssonLean/Examples/FactorizationCounterexample.lean) | `factorization_nonidentification` |
| [`PermanssonLean/Examples/ConstitutiveNoninvariance.lean`](../../PermanssonLean/Examples/ConstitutiveNoninvariance.lean) | `witnessConvergenceMode` |
| [`PermanssonLean/Examples/QSDCounterexample.lean`](../../PermanssonLean/Examples/QSDCounterexample.lean) | `not_uniformly_finitePersistent` |
| [`PermanssonResearch/EconomicWitness/Model.lean`](../../PermanssonResearch/EconomicWitness/Model.lean) | `model` |
| [`PermanssonResearch/EconomicWitness/Incentives.lean`](../../PermanssonResearch/EconomicWitness/Incentives.lean) | `expected_behavioral_optimality` |
| [`PermanssonResearch/EconomicWitness/ExactRegime.lean`](../../PermanssonResearch/EconomicWitness/ExactRegime.lean) | `original_confirmatoryGR` |
| [`PermanssonResearch/EconomicWitness/Constitution.lean`](../../PermanssonResearch/EconomicWitness/Constitution.lean) | `original_grounded_confirmatory_uniformPR` |
| [`PermanssonResearch/EconomicWitness/Regression.lean`](../../PermanssonResearch/EconomicWitness/Regression.lean) | `baseline_leak_not_original_exactGR` |

## C28

**Measurement, earlier applications, and confirmatory inference**\
Paper label: `sec:C28` · Source ZIP member: `sections/C28.tex`.

**Proof role.** Measurement definitions, conditional inference propositions and historical application interpretation.

**Scope boundary.** Nonempty random uncertainty set, alpha in [0,1], measurable coverage event and actual joint coverage are premises; descriptive/constructed applications do not become empirical regime certificates.

**Documentary predecessors.** [`application/APPLICATION_STANDARD.md`](../../application/APPLICATION_STANDARD.md); [`docs/APPLICATION_BOUNDARY.md`](../APPLICATION_BOUNDARY.md); [`research/paper_closures/spec/chapters/08_grammar_economic.md`](../../research/paper_closures/spec/chapters/08_grammar_economic.md). These documents retain their original source/date scope.

**Manuscript review references.** `ROOT-02`, `ROOT-03`, `ROOT-10`, `ROOT-11`, `ROOT-12`, `ROOT-14` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## C29

**Exact algorithms, reflection, and executable evidence**\
Paper label: `sec:C29` · Source ZIP member: `sections/C29.tex`.

**Proof role.** Exact algorithms, reflection and executable evidence with explicit producer/checker/proof roles.

**Scope boundary.** Executable calculations, reflection, generated Lean, transitive axiom checks and independent acceptance are distinct evidence types.

**Documentary predecessors.** [`docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`](../LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md); [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](../LANE_C11_CLASS_STATIONARY_CERTIFICATION.md); [`research/paper_closures/ACCEPTANCE_EVIDENCE_GUIDE.md`](../../research/paper_closures/ACCEPTANCE_EVIDENCE_GUIDE.md). These documents retain their original source/date scope.

**Manuscript review references.** `ROOT-01` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`apps/permansson/application-successor/src/permansson_app/data/capabilities.json`](../../apps/permansson/application-successor/src/permansson_app/data/capabilities.json) | `exact_profiles` |
| [`apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md`](../../apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md) | `successor-finite-numeric.v1` |
| [`apps/permansson/closure-successor/cli.py`](../../apps/permansson/closure-successor/cli.py) | `replay` |
| [`apps/permansson/closure-successor-c11/cli.py`](../../apps/permansson/closure-successor-c11/cli.py) | `replay` |
| [`verification/research/c10_emit_golden_bridge.py`](../../verification/research/c10_emit_golden_bridge.py) | `emit_golden_bridge` |
| [`verification/research/c11_emit_stationary_lean.py`](../../verification/research/c11_emit_stationary_lean.py) | `emit_source` |

## C30

**Formalization, reproducibility, and source concordance**\
Paper label: `sec:C30` · Source ZIP member: `sections/C30.tex`.

**Proof role.** Source inventory, reproducibility and evidence conventions; no new theorem-certification decision.

**Scope boundary.** 798 files (64 core+710 research+24 other),7690 lexical units group-mapped; structural source-label presence and coverage are not individual semantic certification or a fresh full Lean build.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/RESEARCH_BUILD.md`](../RESEARCH_BUILD.md); [`docs/V020_IMPLEMENTATION_INDEX.md`](../V020_IMPLEMENTATION_INDEX.md); [`docs/V020_RESEARCH_PROOF_LEDGER.md`](../V020_RESEARCH_PROOF_LEDGER.md); [`docs/V020_HARDENING.md`](../V020_HARDENING.md); [`research/paper_closures/README.md`](../../research/paper_closures/README.md). These documents retain their original source/date scope.

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## C31

**Limitations, corrected claims, and further mathematical questions**\
Paper label: `sec:C31` · Source ZIP member: `sections/C31.tex`.

**Proof role.** Limitations and extension criteria, including unresolved semantic reconciliation.

**Scope boundary.** Track seven stronger/separately evidenced Appendix P obligations, broader conditional-profile limits, and independent acceptance separately; no source-presence-to-accepted inference.

**Documentary predecessors.** [`docs/FUTURE_THEORY_ROADMAP.md`](../FUTURE_THEORY_ROADMAP.md); [`docs/PERMANSSON_RESEARCH_ARCHITECTURE.md`](../PERMANSSON_RESEARCH_ARCHITECTURE.md); [`docs/PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md`](../PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md); [`research/paper_closures/post_merge_112/acceptance_obligations_report.md`](../../research/paper_closures/post_merge_112/acceptance_obligations_report.md). These documents retain their original source/date scope.

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## Appendix A

**Measurable and probabilistic conventions**\
Paper label: `app:A` · Source ZIP member: `appendices/A_foundations.tex`.

**Proof role.** Detailed measurable and probabilistic conventions and supporting proofs.

**Scope boundary.** State the actual measurable/Borel/nonempty and metric profiles; empirical weak limits, W1 limits, deterministic limits and laws of random limits remain distinct.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/CQ1_FINITE_PATH_BRIDGE.md`](../CQ1_FINITE_PATH_BRIDGE.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-012` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/Regime/PolishDescriptor.lean`](../../PermanssonLean/Regime/PolishDescriptor.lean) | `boundedCompatibleMetric` |
| [`PermanssonLean/Regime/PolishDescriptor.lean`](../../PermanssonLean/Regime/PolishDescriptor.lean) | `hasBoundedLipschitzWeakCriterion` |
| [`PermanssonLean/Regime/PolishDescriptor.lean`](../../PermanssonLean/Regime/PolishDescriptor.lean) | `Proposition41aCertificate` |
| [`PermanssonLean/Regime/PolishDescriptor.lean`](../../PermanssonLean/Regime/PolishDescriptor.lean) | `natDiracProba_not_tight` |
| [`PermanssonLean/Regime/PolishDescriptor.lean`](../../PermanssonLean/Regime/PolishDescriptor.lean) | `natDiracProba_no_weak_limit` |
| [`PermanssonResearch/Probability/A01SupnormClassCountermodel.lean`](../../PermanssonResearch/Probability/A01SupnormClassCountermodel.lean) | `legitimate_bounded_lipschitz_witness_not_unit_supnorm` |
| [`PermanssonResearch/MultipleLimit/CountableEmpiricalWeak.lean`](../../PermanssonResearch/MultipleLimit/CountableEmpiricalWeak.lean) | `weak_of_all_bounded_averages` |
| [`PermanssonResearch/MultipleLimit/CanonicalInitialDensity.lean`](../../PermanssonResearch/MultipleLimit/CanonicalInitialDensity.lean) | `pathLaw_eq_withDensity` |
| [`PermanssonResearch/RegimeExit/RandomEntryOccupation.lean`](../../PermanssonResearch/RegimeExit/RandomEntryOccupation.lean) | `pathLaw_eq_bind` |

## Appendix B

**Earlier-paper lineage and mathematical reconciliation**\
Paper label: `app:B` · Source ZIP member: `appendices/B_lineage.tex`.

**Proof role.** Earlier-paper lineage and mathematical profile reconciliation.

**Scope boundary.** Earlier-paper lineage is preserved; manuscript v2.0.1, formal release v0.2.0 and mathematical guide v1.1.1 are different artifacts. Original equilibrium predecessor is reconciled by the actual product embedding including both reference-mass and nonempty-interior branches. Raw shell c requires normalization e=c/||c|| and b_e=b/||c||; scalar r=1 result is not arbitrary-shell matrix monotonicity; conditional finite algebra does not establish full analytic source identification. Nonempty random uncertainty set, alpha in [0,1], measurable coverage event and actual joint coverage are premises; descriptive/constructed applications do not become empirical regime certificates.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/PERMANSSON_RESEARCH_ARCHITECTURE.md`](../PERMANSSON_RESEARCH_ARCHITECTURE.md); [`docs/FUTURE_THEORY_ROADMAP.md`](../FUTURE_THEORY_ROADMAP.md); [`research/paper_closures/spec/chapters/09_specialized.md`](../../research/paper_closures/spec/chapters/09_specialized.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_112/acceptance_obligations_report.md`](../../research/paper_closures/post_merge_112/acceptance_obligations_report.md); [`application/APPLICATION_STANDARD.md`](../../application/APPLICATION_STANDARD.md); [`docs/APPLICATION_BOUNDARY.md`](../APPLICATION_BOUNDARY.md); [`research/paper_closures/spec/chapters/08_grammar_economic.md`](../../research/paper_closures/spec/chapters/08_grammar_economic.md). These documents retain their original source/date scope.

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## Appendix C

**Canonical dynamics, original predicates and EGR derivations**\
Paper label: `app:C` · Source ZIP member: `appendices/C_foundations.tex`.

**Proof role.** Proof details for canonical dynamics, original predicates and EGR transport.

**Scope boundary.** Chronology is alpha then physical P then update U; original canonical laws and fixed physical-world intervention semantics are retained. Original Exact GR requires all-state invariance and original nontriviality; finite retention and QSD statements have separate hypotheses. Keep measurable grounding maps, original comparison-set requirements, and the paper coordinate-change proof distinct from same-space formal endpoints. Original equilibrium predecessor is reconciled by the actual product embedding including both reference-mass and nonempty-interior branches.

**Documentary predecessors.** [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/LANE_C_ABSORBING_REGIME_FAMILIES.md`](../LANE_C_ABSORBING_REGIME_FAMILIES.md); [`docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md`](../LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-008` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonLean/StrategicWorld/InducedKernel.lean`](../../PermanssonLean/StrategicWorld/InducedKernel.lean) | `inducedKernel_apply` |
| [`PermanssonLean/StrategicWorld/WellPosedness.lean`](../../PermanssonLean/StrategicWorld/WellPosedness.lean) | `pathLaw_existsUnique` |
| [`PermanssonResearch/Probability/CompProdPushforward.lean`](../../PermanssonResearch/Probability/CompProdPushforward.lean) | `compProd_map_left_eq_map_compProd_comap` |
| [`PermanssonResearch/StrategicWorld/DeterministicOrbit.lean`](../../PermanssonResearch/StrategicWorld/DeterministicOrbit.lean) | `pathLaw_dirac_of_deterministic` |
| [`PermanssonResearch/StrategicWorld/InformationBoundary.lean`](../../PermanssonResearch/StrategicWorld/InformationBoundary.lean) | `actual_step_fair_matching` |
| [`PermanssonResearch/StrategicWorld/InformationBoundary.lean`](../../PermanssonResearch/StrategicWorld/InformationBoundary.lean) | `no_unobserved_draw_copy` |
| [`PermanssonLean/Regime/ExitTimeExpectation.lean`](../../PermanssonLean/Regime/ExitTimeExpectation.lean) | `expectedExitTime_eq_greenSeries` |
| [`PermanssonLean/Regime/Persistence.lean`](../../PermanssonLean/Regime/Persistence.lean) | `finitePersistence_iff_killed` |
| [`PermanssonLean/Regime/Persistence.lean`](../../PermanssonLean/Regime/Persistence.lean) | `oneStepRetention_pow_lowerBound` |
| [`PermanssonLean/Regime/RepresentationEquivalence.lean`](../../PermanssonLean/Regime/RepresentationEquivalence.lean) | `exactGR_iff_of_inducedKernel_eq` |
| [`PermanssonLean/Regime/GroundedRepresentationEquivalence.lean`](../../PermanssonLean/Regime/GroundedRepresentationEquivalence.lean) | `groundedPropertyRelative_iff_of_kernel_eq` |
| [`PermanssonLean/Regime/FamilyEquivalence.lean`](../../PermanssonLean/Regime/FamilyEquivalence.lean) | `hasConstitutiveWitness_iff_of_familyEquivalence` |
| [`PermanssonLean/Regime/FamilyEquivalence.lean`](../../PermanssonLean/Regime/FamilyEquivalence.lean) | `noConstitutiveWitness_iff_of_familyEquivalence` |
| [`PermanssonLean/Regime/GroundedFamilyEquivalence.lean`](../../PermanssonLean/Regime/GroundedFamilyEquivalence.lean) | `groundedFrozenFamilyUniformPR_iff_of_signature_match` |
| [`PermanssonLean/Regime/Perturbation.lean`](../../PermanssonLean/Regime/Perturbation.lean) | `constitutiveEffect_perturbation_abs_le` |
| [`PermanssonLean/Regime/Perturbation.lean`](../../PermanssonLean/Regime/Perturbation.lean) | `constitutiveMargin_perturbation_abs_le` |
| [`PermanssonLean/Regime/Perturbation.lean`](../../PermanssonLean/Regime/Perturbation.lean) | `robustUniformConstitution` |

## Appendix D

**Finite occupation proofs and exact absorbing and recurrent witnesses**\
Paper label: `app:D` · Source ZIP member: `appendices/D_occupation.tex`.

**Proof role.** Finite occupation proofs and exact absorbing/recurrent examples.

**Scope boundary.** Random class-dependent joint-state occupations are not replaced by their barycenter; descriptor pushforwards can agree while joint-state limits differ. Property-specific PR and exact finite GR have different gates; deterministic descriptor target does not remove original nontriviality or invariance.

**Documentary predecessors.** [`docs/LANE_C_RECURRENT_CLASSES.md`](../LANE_C_RECURRENT_CLASSES.md); [`docs/LANE_C_ABSORBING_REGIME_FAMILIES.md`](../LANE_C_ABSORBING_REGIME_FAMILIES.md); [`docs/LANE_C4_SIX_STATE_PRECISION.md`](../LANE_C4_SIX_STATE_PRECISION.md); [`docs/LANE_C5_SHARP_FAMILY.md`](../LANE_C5_SHARP_FAMILY.md); [`docs/LANE_C_EXACT_GR_CHARACTERIZATION.md`](../LANE_C_EXACT_GR_CHARACTERIZATION.md); [`docs/LANE_C6_TYPED_OBSERVED_RESPONSE.md`](../LANE_C6_TYPED_OBSERVED_RESPONSE.md); [`docs/LANE_C7_FINITE_EVENT_RESPONSE.md`](../LANE_C7_FINITE_EVENT_RESPONSE.md); [`docs/LANE_C8_SUPPORT_GRAPH_CONSTITUTION.md`](../LANE_C8_SUPPORT_GRAPH_CONSTITUTION.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-003`, `FND-007`, `FND-009`, `FND-013`, `ROOT-17` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/MultipleLimit/FiniteMarkovMartingaleOrthogonality.lean`](../../PermanssonResearch/MultipleLimit/FiniteMarkovMartingaleOrthogonality.lean) | `increment_pairwise_orthogonal` |
| [`PermanssonResearch/MultipleLimit/FiniteMarkovMartingaleVariance.lean`](../../PermanssonResearch/MultipleLimit/FiniteMarkovMartingaleVariance.lean) | `canonical_martingale_second_moment_le_time` |
| [`PermanssonResearch/MultipleLimit/FiniteMarkovMartingaleSquareLaw.lean`](../../PermanssonResearch/MultipleLimit/FiniteMarkovMartingaleSquareLaw.lean) | `square_normalized_ae_tendsto_zero` |
| [`PermanssonResearch/MultipleLimit/FiniteMarkovInterpolation.lean`](../../PermanssonResearch/MultipleLimit/FiniteMarkovInterpolation.lean) | `partialSum_time_lipschitz` |
| [`PermanssonResearch/MultipleLimit/FiniteOccupationTelescoping.lean`](../../PermanssonResearch/MultipleLimit/FiniteOccupationTelescoping.lean) | `occupationDrift_telescope` |
| [`PermanssonResearch/MultipleLimit/FiniteOccupationLimitFromResidual.lean`](../../PermanssonResearch/MultipleLimit/FiniteOccupationLimitFromResidual.lean) | `tendsto_unique_stationary_of_residual` |
| [`PermanssonResearch/MultipleLimit/FiniteOccupationMeasureBridge.lean`](../../PermanssonResearch/MultipleLimit/FiniteOccupationMeasureBridge.lean) | `canonical_physical_occupation_ae_limit` |
| [`PermanssonResearch/MultipleLimit/AbsorbingFamily.lean`](../../PermanssonResearch/MultipleLimit/AbsorbingFamily.lean) | `HasAlmostSureAbsorption` |
| [`PermanssonResearch/MultipleLimit/KernelBlockSurvival.lean`](../../PermanssonResearch/MultipleLimit/KernelBlockSurvival.lean) | `geometric_endpoint_power_of_absorbing_block` |
| [`PermanssonResearch/MultipleLimit/TypedAlmostSureAbsorption.lean`](../../PermanssonResearch/MultipleLimit/TypedAlmostSureAbsorption.lean) | `canonical_almostSureAbsorption` |
| [`PermanssonResearch/MultipleLimit/TypedStrategicWitness.lean`](../../PermanssonResearch/MultipleLimit/TypedStrategicWitness.lean) | `inducedKernel_atom_entry` |
| [`PermanssonResearch/MultipleLimit/TypedStrategicWitness.lean`](../../PermanssonResearch/MultipleLimit/TypedStrategicWitness.lean) | `inducedKernel_eq_rational_transport` |
| [`PermanssonResearch/MultipleLimit/ExactRationalAbsorption.lean`](../../PermanssonResearch/MultipleLimit/ExactRationalAbsorption.lean) | `hitting_u_closed` |
| [`PermanssonResearch/MultipleLimit/ExactRationalAbsorption.lean`](../../PermanssonResearch/MultipleLimit/ExactRationalAbsorption.lean) | `hitting_t_closed` |
| [`PermanssonResearch/MultipleLimit/TypedRandomLimitDistribution.lean`](../../PermanssonResearch/MultipleLimit/TypedRandomLimitDistribution.lean) | `complete_random_limit_law_closed` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateFullRandomLaw.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateFullRandomLaw.lean) | `full_random_occupation_law_u` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateFullRandomLaw.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateFullRandomLaw.lean) | `full_random_occupation_law_t` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateObservedGR.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateObservedGR.lean) | `observedExactGeneratedRegime` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateC3Witness.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateC3Witness.lean) | `identity_no_exactGR_for_any_target` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateMarginalOscillation.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateMarginalOscillation.lean) | `a0_empirical_converges_piA` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateQuotient.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateQuotient.lean) | `class_quotient_exact` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateUnreachable.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateUnreachable.lean) | `A_cannot_reach_B` |
| [`PermanssonResearch/MultipleLimit/FiniteBasinClassification.lean`](../../PermanssonResearch/MultipleLimit/FiniteBasinClassification.lean) | `unreachable_class_mass_zero` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateTargetDisruption.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateTargetDisruption.lean) | `intervention_world_fixed` |
| [`PermanssonResearch/MultipleLimit/SharpFamilyResponseWitness.lean`](../../PermanssonResearch/MultipleLimit/SharpFamilyResponseWitness.lean) | `disrupted_sharp_eq_false` |
| [`PermanssonResearch/MultipleLimit/ExactSixStateC8SupportWitness.lean`](../../PermanssonResearch/MultipleLimit/ExactSixStateC8SupportWitness.lean) | `same_intervened_positive_support` |
| [`PermanssonResearch/MultipleLimit/FiniteSupportCounterexamples.lean`](../../PermanssonResearch/MultipleLimit/FiniteSupportCounterexamples.lean) | `support_equal_but_actual_kernels_distinct` |
| [`PermanssonResearch/MultipleLimit/GroundedC6Response.lean`](../../PermanssonResearch/MultipleLimit/GroundedC6Response.lean) | `frozen_event_factors` |
| [`PermanssonResearch/MultipleLimit/GroundedC6Response.lean`](../../PermanssonResearch/MultipleLimit/GroundedC6Response.lean) | `groundedRelativePR` |
| [`PermanssonResearch/MultipleLimit/RecurrentCounterexamples.lean`](../../PermanssonResearch/MultipleLimit/RecurrentCounterexamples.lean) | `no_original_assumption41_of_subsingleton` |
| [`PermanssonResearch/MultipleLimit/Counterexamples.lean`](../../PermanssonResearch/MultipleLimit/Counterexamples.lean) | `no_universal_terminal_limit` |

## Appendix E

**Ergodic, regenerative and nonfinite proof details**\
Paper label: `app:E` · Source ZIP member: `appendices/E_ergodic.tex`.

**Proof role.** Ergodic, regenerative and nonfinite arguments under their respective hypotheses.

**Scope boundary.** Stationary random-limit, compact Feller, initial-AC, and regenerative all-initial profiles have different premises; general L1 paper result exceeds one constant-approximant formal endpoint. Restart uses actual full-future laws and correct same-T empirical comparison; exit, entry, retention and constitutive switching remain separate events.

**Documentary predecessors.** [`research/paper_closures/README.md`](../../research/paper_closures/README.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/05_long_run.md`](../../research/paper_closures/spec/chapters/05_long_run.md); [`docs/LANE_C_EXIT_ROUTING.md`](../LANE_C_EXIT_ROUTING.md); [`docs/LANE_C_EXIT_SWITCHING.md`](../LANE_C_EXIT_SWITCHING.md); [`docs/LANE_C_EXIT_RESTART.md`](../LANE_C_EXIT_RESTART.md); [`docs/LANE_C_EXIT_RANDOM_ENTRY.md`](../LANE_C_EXIT_RANDOM_ENTRY.md). These documents retain their original source/date scope.

**Manuscript review references.** `FND-004`, `FND-006` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Probability/HopfMaximal.lean`](../../PermanssonResearch/Probability/HopfMaximal.lean) | `finite_maximal_integral_nonneg` |
| [`PermanssonResearch/Probability/HopfMaximal.lean`](../../PermanssonResearch/Probability/HopfMaximal.lean) | `integral_nonneg_of_positive_partial_sums` |
| [`PermanssonResearch/Probability/L1Maximal.lean`](../../PermanssonResearch/Probability/L1Maximal.lean) | `maximalEvent_measure_bound` |
| [`PermanssonResearch/Probability/BoundedOrbitAverages.lean`](../../PermanssonResearch/Probability/BoundedOrbitAverages.lean) | `upperAverage_invariant` |
| [`PermanssonResearch/Probability/BoundedBirkhoff.lean`](../../PermanssonResearch/Probability/BoundedBirkhoff.lean) | `bounded_birkhoff` |
| [`PermanssonResearch/Probability/BoundedBirkhoffConditional.lean`](../../PermanssonResearch/Probability/BoundedBirkhoffConditional.lean) | `bounded_birkhoff_condExp` |
| [`PermanssonResearch/Probability/BoundedBirkhoffRegression.lean`](../../PermanssonResearch/Probability/BoundedBirkhoffRegression.lean) | `identity_limits_distinct` |
| [`PermanssonResearch/Probability/BoundedBirkhoffRegression.lean`](../../PermanssonResearch/Probability/BoundedBirkhoffRegression.lean) | `reset_conditional_time_average` |
| [`PermanssonResearch/Probability/L1Truncation.lean`](../../PermanssonResearch/Probability/L1Truncation.lean) | `positiveTruncation_L1` |
| [`PermanssonResearch/Probability/L1AverageApproximation.lean`](../../PermanssonResearch/Probability/L1AverageApproximation.lean) | `ae_average_limit_of_L1_approximation` |
| [`PermanssonResearch/Probability/BoundedInnovations.lean`](../../PermanssonResearch/Probability/BoundedInnovations.lean) | `ae_strong_law` |
| [`PermanssonResearch/Probability/StandardBorelKernelEquality.lean`](../../PermanssonResearch/Probability/StandardBorelKernelEquality.lean) | `kernel_ae_eq_of_determining` |
| [`PermanssonResearch/MultipleLimit/StationaryConditionalInvariant.lean`](../../PermanssonResearch/MultipleLimit/StationaryConditionalInvariant.lean) | `randomLaw_invariant_ae` |
| [`verification/research/StationaryRandomWitness.lean`](../../verification/research/StationaryRandomWitness.lean) | `identity_randomLaw` |
| [`verification/research/CompactFellerWitness.lean`](../../verification/research/CompactFellerWitness.lean) | `reset_comp` |
| [`PermanssonResearch/Probability/RegenerativeOperator.lean`](../../PermanssonResearch/Probability/RegenerativeOperator.lean) | `resolvent_equation` |
| [`PermanssonResearch/Probability/RegenerativePoisson.lean`](../../PermanssonResearch/Probability/RegenerativePoisson.lean) | `poisson_equation` |
| [`PermanssonResearch/MultipleLimit/RegenerativeAverages.lean`](../../PermanssonResearch/MultipleLimit/RegenerativeAverages.lean) | `canonical_regenerative_averages` |
| [`PermanssonResearch/Probability/RegenerativeRenewalMass.lean`](../../PermanssonResearch/Probability/RegenerativeRenewalMass.lean) | `orbit_tv_le_pow` |
| [`PermanssonResearch/MultipleLimit/RegenerativeInitialTransfer.lean`](../../PermanssonResearch/MultipleLimit/RegenerativeInitialTransfer.lean) | `ae_shiftInvariant_transfer` |
| [`PermanssonResearch/MultipleLimit/RegenerativeDescriptorTails.lean`](../../PermanssonResearch/MultipleLimit/RegenerativeDescriptorTails.lean) | `canonical_excess_tail_uniform` |
| [`PermanssonResearch/Probability/RegenerativeMomentRegression.lean`](../../PermanssonResearch/Probability/RegenerativeMomentRegression.lean) | `invariant_unbounded_support` |
| [`PermanssonResearch/Probability/RegenerativeMomentRegression.lean`](../../PermanssonResearch/Probability/RegenerativeMomentRegression.lean) | `all_initial_actual_empirical_W1` |
| [`PermanssonResearch/Probability/RegenerativeRegression.lean`](../../PermanssonResearch/Probability/RegenerativeRegression.lean) | `halfReset_all_bounded_measurable_averages` |
| [`PermanssonResearch/Probability/RegenerativeRegression.lean`](../../PermanssonResearch/Probability/RegenerativeRegression.lean) | `false_reset_decomposition_rejected` |
| [`PermanssonResearch/MultipleLimit/GrowingBlockAverages.lean`](../../PermanssonResearch/MultipleLimit/GrowingBlockAverages.lean) | `last_block_error` |
| [`PermanssonResearch/MultipleLimit/GrowingBlockAverages.lean`](../../PermanssonResearch/MultipleLimit/GrowingBlockAverages.lean) | `averages_do_not_converge` |
| [`PermanssonResearch/MultipleLimit/GrowingBlockCounterexample.lean`](../../PermanssonResearch/MultipleLimit/GrowingBlockCounterexample.lean) | `canonical_growing_block_occupations_fail` |
| [`PermanssonResearch/MultipleLimit/NonfiniteClock.lean`](../../PermanssonResearch/MultipleLimit/NonfiniteClock.lean) | `canonical_clock_no_weak_limit` |

## Appendix F

**Grammar proofs and finite-certificate details**\
Paper label: `app:F` · Source ZIP member: `appendices/F_grammar.tex`.

**Proof role.** Grammar and finite-certificate derivations and counterexamples.

**Scope boundary.** Least-positive requires positivity and lower-bound inclusion; minimality transport needs actual strict lower-set coverage, and inverse-image strictness needs nonempty fibres. Separate primitive additive and common-mass product routes; formal finite-prefix interface also requests the joint-state (Y,Y) common-kernel instance.

**Documentary predecessors.** [`docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md`](../LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md); [`docs/LANE_B2_SEQUENTIAL_EFFECTS.md`](../LANE_B2_SEQUENTIAL_EFFECTS.md); [`research/paper_closures/post_merge_79/NEXT06_B01_OVERLAP.md`](../../research/paper_closures/post_merge_79/NEXT06_B01_OVERLAP.md); [`research/paper_closures/spec/chapters/08_grammar_economic.md`](../../research/paper_closures/spec/chapters/08_grammar_economic.md); [`docs/CQ1_FINITE_PATH_BRIDGE.md`](../CQ1_FINITE_PATH_BRIDGE.md); [`docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md`](../CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md); [`docs/CQ1_CERTIFICATE_TRANSPORT.md`](../CQ1_CERTIFICATE_TRANSPORT.md); [`docs/LANE_A2_PRIMITIVE_TV.md`](../LANE_A2_PRIMITIVE_TV.md); [`research/paper_closures/spec/chapters/04_robustness.md`](../../research/paper_closures/spec/chapters/04_robustness.md). These documents retain their original source/date scope.

**Manuscript review references.** `Q11`, `Q12` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/GrammarRobust/AtomicLocality.lean`](../../PermanssonResearch/GrammarRobust/AtomicLocality.lean) | `patchedAction_unaffected` |
| [`PermanssonResearch/GrammarRobust/BlockModels.lean`](../../PermanssonResearch/GrammarRobust/BlockModels.lean) | `blockModel_eq_of_expand_eq` |
| [`PermanssonResearch/GrammarRobust/OriginalInterventionBridge.lean`](../../PermanssonResearch/GrammarRobust/OriginalInterventionBridge.lean) | `admittedBlockIntervention_apply` |
| [`PermanssonLean/Regime/Occupation.lean`](../../PermanssonLean/Regime/Occupation.lean) | `IsDescriptorNondegenerate` |
| [`PermanssonResearch/GrammarRobust/BooleanOccupation.lean`](../../PermanssonResearch/GrammarRobust/BooleanOccupation.lean) | `exactGR` |
| [`PermanssonResearch/GrammarRobust/BooleanPersistence.lean`](../../PermanssonResearch/GrammarRobust/BooleanPersistence.lean) | `uniformRelativePR` |
| [`PermanssonResearch/GrammarRobust/BooleanOneStepEvents.lean`](../../PermanssonResearch/GrammarRobust/BooleanOneStepEvents.lean) | `or_pathlaw_table` |
| [`PermanssonResearch/GrammarRobust/BooleanOneStepEvents.lean`](../../PermanssonResearch/GrammarRobust/BooleanOneStepEvents.lean) | `and_pathlaw_table` |
| [`PermanssonResearch/GrammarRobust/BooleanOneStepEvents.lean`](../../PermanssonResearch/GrammarRobust/BooleanOneStepEvents.lean) | `xor_pathlaw_table` |
| [`PermanssonResearch/GrammarRobust/JointOnlyCertifiedFixture.lean`](../../PermanssonResearch/GrammarRobust/JointOnlyCertifiedFixture.lean) | `original_or_joint_only` |
| [`PermanssonResearch/GrammarRobust/BooleanMinimalityCases.lean`](../../PermanssonResearch/GrammarRobust/BooleanMinimalityCases.lean) | `B7_minimality_not_preserved_by_refinement` |
| [`PermanssonResearch/GrammarRobust/BooleanMinimalityCases.lean`](../../PermanssonResearch/GrammarRobust/BooleanMinimalityCases.lean) | `B8_coarse_hides_positive_fine_singleton` |
| [`PermanssonResearch/GrammarRobust/SequentialAdversaries.lean`](../../PermanssonResearch/GrammarRobust/SequentialAdversaries.lean) | `zeroInf_strong_false_promotion` |
| [`PermanssonResearch/GrammarRobust/SequentialAdversaries.lean`](../../PermanssonResearch/GrammarRobust/SequentialAdversaries.lean) | `vector_interaction_not_scalar_distance` |
| [`PermanssonResearch/GrammarRobust/SequentialAdversaries.lean`](../../PermanssonResearch/GrammarRobust/SequentialAdversaries.lean) | `vector_conditional_legs_unequal` |
| [`PermanssonResearch/GrammarRobust/AdversarialAdmission.lean`](../../PermanssonResearch/GrammarRobust/AdversarialAdmission.lean) | `forbidden_block_has_no_certificate` |
| [`PermanssonResearch/GrammarRobust/B02LocalOriginalMarginClosure.lean`](../../PermanssonResearch/GrammarRobust/B02LocalOriginalMarginClosure.lean) | `fullOrEmptyFine_rejects_singleton_zero` |
| [`PermanssonResearch/ReverseSolver/AdaptiveGrammarAdmissionFixture.lean`](../../PermanssonResearch/ReverseSolver/AdaptiveGrammarAdmissionFixture.lean) | `restrictedCertifiedMenu` |
| [`PermanssonResearch/GrammarRobust/InvalidBijectionWitness.lean`](../../PermanssonResearch/GrammarRobust/InvalidBijectionWitness.lean) | `AND_margin_invariant_under_invalid_swap` |
| [`PermanssonResearch/GrammarRobust/InvalidBijectionWitness.lean`](../../PermanssonResearch/GrammarRobust/InvalidBijectionWitness.lean) | `invalid_swap_does_not_preserve_proper_inclusion` |
| [`PermanssonResearch/GrammarRobust/AlternativeBankWitness.lean`](../../PermanssonResearch/GrammarRobust/AlternativeBankWitness.lean) | `B4_distinct_frozen_constitutive_margins` |
| [`PermanssonResearch/GrammarRobust/BooleanOverlapFixture.lean`](../../PermanssonResearch/GrammarRobust/BooleanOverlapFixture.lean) | `compatible_order_independent` |
| [`PermanssonResearch/GrammarRobust/BooleanOverlapFixture.lean`](../../PermanssonResearch/GrammarRobust/BooleanOverlapFixture.lean) | `incompatible_order_changes_actual_kernel` |
| [`PermanssonResearch/GrammarRobust/AdversarialAdmission.lean`](../../PermanssonResearch/GrammarRobust/AdversarialAdmission.lean) | `overlapping_action_rows_rejected` |
| [`PermanssonResearch/GrammarRobust/LocalOrderPositiveFixture.lean`](../../PermanssonResearch/GrammarRobust/LocalOrderPositiveFixture.lean) | `local_minimality_without_global_isomorphism` |
| [`PermanssonResearch/GrammarRobust/B02LocalOriginalMarginClosure.lean`](../../PermanssonResearch/GrammarRobust/B02LocalOriginalMarginClosure.lean) | `original_local_minimality_without_global_isomorphism` |
| [`PermanssonResearch/ConstitutiveQuasi/ComparisonTransport.lean`](../../PermanssonResearch/ConstitutiveQuasi/ComparisonTransport.lean) | `transportComparisonSet` |
| [`PermanssonResearch/ConstitutiveQuasi/PersistencePromotion.lean`](../../PermanssonResearch/ConstitutiveQuasi/PersistencePromotion.lean) | `clampedPersistenceError` |

## Appendix G

**Path transport and discounted-score proofs**\
Paper label: `app:G` · Source ZIP member: `appendices/G_path_transport.tex`.

**Proof role.** Path/common-mass transport and discounted-score proofs.

**Scope boundary.** Separate primitive additive and common-mass product routes; formal finite-prefix interface also requests the joint-state (Y,Y) common-kernel instance. Probability normalization, initial mismatch and conditional histories stay explicit; a unit defect or unit initial mismatch trivializes the infinite product even when defects are summable.

**Documentary predecessors.** [`docs/CQ1_FINITE_PATH_BRIDGE.md`](../CQ1_FINITE_PATH_BRIDGE.md); [`docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md`](../CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md); [`docs/CQ1_CERTIFICATE_TRANSPORT.md`](../CQ1_CERTIFICATE_TRANSPORT.md); [`docs/LANE_A2_PRIMITIVE_TV.md`](../LANE_A2_PRIMITIVE_TV.md); [`research/paper_closures/spec/chapters/04_robustness.md`](../../research/paper_closures/spec/chapters/04_robustness.md); [`docs/LANE_E1_APPROX_QUOTIENT.md`](../LANE_E1_APPROX_QUOTIENT.md); [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_79/NEXT03_Q03_DEPENDENT_HISTORY_SCOPE.md`](../../research/paper_closures/post_merge_79/NEXT03_Q03_DEPENDENT_HISTORY_SCOPE.md). These documents retain their original source/date scope.

**Retained obligations.** [Later-Q1](RESIDUAL_STATUS.md#later-q1).

**Manuscript review references.** `Q05`, `Q13` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Probability/SummablePathScores.lean`](../../PermanssonResearch/Probability/SummablePathScores.lean) | `summable_output_score_error` |
| [`verification/research/tranche10_q04_scope_receipt_addendum.lean`](../../verification/research/tranche10_q04_scope_receipt_addendum.lean) | `treated_bad_row_defect_one` |
| [`verification/research/tranche10_q04_scope_receipt_addendum.lean`](../../verification/research/tranche10_q04_scope_receipt_addendum.lean) | `original_margin_error_equals_charged_budget` |
| [`PermanssonResearch/Quotient/Q05ActualAtomClosure.lean`](../../PermanssonResearch/Quotient/Q05ActualAtomClosure.lean) | `actual_original_B1_margin_bound` |
| [`verification/research/tranche7_q05_original_margin_addendum.lean`](../../verification/research/tranche7_q05_original_margin_addendum.lean) | `fine_original_margin` |

## Appendix H

**Transport, completeness and occupation proofs**\
Paper label: `app:H` · Source ZIP member: `appendices/H_metric_occupation.tex`.

**Proof role.** Transport/completeness/occupation derivations with separated metric profiles.

**Scope boundary.** Dual calculus may use pseudometrics; uniqueness uses a metric. First-moment KR does not need completeness, Banach invariants do; both compared laws must be supplied/constructed under their own premises. One globally fixed property, fallback and four actual path-law factorizations; complete separable metric/Borel selector profile, continuous descriptor for weak regenerative route, distinct measurable-descriptor P1 route.

**Documentary predecessors.** [`docs/LANE_A3_CONTRACTIVE.md`](../LANE_A3_CONTRACTIVE.md); [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/05_long_run.md`](../../research/paper_closures/spec/chapters/05_long_run.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md). These documents retain their original source/date scope.

**Retained obligations.** [A-01](RESIDUAL_STATUS.md#a-01), [A-04](RESIDUAL_STATUS.md#a-04).

**Manuscript review references.** `Q07` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Probability/FiniteTransportSeparation.lean`](../../PermanssonResearch/Probability/FiniteTransportSeparation.lean) | `exists_plan_of_dual` |
| [`PermanssonResearch/Probability/FiniteKantorovichDuality.lean`](../../PermanssonResearch/Probability/FiniteKantorovichDuality.lean) | `envelope_lipschitz` |
| [`PermanssonResearch/Probability/FiniteLipschitzExtension.lean`](../../PermanssonResearch/Probability/FiniteLipschitzExtension.lean) | `extension_error` |
| [`PermanssonResearch/Probability/FirstMomentKantorovichDuality.lean`](../../PermanssonResearch/Probability/FirstMomentKantorovichDuality.lean) | `firstMoment_couplingW1_le_of_w1DualLE` |
| [`PermanssonResearch/Probability/FinitePartitionMeasure.lean`](../../PermanssonResearch/Probability/FinitePartitionMeasure.lean) | `cell_mass_smul` |
| [`PermanssonResearch/Probability/FinitePartitionMeasure.lean`](../../PermanssonResearch/Probability/FinitePartitionMeasure.lean) | `liftLaw_first` |
| [`PermanssonResearch/Probability/FiniteQuantizationBound.lean`](../../PermanssonResearch/Probability/FiniteQuantizationBound.lean) | `distance_le_quantization` |
| [`PermanssonResearch/Probability/KRDualSeparation.lean`](../../PermanssonResearch/Probability/KRDualSeparation.lean) | `measure_eq_of_w1DualLE_zero` |
| [`PermanssonResearch/Probability/SummableStepLimit.lean`](../../PermanssonResearch/Probability/SummableStepLimit.lean) | `integral_dist_limit_le` |
| [`PermanssonResearch/Probability/GluedCouplingSequence.lean`](../../PermanssonResearch/Probability/GluedCouplingSequence.lean) | `law` |
| [`PermanssonResearch/Probability/SummableTransportLimit.lean`](../../PermanssonResearch/Probability/SummableTransportLimit.lean) | `exists_limit_of_summable_couplings` |
| [`PermanssonResearch/Perturbation/FiniteInvariantConstructor.lean`](../../PermanssonResearch/Perturbation/FiniteInvariantConstructor.lean) | `exists_unique_invariant` |
| [`PermanssonResearch/Probability/RegenerativeMomentCondition.lean`](../../PermanssonResearch/Probability/RegenerativeMomentCondition.lean) | `integrable_law_of_rewardCondition` |
| [`PermanssonResearch/Probability/FirstMomentEmpiricalConvergence.lean`](../../PermanssonResearch/Probability/FirstMomentEmpiricalConvergence.lean) | `empirical_tendsto_of_quantized_averages` |

## Appendix I

**Exact and geometric quotient derivations**\
Paper label: `app:I` · Source ZIP member: `appendices/I_quotients.tex`.

**Proof role.** Exact and geometric quotient derivations and source-adapter premises.

**Scope boundary.** Projected process need not be Markov; geometric common-mass/RN profile is stronger than old linear general-measurable profile; canonical positive initial mismatch adapter remains separately scoped.

**Documentary predecessors.** [`docs/LANE_E1_APPROX_QUOTIENT.md`](../LANE_E1_APPROX_QUOTIENT.md); [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`research/paper_closures/post_merge_102/NEXT04_ORIGINAL_MARGIN_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT04_ORIGINAL_MARGIN_V2_SCOPE.md); [`research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md`](../../research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md). These documents retain their original source/date scope.

**Retained obligations.** [Later-Q1](RESIDUAL_STATUS.md#later-q1).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Probability/ProjectedCommonSubkernel.lean`](../../PermanssonResearch/Probability/ProjectedCommonSubkernel.lean) | `map_liftProjectedDensity` |
| [`PermanssonResearch/Quotient/GeometricQuotient.lean`](../../PermanssonResearch/Quotient/GeometricQuotient.lean) | `map_projectedCommonKernel` |

## Appendix J

**History laws, monitor invariants, belief reduction, and safety**\
Paper label: `app:J` · Source ZIP member: `appendices/J_control.tex`.

**Proof role.** History, monitor, belief and safety proof details.

**Scope boundary.** Finite legal menus, history chronology, success/risk monitor separation and m+1 observations for m transitions; residence block index is j+m<=t. Finite nonempty hidden/observation/decision sets and common legal menu; belief reduction is for the stated observation-admissible history class. Exact flow reconstruction quantifies over stated behavioral policies; through-horizon danger survives completed success; infinite safety uses actual infinite law.

**Documentary predecessors.** [`docs/D1_CONTROLLED_KERNEL.md`](../D1_CONTROLLED_KERNEL.md); [`docs/D1_HISTORY_DEPENDENT.md`](../D1_HISTORY_DEPENDENT.md); [`docs/D1_TYPED_HISTORY_DEPENDENT.md`](../D1_TYPED_HISTORY_DEPENDENT.md); [`docs/D2_RESIDENCE_OBJECTIVE.md`](../D2_RESIDENCE_OBJECTIVE.md); [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md); [`docs/D1_BELLMAN.md`](../D1_BELLMAN.md); [`docs/D1_NONSTATIONARY_RATIONAL.md`](../D1_NONSTATIONARY_RATIONAL.md); [`docs/D1_TYPED_NONSTATIONARY.md`](../D1_TYPED_NONSTATIONARY.md); [`docs/D0_FROZEN_MENU.md`](../D0_FROZEN_MENU.md); [`research/paper_closures/spec/chapters/06_solver.md`](../../research/paper_closures/spec/chapters/06_solver.md). These documents retain their original source/date scope.

**Manuscript review references.** `CTRL-02`, `CTRL-12`, `CTRL-13` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/InitialLawMonitor.lean`](../../PermanssonResearch/ReverseSolver/InitialLawMonitor.lean) | `initialChronologicalLaw_monitor_expectation` |
| [`PermanssonResearch/ReverseSolver/InitialLawMonitor.lean`](../../PermanssonResearch/ReverseSolver/InitialLawMonitor.lean) | `monitor_initialLaw_optimal_and_attained` |
| [`PermanssonResearch/ReverseSolver/FiniteOccupancyMonitor.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyMonitor.lean) | `actual_monitor_consistent` |
| [`PermanssonResearch/ReverseSolver/FiniteOccupancyMonitor.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyMonitor.lean) | `consistent_eq_literal_run` |
| [`PermanssonResearch/ReverseSolver/FiniteOccupancyMonitor.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyMonitor.lean) | `actual_monitor_literal_integral` |
| [`PermanssonResearch/ReverseSolver/RollingMonitorTable.lean`](../../PermanssonResearch/ReverseSolver/RollingMonitorTable.lean) | `rollingMonitorTable_eq_value` |
| [`PermanssonResearch/ReverseSolver/ComputableFiniteMonitor.lean`](../../PermanssonResearch/ReverseSolver/ComputableFiniteMonitor.lean) | `computedMaximizer_attains` |
| [`PermanssonResearch/ReverseSolver/ControlledKernelExamples.lean`](../../PermanssonResearch/ReverseSolver/ControlledKernelExamples.lean) | `typed_feedback_strictly_improves` |
| [`PermanssonResearch/ReverseSolver/HistoryTypedExamples.lean`](../../PermanssonResearch/ReverseSolver/HistoryTypedExamples.lean) | `typed_history_deadline_optimum_five_eighths` |
| [`PermanssonResearch/ReverseSolver/NonstationaryExamples.lean`](../../PermanssonResearch/ReverseSolver/NonstationaryExamples.lean) | `false_cross_deadline_projectivity` |
| [`PermanssonResearch/ReverseSolver/HistoryPolicyExamples.lean`](../../PermanssonResearch/ReverseSolver/HistoryPolicyExamples.lean) | `reconverge_history_sensitive` |
| [`PermanssonResearch/ReverseSolver/HistoryPolicyExamples.lean`](../../PermanssonResearch/ReverseSolver/HistoryPolicyExamples.lean) | `reconverge_left_mass` |
| [`PermanssonResearch/ReverseSolver/HistoryPolicyExamples.lean`](../../PermanssonResearch/ReverseSolver/HistoryPolicyExamples.lean) | `reconverge_right_mass` |
| [`verification/research/BeliefObservationWitness.lean`](../../verification/research/BeliefObservationWitness.lean) | `observation_optimum` |
| [`verification/research/BeliefObservationWitness.lean`](../../verification/research/BeliefObservationWitness.lean) | `impossible_observation` |
| [`PermanssonResearch/ReverseSolver/FiniteOccupancyRiskFixture.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyRiskFixture.lean) | `actual_success` |
| [`PermanssonResearch/ReverseSolver/FiniteOccupancyRiskFixture.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyRiskFixture.lean) | `actual_danger` |
| [`PermanssonResearch/ReverseSolver/FiniteOccupancyRiskFixture.lean`](../../PermanssonResearch/ReverseSolver/FiniteOccupancyRiskFixture.lean) | `reconstructed_mixing_scores` |
| [`PermanssonResearch/ReverseSolver/ThroughHorizonRiskFixture.lean`](../../PermanssonResearch/ReverseSolver/ThroughHorizonRiskFixture.lean) | `failure_and_danger_are_not_complements` |
| [`PermanssonResearch/ReverseSolver/ThroughHorizonRiskFixture.lean`](../../PermanssonResearch/ReverseSolver/ThroughHorizonRiskFixture.lean) | `danger_after_completed_success_counts` |

## Appendix K

**Exact rational algorithms and their semantic proofs**\
Paper label: `app:K` · Source ZIP member: `appendices/K_algorithms.tex`.

**Proof role.** Exact rational algorithms and semantic proof details.

**Scope boundary.** Exact flow reconstruction quantifies over stated behavioral policies; through-horizon danger survives completed success; infinite safety uses actual infinite law. Total rational constructors retain positive dimensions, nonempty menus/comparison sets and path-law nontriviality; worst starts minimize absolute effects, not treated event probabilities. Nonlinear optimizer is for deterministic stationary policies; phase-aware and multichain examples do not establish unrestricted randomized/history optimality. Nature observing the realized control, private-current-draw stage play and a model fixed at time zero are distinct games.

**Documentary predecessors.** [`docs/D0_FROZEN_MENU.md`](../D0_FROZEN_MENU.md); [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/06_solver.md`](../../research/paper_closures/spec/chapters/06_solver.md); [`docs/LANE_C9_CERTIFIED_MENU_SYNTHESIS.md`](../LANE_C9_CERTIFIED_MENU_SYNTHESIS.md); [`docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`](../LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md); [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](../LANE_C11_CLASS_STATIONARY_CERTIFICATION.md); [`docs/D2_RESIDENCE_OBJECTIVE.md`](../D2_RESIDENCE_OBJECTIVE.md); [`research/paper_closures/post_merge_102/NEXT06_NATIVE_POLICY_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT06_NATIVE_POLICY_V2_SCOPE.md); [`research/paper_closures/post_merge_112/README.md`](../../research/paper_closures/post_merge_112/README.md); [`research/paper_closures/post_merge_79/NEXT06_D05_CHRONOLOGICAL_SCOPE.md`](../../research/paper_closures/post_merge_79/NEXT06_D05_CHRONOLOGICAL_SCOPE.md). These documents retain their original source/date scope.

**Manuscript review references.** `CTRL-14` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/ReverseSolver/RationalCertificateUniqueness.lean`](../../PermanssonResearch/ReverseSolver/RationalCertificateUniqueness.lean) | `checked_dirichlet_tables_unique` |
| [`PermanssonResearch/ReverseSolver/TypedStoppedClassAbsorption.lean`](../../PermanssonResearch/ReverseSolver/TypedStoppedClassAbsorption.lean) | `cramerWeight_eq_typedStoppedClass_probability` |
| [`PermanssonResearch/ReverseSolver/TypedObservedCramerCorrespondence.lean`](../../PermanssonResearch/ReverseSolver/TypedObservedCramerCorrespondence.lean) | `cramer_eventValue_eq_canonical_probability` |
| [`PermanssonResearch/ReverseSolver/C10RationalInitialMixture.lean`](../../PermanssonResearch/ReverseSolver/C10RationalInitialMixture.lean) | `checked_rationalMixedEventValue_eq_actual_path` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceMatrix.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceMatrix.lean) | `referenceMatrix_det_ne_zero` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceProbability.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceProbability.lean) | `referenceWeights_probability` |
| [`PermanssonResearch/ReverseSolver/C11SixStateWitness.lean`](../../PermanssonResearch/ReverseSolver/C11SixStateWitness.lean) | `sixClassA_eq_C4` |
| [`PermanssonResearch/ReverseSolver/C11SixStateWitness.lean`](../../PermanssonResearch/ReverseSolver/C11SixStateWitness.lean) | `sixClassB_eq_C4` |
| [`PermanssonResearch/ReverseSolver/C11SixStateWitness.lean`](../../PermanssonResearch/ReverseSolver/C11SixStateWitness.lean) | `sixFullFalseClass_typed` |
| [`PermanssonResearch/ReverseSolver/PolytopeActive.lean`](../../PermanssonResearch/ReverseSolver/PolytopeActive.lean) | `extreme_active_kernel_zero` |
| [`PermanssonResearch/ReverseSolver/PolytopeRational.lean`](../../PermanssonResearch/ReverseSolver/PolytopeRational.lean) | `extreme_active_gram_det_ne_zero` |
| [`PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean`](../../PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean) | `every_vertex_is_enumerated` |
| [`PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean`](../../PermanssonResearch/ReverseSolver/PolytopeCompleteness.lean) | `exists_rational_optimal_candidate` |
| [`PermanssonResearch/ApplicationBridge/LinearProgramReceipt.lean`](../../PermanssonResearch/ApplicationBridge/LinearProgramReceipt.lean) | `optimum_over_reals` |
| [`PermanssonResearch/ApplicationBridge/LinearProgramReceipt.lean`](../../PermanssonResearch/ApplicationBridge/LinearProgramReceipt.lean) | `infeasible_over_reals` |
| [`PermanssonResearch/ApplicationBridge/FlowInfeasibilityReceipt.lean`](../../PermanssonResearch/ApplicationBridge/FlowInfeasibilityReceipt.lean) | `checked_min_risk` |
| [`PermanssonResearch/ApplicationBridge/FlowInfeasibilityReceipt.lean`](../../PermanssonResearch/ApplicationBridge/FlowInfeasibilityReceipt.lean) | `checked_cap_infeasible` |
| [`PermanssonResearch/ReverseSolver/NonlinearOccupationBoundaryFixture.lean`](../../PermanssonResearch/ReverseSolver/NonlinearOccupationBoundaryFixture.lean) | `period_three_beats_all_stationary` |
| [`PermanssonResearch/ReverseSolver/NonlinearPeriodThreePathLaw.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPeriodThreePathLaw.lean) | `native_pathLaw_dirac` |
| [`PermanssonResearch/ReverseSolver/NonlinearPeriodThreeCanonical.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPeriodThreeCanonical.lean) | `native_actual_occupation_ae_limit` |
| [`PermanssonResearch/ReverseSolver/NonlinearPeriodThreeExpectedScore.lean`](../../PermanssonResearch/ReverseSolver/NonlinearPeriodThreeExpectedScore.lean) | `native_phase_aware_actual_score_one` |
| [`PermanssonResearch/ReverseSolver/C11ObservedStationary.lean`](../../PermanssonResearch/ReverseSolver/C11ObservedStationary.lean) | `trueShare_one_iff_all_true` |
| [`PermanssonResearch/ReverseSolver/C11ObservedStationary.lean`](../../PermanssonResearch/ReverseSolver/C11ObservedStationary.lean) | `trueShare_zero_iff_all_false` |
| [`PermanssonResearch/ReverseSolver/C11ObservedStationary.lean`](../../PermanssonResearch/ReverseSolver/C11ObservedStationary.lean) | `trueShare_mixed_iff` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean) | `periodic_reference_exact` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean) | `nearly_reducible_reference_exact` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean) | `physical_classes_remain_distinct` |
| [`PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean`](../../PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean) | `corrupted_stationary_receipt_rejected` |
| [`PermanssonResearch/ReverseSolver/CertifiedSelection.lean`](../../PermanssonResearch/ReverseSolver/CertifiedSelection.lean) | `selectRationalMember_dominates` |
| [`PermanssonResearch/ReverseSolver/TypedMenuCertification.lean`](../../PermanssonResearch/ReverseSolver/TypedMenuCertification.lean) | `certifiedSelected_exactValue` |
| [`PermanssonResearch/ReverseSolver/TypedMenuCertificationExamples.lean`](../../PermanssonResearch/ReverseSolver/TypedMenuCertificationExamples.lean) | `selected_typed_value_one` |
| [`PermanssonResearch/ReverseSolver/CanonicalCertificationExamples.lean`](../../PermanssonResearch/ReverseSolver/CanonicalCertificationExamples.lean) | `half_goal_two_steps` |
| [`PermanssonResearch/ReverseSolver/ExactSixStateC9MenuWitness.lean`](../../PermanssonResearch/ReverseSolver/ExactSixStateC9MenuWitness.lean) | `identityOnlyMenu_not_family_obstruction` |
| [`PermanssonResearch/ReverseSolver/ExactSixStateC9MenuWitness.lean`](../../PermanssonResearch/ReverseSolver/ExactSixStateC9MenuWitness.lean) | `negativeMenu_not_family_obstruction` |
| [`PermanssonResearch/ReverseSolver/ExactSixStateBOnly.lean`](../../PermanssonResearch/ReverseSolver/ExactSixStateBOnly.lean) | `bOnly_original_margin_zero` |
| [`PermanssonResearch/ReverseSolver/C10FullReceipt.lean`](../../PermanssonResearch/ReverseSolver/C10FullReceipt.lean) | `checkedFullReceipt_worstStart` |

## Appendix L

**Game laws, X1 arithmetic, multi-agent transport, and causal identification**\
Paper label: `app:L` · Source ZIP member: `appendices/L_games_multiagent.tex`.

**Proof role.** Game, X1, multi-agent and causal-identification proof details.

**Scope boundary.** X1 DescriptorHasTwoValues fails on replete B; IsDescriptorNondegenerate holds from times 0/1 with true masses 1 and 13/20; invariance fails. These paper-derived predicate observations are not new compiled X1 declarations. Strict anchors/common exogeneity, all-history model-specified rows including null histories, actual advancing clock, and whole marked laws must retain their precise separate profiles. Finite SCM identification requires the declared independent noise/positivity/information assumptions; no observation-only unrestricted causal identification or dynamic mediation follows.

**Documentary predecessors.** [`docs/LANE_X1_COMMONS.md`](../LANE_X1_COMMONS.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/01_x1.md`](../../research/paper_closures/spec/chapters/01_x1.md); [`research/paper_closures/spec/chapters/02_strategies.md`](../../research/paper_closures/spec/chapters/02_strategies.md); [`docs/LANE_F1_MULTIAGENT_PROTOCOLS.md`](../LANE_F1_MULTIAGENT_PROTOCOLS.md); [`research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md`](../../research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md); [`research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md`](../../research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md); [`research/paper_closures/post_merge_102/NEXT05_FULL_MARGIN_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT05_FULL_MARGIN_V2_SCOPE.md); [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/spec/chapters/03_autonomy.md`](../../research/paper_closures/spec/chapters/03_autonomy.md). These documents retain their original source/date scope.

**Retained obligations.** [X-01](RESIDUAL_STATUS.md#x-01), [F-02](RESIDUAL_STATUS.md#f-02), [M-02](RESIDUAL_STATUS.md#m-02).

**Manuscript review references.** `CTRL-11` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/StrategicWorld/ActionTraceStatePrefix.lean`](../../PermanssonResearch/StrategicWorld/ActionTraceStatePrefix.lean) | `canonical_coherent` |
| [`PermanssonResearch/StrategicWorld/ActionTraceOriginalBridge.lean`](../../PermanssonResearch/StrategicWorld/ActionTraceOriginalBridge.lean) | `canonical_state_erasure_eq_original` |
| [`PermanssonResearch/StrategicWorld/ActionTraceInitialLaw.lean`](../../PermanssonResearch/StrategicWorld/ActionTraceInitialLaw.lean) | `expected_verification_initial_measure` |
| [`PermanssonResearch/Games/DiscountedVerification.lean`](../../PermanssonResearch/Games/DiscountedVerification.lean) | `finite_performance_difference` |
| [`PermanssonResearch/X1/FullStrategyCertificate.lean`](../../PermanssonResearch/X1/FullStrategyCertificate.lean) | `exact_advantage_table` |
| [`PermanssonResearch/X1/FiniteOutputs.lean`](../../PermanssonResearch/X1/FiniteOutputs.lean) | `survivalProbability_eq_kernelTerminal_killed` |
| [`PermanssonResearch/X1/ExactMargins.lean`](../../PermanssonResearch/X1/ExactMargins.lean) | `effects_eq_candidates` |
| [`PermanssonResearch/X1/OccupationNumerics.lean`](../../PermanssonResearch/X1/OccupationNumerics.lean) | `poisson_identity` |
| [`PermanssonResearch/MultiAgent/AutonomousInputMarginal.lean`](../../PermanssonResearch/MultiAgent/AutonomousInputMarginal.lean) | `Profile.actual_input_marginal` |
| [`PermanssonResearch/MultiAgent/AutonomousMarkedKernel.lean`](../../PermanssonResearch/MultiAgent/AutonomousMarkedKernel.lean) | `autonomous_marked_atom` |
| [`PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean`](../../PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean) | `supported_update_eq` |
| [`PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean`](../../PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean) | `supported_full_kernel_eq` |
| [`PermanssonResearch/MultiAgent/AutonomousAETransport.lean`](../../PermanssonResearch/MultiAgent/AutonomousAETransport.lean) | `primitive_factor_agreement` |
| [`PermanssonResearch/MultiAgent/AutonomousAEContinuumFixture.lean`](../../PermanssonResearch/MultiAgent/AutonomousAEContinuumFixture.lean) | `nonatomic_treated_pathLaw_eq` |
| [`PermanssonResearch/MultiAgent/AutonomousAEContinuumFixture.lean`](../../PermanssonResearch/MultiAgent/AutonomousAEContinuumFixture.lean) | `point_start_treated_pathLaw_ne` |
| [`PermanssonResearch/MultiAgent/PlayerSwapConstitution.lean`](../../PermanssonResearch/MultiAgent/PlayerSwapConstitution.lean) | `original_effect` |
| [`PermanssonResearch/MultiAgent/PlayerSwapConstitution.lean`](../../PermanssonResearch/MultiAgent/PlayerSwapConstitution.lean) | `original_margin` |
| [`PermanssonResearch/MultiAgent/AsymmetricCommonSwapFixture.lean`](../../PermanssonResearch/MultiAgent/AsymmetricCommonSwapFixture.lean) | `asymmetric_mixed_original_path_law_transport` |
| [`PermanssonResearch/MultiAgent/ProtocolWitnesses.lean`](../../PermanssonResearch/MultiAgent/ProtocolWitnesses.lean) | `closedLoop_ne_openLoop` |
| [`PermanssonResearch/MultiAgent/ProtocolWitnesses.lean`](../../PermanssonResearch/MultiAgent/ProtocolWitnesses.lean) | `closedLoop_eq_openLoopExtract` |
| [`PermanssonResearch/MultiAgent/ProtocolWitnesses.lean`](../../PermanssonResearch/MultiAgent/ProtocolWitnesses.lean) | `declared_anchors_agree_on_support_but_openLoop_differs` |
| [`PermanssonResearch/MultiAgent/ProtocolWitnesses.lean`](../../PermanssonResearch/MultiAgent/ProtocolWitnesses.lean) | `correlated_generator_not_product` |
| [`PermanssonResearch/MultiAgent/MeasurableNatClockFixture.lean`](../../PermanssonResearch/MultiAgent/MeasurableNatClockFixture.lean) | `full_actual_real_projection` |
| [`verification/research/MultiAgentFiniteProduct.lean`](../../verification/research/MultiAgentFiniteProduct.lean) | `clActions` |
| [`verification/research/tranche8_f01_scope_receipt_addendum.lean`](../../verification/research/tranche8_f01_scope_receipt_addendum.lean) | `three_player_original_protocol_action_rows` |
| [`verification/research/tranche8_f01_scope_receipt_addendum.lean`](../../verification/research/tranche8_f01_scope_receipt_addendum.lean) | `three_player_original_asymmetric_physics` |
| [`verification/research/tranche8_f01_scope_receipt_addendum.lean`](../../verification/research/tranche8_f01_scope_receipt_addendum.lean) | `private_update_inputs_are_reindexed` |
| [`PermanssonResearch/MultiAgent/MeasurableProductRegression.lean`](../../PermanssonResearch/MultiAgent/MeasurableProductRegression.lean) | `actual_action_laws_distinct` |
| [`PermanssonResearch/MultiAgent/MeasurableProductRegression.lean`](../../PermanssonResearch/MultiAgent/MeasurableProductRegression.lean) | `replacement_update` |
| [`verification/research/MultiAgentNatPrivateClock.lean`](../../verification/research/MultiAgentNatPrivateClock.lean) | `schedule_nonperiodic` |
| [`verification/research/MultiAgentNatPrivateClock.lean`](../../verification/research/MultiAgentNatPrivateClock.lean) | `treated_clock_not_strict` |

## Appendix M

**Specialized dictionary, shell and source proofs**\
Paper label: `app:M` · Source ZIP member: `appendices/M_specialized.tex`.

**Proof role.** Conditional specialized dictionary, shell and source proofs.

**Scope boundary.** Raw shell c requires normalization e=c/||c|| and b_e=b/||c||; scalar r=1 result is not arbitrary-shell matrix monotonicity; conditional finite algebra does not establish full analytic source identification.

**Documentary predecessors.** [`research/paper_closures/spec/chapters/09_specialized.md`](../../research/paper_closures/spec/chapters/09_specialized.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_112/acceptance_obligations_report.md`](../../research/paper_closures/post_merge_112/acceptance_obligations_report.md). These documents retain their original source/date scope.

**Retained obligations.** [E-05](RESIDUAL_STATUS.md#e-05).

**Manuscript review references.** `ROOT-07`, `ROOT-08` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

| Cited repository file | Literal declaration or producer label |
|---|---|
| [`PermanssonResearch/Specialized/FiniteDetection.lean`](../../PermanssonResearch/Specialized/FiniteDetection.lean) | `quadratic_two_control_bound` |
| [`PermanssonResearch/Specialized/FiniteDetection.lean`](../../PermanssonResearch/Specialized/FiniteDetection.lean) | `negative_persists_under_embedding` |
| [`PermanssonResearch/Specialized/BoundaryWitnesses.lean`](../../PermanssonResearch/Specialized/BoundaryWitnesses.lean) | `exact_but_illegal_approximant` |
| [`PermanssonResearch/Specialized/BoundaryWitnesses.lean`](../../PermanssonResearch/Specialized/BoundaryWitnesses.lean) | `changed_embedding_loses_negativity` |
| [`PermanssonResearch/Specialized/BoundaryWitnesses.lean`](../../PermanssonResearch/Specialized/BoundaryWitnesses.lean) | `dimension_two_retains_second_equation` |
| [`PermanssonResearch/Specialized/BoundaryWitnesses.lean`](../../PermanssonResearch/Specialized/BoundaryWitnesses.lean) | `zero_shift_does_not_supply_inverse` |
| [`PermanssonResearch/Specialized/SingularCompatibility.lean`](../../PermanssonResearch/Specialized/SingularCompatibility.lean) | `singular_block_nonnegative_iff` |
| [`PermanssonResearch/Specialized/SingularCompatibility.lean`](../../PermanssonResearch/Specialized/SingularCompatibility.lean) | `incompatible_kernel_negative` |
| [`PermanssonResearch/Specialized/SingularCompatibility.lean`](../../PermanssonResearch/Specialized/SingularCompatibility.lean) | `denominator_free_kernel_rigidity` |
| [`PermanssonResearch/Specialized/E05FullGramMaskingCountermodel.lean`](../../PermanssonResearch/Specialized/E05FullGramMaskingCountermodel.lean) | `added_component_masks_actual_negative_gram` |

## Appendix N

**Application derivations, exact examples, and the confirmatory workflow**\
Paper label: `app:N` · Source ZIP member: `appendices/N_cases.tex`.

**Proof role.** Abstract application derivations and constructed examples with explicit empirical limits.

**Scope boundary.** Each fixture is tied to actual primitives, comparison domain and expected obstruction; a similarly named example does not discharge a different historical acceptance requirement. Nonempty random uncertainty set, alpha in [0,1], measurable coverage event and actual joint coverage are premises; descriptive/constructed applications do not become empirical regime certificates.

**Documentary predecessors.** [`docs/LANE_C4_SIX_STATE_PRECISION.md`](../LANE_C4_SIX_STATE_PRECISION.md); [`docs/LANE_C5_SHARP_FAMILY.md`](../LANE_C5_SHARP_FAMILY.md); [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md); [`research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md`](../../research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md); [`application/APPLICATION_STANDARD.md`](../../application/APPLICATION_STANDARD.md); [`docs/APPLICATION_BOUNDARY.md`](../APPLICATION_BOUNDARY.md); [`research/paper_closures/spec/chapters/08_grammar_economic.md`](../../research/paper_closures/spec/chapters/08_grammar_economic.md). These documents retain their original source/date scope.

**Manuscript review references.** `ROOT-04`, `ROOT-05` in [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md).

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## Appendix O

**Mathematical index and source-concordance conventions**\
Paper label: `app:O` · Source ZIP member: `appendices/O_concordance.tex`.

**Proof role.** Mathematical index and source-concordance conventions.

**Scope boundary.** Executable calculations, reflection, generated Lean, transitive axiom checks and independent acceptance are distinct evidence types. 798 files (64 core+710 research+24 other),7690 lexical units group-mapped; structural source-label presence and coverage are not individual semantic certification or a fresh full Lean build.

**Documentary predecessors.** [`docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`](../LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md); [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](../LANE_C11_CLASS_STATIONARY_CERTIFICATION.md); [`research/paper_closures/ACCEPTANCE_EVIDENCE_GUIDE.md`](../../research/paper_closures/ACCEPTANCE_EVIDENCE_GUIDE.md); [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md); [`docs/RESEARCH_BUILD.md`](../RESEARCH_BUILD.md); [`docs/V020_IMPLEMENTATION_INDEX.md`](../V020_IMPLEMENTATION_INDEX.md); [`docs/V020_RESEARCH_PROOF_LEDGER.md`](../V020_RESEARCH_PROOF_LEDGER.md); [`docs/V020_HARDENING.md`](../V020_HARDENING.md); [`research/paper_closures/README.md`](../../research/paper_closures/README.md). These documents retain their original source/date scope.

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## Appendix P

**Precise residual obligations and extension criteria**\
Paper label: `app:P` · Source ZIP member: `appendices/P_open.tex`.

**Proof role.** Precise source-relative residuals and extension criteria; separate from acceptance decisions.

**Scope boundary.** Track seven stronger/separately evidenced Appendix P obligations, broader conditional-profile limits, and independent acceptance separately; no source-presence-to-accepted inference.

**Documentary predecessors.** [`docs/FUTURE_THEORY_ROADMAP.md`](../FUTURE_THEORY_ROADMAP.md); [`docs/PERMANSSON_RESEARCH_ARCHITECTURE.md`](../PERMANSSON_RESEARCH_ARCHITECTURE.md); [`docs/PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md`](../PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md); [`research/paper_closures/post_merge_112/acceptance_obligations_report.md`](../../research/paper_closures/post_merge_112/acceptance_obligations_report.md). These documents retain their original source/date scope.

**Retained obligations.** [X-01](RESIDUAL_STATUS.md#x-01), [F-02](RESIDUAL_STATUS.md#f-02), [A-01](RESIDUAL_STATUS.md#a-01), [A-04](RESIDUAL_STATUS.md#a-04), [E-05](RESIDUAL_STATUS.md#e-05), [Later-Q1](RESIDUAL_STATUS.md#later-q1), [M-02](RESIDUAL_STATUS.md#m-02).

This destination has no literal source-anchor occurrence in the reviewed manuscript. Its prose, historical sources, bibliography and associated concordance records still form part of the paper.

## Numbered statement index

The following 147 rows reproduce the item kinds, titles and literal labels of the reviewed index. Each link routes to the containing section or appendix above. The [machine-readable statement index](../../paper2/v2.0.1/indices/statement_index.json) is the exact source record; these rows do not assign new proof or acceptance statuses.

| Item | Kind | Title | Literal paper label |
|---|---|---|---|
| 1 | lemma | Empirical pushforward and finite-prefix deletion | [`lem:C02-empirical`](#c02) |
| 2 | lemma | Common-mass estimate and measurable processing | [`lem:C02-commonmass`](#c02) |
| 3 | theorem | Typed composition | [`thm:C03-composition`](#c03) |
| 4 | theorem | Existence, uniqueness, and Markov property | [`thm:C03-path`](#c03) |
| 5 | proposition | Erasure and observable properties | [`prop:C03-erasure`](#c03) |
| 6 | definition | Exact generated regime | [`def:C04-GR`](#c04) |
| 7 | definition | Confirmatory subclass | [`def:C04-confirmatory`](#c04) |
| 8 | theorem | Killed-kernel calculus | [`thm:C04-killed`](#c04) |
| 9 | corollary | Equivalent exact-persistence statements | [`cor:C04-exact`](#c04) |
| 10 | definition | Finite persistence and quasi-regimes | [`def:C04-quasi`](#c04) |
| 11 | definition | Quasi-stationary distribution | [`def:C04-QSD`](#c04) |
| 12 | theorem | QSD survival and conditional stationarity | [`thm:C04-QSD`](#c04) |
| 13 | definition | Relative and family Permansson predicates | [`def:C05-PR`](#c05) |
| 14 | definition | Protocol-relative grounded property | [`def:C05-grounded`](#c05) |
| 15 | proposition | Nuisance exclusion | [`prop:C05-nuisance`](#c05) |
| 16 | theorem | Intervention-compatible representation invariance | [`thm:C05-representation`](#c05) |
| 17 | proposition | One-shot verification | [`prop:C06-one-shot`](#c06) |
| 18 | definition | Policy and mechanism constitution in the EGR model | [`def:C06-policy-PR`](#c06) |
| 19 | proposition | Scale-free resistance and stationary drift | [`prop:C06-resistance`](#c06) |
| 20 | theorem | Equilibrium and exact region closure | [`thm:C06-engagement`](#c06) |
| 21 | theorem | Spectral growth and the EGR | [`thm:C06-Perron`](#c06) |
| 22 | proposition | Constitutive growth and material cross-generation | [`prop:C06-constitutive-growth`](#c06) |
| 23 | proposition | State preservation and exact nesting | [`prop:C06-nonlinear`](#c06) |
| 24 | theorem | Complete claim-or-wait equilibrium correspondence | [`thm:C06-claim-equilibrium`](#c06) |
| 25 | theorem | Exact EGR and property recovery | [`thm:C06-embedding`](#c06) |
| 26 | theorem | Eventual class selection | [`thm:C07-class-selection`](#c07) |
| 27 | theorem | Actual random empirical limit and its whole law | [`thm:C07-random-limit`](#c07) |
| 28 | example | Branching and a periodic class | [`ex:C07-branching`](#c07) |
| 29 | theorem | Original exact GR if and only if the reachable target is common | [`thm:C08-exactGR`](#c08) |
| 30 | theorem | Exact opposing-mass effect and finite uniform margin | [`thm:C08-opposing`](#c08) |
| 31 | proposition | Exact support transport | [`prop:C08-support`](#c08) |
| 32 | theorem | Stationary random-law occupation | [`thm:C09-stationary`](#c09) |
| 33 | theorem | Compact Feller occupation family | [`thm:C09-Feller`](#c09) |
| 34 | proposition | Invariant law and integrable renewal rewards | [`prop:C09-renewal`](#c09) |
| 35 | theorem | Regenerative empirical Wasserstein limit | [`thm:C09-regenerative-W1`](#c09) |
| 36 | corollary | Genuine occupation-property factorization | [`cor:C09-factor`](#c09) |
| 37 | example | Escape and descriptor oscillation | [`ex:C09-failure`](#c09) |
| 38 | theorem | First-exit law, masks and conservation | [`thm:C10-routing`](#c10) |
| 39 | corollary | QSD destination law | [`cor:C10-QSD-destination`](#c10) |
| 40 | theorem | Unconditional full-future first-exit restart | [`thm:C10-restart`](#c10) |
| 41 | theorem | Occupation after a random entrance | [`thm:C10-occupation`](#c10) |
| 42 | theorem | Scoped intervention-driven switching | [`thm:C10-switch`](#c10) |
| 43 | example | Five-state strategic switching | [`ex:C10-switch`](#c10) |
| 44 | example | Routing, nonexit mass and failure of destination retention | [`ex:C10-exit-boundaries`](#c10) |
| 45 | definition | Frozen atomic bank and partition grammar | [`def:C11:grammar`](#c11) |
| 46 | proposition | Assembly of overlapping patches | [`prop:C11:assembly`](#c11) |
| 47 | proposition | Effect transport under exact realization | [`prop:C11:effecttransport`](#c11) |
| 48 | proposition | Conditional-margin inequalities | [`prop:C11:conditional`](#c11) |
| 49 | definition | Admitted minimality | [`def:C11:minimal`](#c11) |
| 50 | theorem | Existence and transport of minimal blocks | [`thm:C11:minimality`](#c11) |
| 51 | theorem | Transport of a finite certificate | [`thm:C12:finitecertificate`](#c12) |
| 52 | proposition | Additive and product primitive bounds | [`prop:C12:primitiveTV`](#c12) |
| 53 | proposition | Weighted sequential metric budget | [`prop:C12:metric`](#c12) |
| 54 | proposition | Zero horizon and a positive one-step certificate | [`prop:C12:horizons`](#c12) |
| 55 | theorem | Dependent-history product bound | [`thm:C13:product`](#c13) |
| 56 | theorem | Localized chronological bound | [`thm:C13:localized`](#c13) |
| 57 | theorem | Finite and first-moment duality | [`thm:C14:duality`](#c14) |
| 58 | theorem | Invariant law and geometric convergence | [`thm:C14:invariant`](#c14) |
| 59 | lemma | Occupation factorization | [`lem:C15:factor`](#c15) |
| 60 | theorem | Occupation-margin robustness | [`thm:C15:margin`](#c15) |
| 61 | theorem | Exact quotient preservation | [`thm:C16:exact`](#c16) |
| 62 | theorem | Projected-prefix bound | [`thm:C16:geometric`](#c16) |
| 63 | theorem | Nonstationary projected-history transport | [`thm:C16:nonstationary`](#c16) |
| 64 | definition | Legal behavioral history policy | [`def:C17-policy`](#c17) |
| 65 | theorem | Actual-law finite-horizon optimality | [`thm:C17-monitor-optimality`](#c17) |
| 66 | proposition | Filtering identity including null words | [`prop:C18-filter`](#c18) |
| 67 | theorem | Belief sufficiency and exact finite envelope | [`thm:C18-alpha`](#c18) |
| 68 | theorem | Flow realization | [`thm:C19-flow`](#c19) |
| 69 | theorem | Risk-constrained actual-policy optimization | [`thm:C19-risk-optimality`](#c19) |
| 70 | example | A genuinely mixed risk optimum | [`ex:C19-mixed-risk`](#c19) |
| 71 | theorem | Optimal infinite safety | [`thm:C19-infinite-safety`](#c19) |
| 72 | theorem | Total exact absorption certificate | [`thm:C20-absorption`](#c20) |
| 73 | theorem | Total stationary family and native equality | [`thm:C20-stationary`](#c20) |
| 74 | theorem | Computed frozen-menu margin equals the original margin | [`thm:C20-original-margin`](#c20) |
| 75 | proposition | Exact nonlinear expectation | [`prop:C21-exact-objective`](#c21) |
| 76 | theorem | Attained deterministic stationary optimum | [`thm:C21-stationary-optimum`](#c21) |
| 77 | example | Expectation of a score is not score of an average law | [`ex:C21-nonlinear-mixture`](#c21) |
| 78 | theorem | Actual rectangular saddle bounds | [`thm:C22-rectangular`](#c22) |
| 79 | example | Two-stage commitment changes survival | [`ex:C22-commitment`](#c22) |
| 80 | theorem | Exact private randomized optimum | [`thm:C22-private`](#c22) |
| 81 | example | Private matching and observed-control response | [`ex:C22-private-matching`](#c22) |
| 82 | theorem | Full-history discounted performance identity | [`thm:C23-performance`](#c23) |
| 83 | corollary | X1 exact full-history identity | [`cor:C23-X1-full-history`](#c23) |
| 84 | proposition | Measurable finite-product realization | [`prop:C24-product`](#c24) |
| 85 | theorem | Matched measurable two-player path and margin recovery | [`thm:C24-matched`](#c24) |
| 86 | proposition | Row autonomy if and only if history autonomy | [`prop:C24-row-history`](#c24) |
| 87 | theorem | Autonomous anchor path-law equality | [`thm:C24-autonomy`](#c24) |
| 88 | proposition | Finite legal-fibre criterion | [`prop:C24-legal-fibre`](#c24) |
| 89 | theorem | Finite mediation identification on used support | [`thm:C25-identification`](#c25) |
| 90 | proposition | Finite observational nonidentification | [`prop:C25-nonidentification`](#c25) |
| 91 | theorem | Source-scoped finite detection and nesting | [`thm:C26:detection`](#c26) |
| 92 | example | Periodic Exact GR | [`ex:periodic-original`](#c27) |
| 93 | example | The original stochastic factorization witness | [`ex:bernoulli-factorization`](#c27) |
| 94 | counterexample | An eigenmeasure does not give uniform persistence | [`ex:qsd-uniform`](#c27) |
| 95 | construction | Three-world restraint model | [`con:economic-witness`](#c27) |
| 96 | theorem | Incentives, occupation, and original uniform constitution | [`thm:economic-full`](#c27) |
| 97 | definition | A frozen confirmatory pipeline | [`def:confirmatory-pipeline`](#c28) |
| 98 | definition | Identified-set constitution | [`def:identified-constitution`](#c28) |
| 99 | proposition | Three distinct model-set conclusions | [`prop:modelset-distinction`](#c28) |
| 100 | theorem | A simultaneous outer-set certificate | [`thm:outer-certificate`](#c28) |
| 101 | proposition | Sharp completion bounds | [`prop:completion-bounds`](#c28) |
| 102 | proposition | Exact arithmetic and equilibrium of the frozen grid | [`prop:bm-exact`](#c28) |
| 103 | proposition | Correctness of finite primitive evaluation | [`prop:finite-kernel-algorithm`](#c29) |
| 104 | definition | A numerical receipt contract | [`def:receipt-contract`](#c29) |
| 105 | proposition | Reflection requires literal-data equality | [`prop:reflection-chain`](#c29) |
| 106 | definition | Evidence coordinates | [`def:evidence-coordinates`](#c30) |
| 107 | definition | Coverage dispositions | [`def:coverage-disposition`](#c30) |
| 108 | proposition | Polish descriptor extension | [`prop:A-Polish`](#appendix-a) |
| 109 | example | Polishness supplies no compactness of all laws | [`ex:A-escaping-Dirac`](#appendix-a) |
| 110 | example | Correct dual test class | [`ex:A-dual-class`](#appendix-a) |
| 111 | lemma | A countable open-lattice criterion | [`lem:A-countable-tests`](#appendix-a) |
| 112 | lemma | Initial mixtures and null-event transfer | [`lem:A-initial-mixture`](#appendix-a) |
| 113 | lemma | Pushforward of the first composition factor | [`lem:C-compProd`](#appendix-c) |
| 114 | lemma | Deterministic orbit law | [`lem:C-deterministic`](#appendix-c) |
| 115 | proposition | Unobserved-draw boundary | [`prop:C-information`](#appendix-c) |
| 116 | proposition | Minimal nonnegative exit-time solution | [`prop:C-Green`](#appendix-c) |
| 117 | theorem | Complete same-space signature transport | [`thm:C-signature`](#appendix-c) |
| 118 | lemma | Two-sided property errors and the infimum | [`lem:C-output-errors`](#appendix-c) |
| 119 | lemma | Orthogonality, square times and interpolation | [`lem:D-innovation`](#appendix-d) |
| 120 | lemma | Uniform block hitting | [`lem:D-block`](#appendix-d) |
| 121 | proposition | Typed four-state absorption | [`prop:D-fourstate`](#appendix-d) |
| 122 | proposition | The exact six-state integration | [`prop:D-sixstate`](#appendix-d) |
| 123 | proposition | Full and soft six-state constitutive responses | [`prop:D-response`](#appendix-d) |
| 124 | lemma | Finite and infinite Hopf inequalities | [`lem:E-Hopf`](#appendix-e) |
| 125 | theorem | Bounded pointwise ergodic convergence | [`thm:E-bounded-Birkhoff`](#appendix-e) |
| 126 | corollary | Integrable extension and uniform average approximation | [`cor:E-L1`](#appendix-e) |
| 127 | proposition | Actual bounded regenerative averages | [`prop:E-regenerative-bounded`](#appendix-e) |
| 128 | lemma | Shift-invariant good-event transfer | [`lem:E-regenerative-transfer`](#appendix-e) |
| 129 | example | Noncompact reset-and-increment witness | [`ex:E-reset-increment`](#appendix-e) |
| 130 | proposition | An actual joint-only persistent PR | [`prop:F:booleanPR`](#appendix-f) |
| 131 | example | Admitted does not mean every syntactic subset | [`ex:F:admission`](#appendix-f) |
| 132 | example | Equal margin profiles under an invalid label bijection | [`ex:F:invalidbijection`](#appendix-f) |
| 133 | example | A fixed baseline does not determine its replacement bank | [`ex:F:banks`](#appendix-f) |
| 134 | theorem | Summable whole-path score transport | [`thm:G:summable`](#appendix-g) |
| 135 | corollary | Finite attainment as a mathematical consequence | [`cor:H:finiteattainment`](#appendix-h) |
| 136 | lemma | Bounded finite Lipschitz extension | [`lem:H:extension`](#appendix-h) |
| 137 | proposition | Finite-cell transport estimate | [`prop:H:cells`](#appendix-h) |
| 138 | lemma | Zero dual distance separates probability laws | [`lem:H:separation`](#appendix-h) |
| 139 | lemma | Stored summary equals the literal scan | [`lem:J-monitor-consistency`](#appendix-j) |
| 140 | lemma | Rolling-table equality | [`lem:J-table`](#appendix-j) |
| 141 | proposition | Boolean class-share trichotomy | [`prop:K-share-trichotomy`](#appendix-k) |
| 142 | example | A null key and a changed initial law | [`ex:L-null-key`](#appendix-l) |
| 143 | proposition | Deterministic-mixture construction | [`prop:clipped-wellposed`](#appendix-n) |
| 144 | proposition | Reported counts identify a product | [`prop:poisson-thinning`](#appendix-n) |
| 145 | proposition | An inactive input cannot identify its coefficient | [`prop:inactive-channel`](#appendix-n) |
| 146 | proposition | Stock decay and the first-step lag | [`prop:reserve-lag`](#appendix-n) |
| 147 | proposition | Projected-path null | [`prop:projected-null`](#appendix-n) |

## Complete Lean inventory and written groups

The [798-file index](../../paper2/v2.0.1/indices/all_lean_written_connections.json) has one row for every Lean file in the pinned inventory: **64 core**, **710 research** and **24 other** files (22 verification Lean files and the two import roots). Every row has a reviewed module/proof-group connection. The index expressly sets individual declaration semantic equivalence to false; that field is preserved.

The **7,690 declaration/example units** are lexical inventory units, including definitions and other declarations. They are not a count of independently verified theorem equivalences. The table below groups each file once by its primary inventory chapter; a file can have additional actual manuscript destinations in its own index row.

| Primary inventory chapter | Files | Lexical units | Subject |
|---|---|---|---|
| [C02](#c02) | 34 | 288 | Probability, measurable structure, and convergence |
| [C03](#c03) | 11 | 113 | Chronological strategic-world dynamics and canonical laws |
| [C04](#c04) | 14 | 129 | Generated regimes, persistence, and quasi-stationarity |
| [C05](#c05) | 19 | 142 | Constitution, grounding, and representation |
| [C06](#c06) | 10 | 144 | The equilibrium predecessor: models, mechanisms and exact recovery |
| [C07](#c07) | 131 | 1014 | Finite recurrence and the complete law of random occupations |
| [C08](#c08) | 13 | 59 | Exact finite GR and property-specific PR characterizations |
| [C09](#c09) | 19 | 181 | Nonfinite occupation: stationary, compact Feller and regenerative routes |
| [C10](#c10) | 45 | 321 | Exit destinations, full-future restart and intervention-driven switching |
| [C11](#c11) | 55 | 541 | Admitted grammars, interaction and minimality |
| [C12](#c12) | 26 | 145 | Finite constitutive certificates and primitive error budgets |
| [C13](#c13) | 16 | 248 | Finite, localized and whole-path probability bounds |
| [C14](#c14) | 33 | 318 | Transport metrics, contraction and invariant-law construction |
| [C15](#c15) | 11 | 85 | Frozen occupation properties and original-margin robustness |
| [C16](#c16) | 26 | 257 | Exact and approximate intervention-compatible quotients |
| [C17](#c17) | 91 | 742 | Finite histories, monitors, and adaptive feedback |
| [C18](#c18) | 21 | 233 | Belief control and nonstationary dynamics |
| [C19](#c19) | 15 | 190 | Occupation flows, risk constraints, and infinite safety |
| [C20](#c20) | 60 | 417 | Total rational construction and recovery of the original semantics |
| [C21](#c21) | 15 | 157 | Nonlinear occupation objectives and stationary policy optimization |
| [C22](#c22) | 7 | 123 | Robust control, rectangular Nature, and private randomization |
| [C23](#c23) | 21 | 297 | Discounted full-history verification and the X1 model |
| [C24](#c24) | 54 | 728 | Measurable multi-agent mechanisms, autonomy, clocks, and mediators |
| [C25](#c25) | 2 | 35 | Finite structural causal models and mediation identification |
| [C26](#c26) | 8 | 82 | Specialized finite algebra, detection and source rigidity |
| [C27](#c27) | 14 | 241 | Constructed examples and counterexamples |
| [C29](#c29) | 24 | 460 | Exact algorithms, reflection, and executable evidence |
| [C30](#c30) | 3 | 0 | Formalization, reproducibility, and source concordance |

The research import root directly imports all 710 research modules at the pinned source. The core root directly imports 63 of its 64 module files; [`PermanssonLean/Regime/SurvivalBridge.lean`](../../PermanssonLean/Regime/SurvivalBridge.lean) is the explicit direct-import exception. Module presence is not inferred to mean root inclusion. See the preserved [reference guide identity and import note](../reference/README.md).

The broader inventory contains **793 Python files**. Their detailed roles are retained in the source ZIP at `coverage/inventory/python_computation_coverage.json`, alongside `repository_all_files_coverage.json` and `lean_all_declarations_coverage.json`. An exact checker, producer, fixture, build script and historical report have different roles; none is promoted to a formal proof merely by appearing in that inventory. Current executable scope is described in [application compatibility](APPLICATION_COMPATIBILITY.md) and [verification](VERIFICATION.md).

## Historical document navigation

The following predecessor documents retain their original wording and source identities. In particular, the original formalization map describes the v0.1.8 boundary, and the v0.2.0 index, lane notes, scope reviews and roadmap retain their dated checkpoints even where their prose uses words such as “current” or “live”. Use the current paper routes here to interpret their place in v2.0.1; use [residual status](RESIDUAL_STATUS.md) for the current manuscript's outstanding obligations.

| Existing document | Current paper destinations | Reading convention |
|---|---|---|
| [`docs/CQ1_CERTIFICATE_TRANSPORT.md`](../CQ1_CERTIFICATE_TRANSPORT.md) | [C12](#c12); [F](#appendix-f); [G](#appendix-g) | Dated source/scope record; acceptance unchanged |
| [`docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md`](../CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md) | [C12](#c12); [F](#appendix-f); [G](#appendix-g) | Dated source/scope record; acceptance unchanged |
| [`docs/CQ1_FINITE_PATH_BRIDGE.md`](../CQ1_FINITE_PATH_BRIDGE.md) | [C02](#c02); [C12](#c12); [A](#appendix-a); [F](#appendix-f); [G](#appendix-g) | Dated source/scope record; acceptance unchanged |
| [`docs/D0_FROZEN_MENU.md`](../D0_FROZEN_MENU.md) | [C19](#c19); [C20](#c20); [J](#appendix-j); [K](#appendix-k) | Dated source/scope record; acceptance unchanged |
| [`docs/D1_BELLMAN.md`](../D1_BELLMAN.md) | [C18](#c18); [J](#appendix-j) | Dated source/scope record; acceptance unchanged |
| [`docs/D1_CONTROLLED_KERNEL.md`](../D1_CONTROLLED_KERNEL.md) | [C17](#c17); [J](#appendix-j) | Dated source/scope record; acceptance unchanged |
| [`docs/D1_HISTORY_DEPENDENT.md`](../D1_HISTORY_DEPENDENT.md) | [C17](#c17); [J](#appendix-j) | Dated source/scope record; acceptance unchanged |
| [`docs/D1_NONSTATIONARY_RATIONAL.md`](../D1_NONSTATIONARY_RATIONAL.md) | [C18](#c18); [J](#appendix-j) | Dated source/scope record; acceptance unchanged |
| [`docs/D1_TYPED_HISTORY_DEPENDENT.md`](../D1_TYPED_HISTORY_DEPENDENT.md) | [C17](#c17); [J](#appendix-j) | Dated source/scope record; acceptance unchanged |
| [`docs/D1_TYPED_NONSTATIONARY.md`](../D1_TYPED_NONSTATIONARY.md) | [C18](#c18); [J](#appendix-j) | Dated source/scope record; acceptance unchanged |
| [`docs/D2_RESIDENCE_OBJECTIVE.md`](../D2_RESIDENCE_OBJECTIVE.md) | [C17](#c17); [C21](#c21); [J](#appendix-j); [K](#appendix-k) | Dated source/scope record; acceptance unchanged |
| [`docs/FORMALIZATION_MAP.md`](../FORMALIZATION_MAP.md) | [C01](#c01); [C02](#c02); [C03](#c03); [C04](#c04); [C05](#c05); [C06](#c06); [C16](#c16); [C30](#c30); [A](#appendix-a); [B](#appendix-b); [C](#appendix-c); [I](#appendix-i); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`docs/FUTURE_THEORY_ROADMAP.md`](../FUTURE_THEORY_ROADMAP.md) | [C01](#c01); [C31](#c31); [B](#appendix-b); [P](#appendix-p) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_A2_PRIMITIVE_TV.md`](../LANE_A2_PRIMITIVE_TV.md) | [C12](#c12); [C13](#c13); [F](#appendix-f); [G](#appendix-g) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_A3_CONTRACTIVE.md`](../LANE_A3_CONTRACTIVE.md) | [C14](#c14); [C15](#c15); [H](#appendix-h) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_B2_SEQUENTIAL_EFFECTS.md`](../LANE_B2_SEQUENTIAL_EFFECTS.md) | [C11](#c11); [F](#appendix-f) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md`](../LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md) | [C05](#c05); [C11](#c11); [C](#appendix-c); [F](#appendix-f) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`](../LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md) | [C20](#c20); [C29](#c29); [K](#appendix-k); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](../LANE_C11_CLASS_STATIONARY_CERTIFICATION.md) | [C20](#c20); [C21](#c21); [C29](#c29); [K](#appendix-k); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C4_SIX_STATE_PRECISION.md`](../LANE_C4_SIX_STATE_PRECISION.md) | [C07](#c07); [C27](#c27); [D](#appendix-d); [N](#appendix-n) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C5_SHARP_FAMILY.md`](../LANE_C5_SHARP_FAMILY.md) | [C07](#c07); [C27](#c27); [D](#appendix-d); [N](#appendix-n) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C6_TYPED_OBSERVED_RESPONSE.md`](../LANE_C6_TYPED_OBSERVED_RESPONSE.md) | [C08](#c08); [D](#appendix-d) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C7_FINITE_EVENT_RESPONSE.md`](../LANE_C7_FINITE_EVENT_RESPONSE.md) | [C08](#c08); [D](#appendix-d) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C8_SUPPORT_GRAPH_CONSTITUTION.md`](../LANE_C8_SUPPORT_GRAPH_CONSTITUTION.md) | [C08](#c08); [D](#appendix-d) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C9_CERTIFIED_MENU_SYNTHESIS.md`](../LANE_C9_CERTIFIED_MENU_SYNTHESIS.md) | [C20](#c20); [K](#appendix-k) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C_ABSORBING_REGIME_FAMILIES.md`](../LANE_C_ABSORBING_REGIME_FAMILIES.md) | [C04](#c04); [C07](#c07); [C](#appendix-c); [D](#appendix-d) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C_EXACT_GR_CHARACTERIZATION.md`](../LANE_C_EXACT_GR_CHARACTERIZATION.md) | [C08](#c08); [D](#appendix-d) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C_EXIT_RANDOM_ENTRY.md`](../LANE_C_EXIT_RANDOM_ENTRY.md) | [C10](#c10); [E](#appendix-e) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C_EXIT_RESTART.md`](../LANE_C_EXIT_RESTART.md) | [C10](#c10); [E](#appendix-e) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C_EXIT_ROUTING.md`](../LANE_C_EXIT_ROUTING.md) | [C10](#c10); [E](#appendix-e) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C_EXIT_SWITCHING.md`](../LANE_C_EXIT_SWITCHING.md) | [C10](#c10); [E](#appendix-e) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_C_RECURRENT_CLASSES.md`](../LANE_C_RECURRENT_CLASSES.md) | [C07](#c07); [D](#appendix-d) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_E1_APPROX_QUOTIENT.md`](../LANE_E1_APPROX_QUOTIENT.md) | [C13](#c13); [C16](#c16); [G](#appendix-g); [I](#appendix-i) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_F1_MULTIAGENT_PROTOCOLS.md`](../LANE_F1_MULTIAGENT_PROTOCOLS.md) | [C24](#c24); [C25](#c25); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`docs/LANE_X1_COMMONS.md`](../LANE_X1_COMMONS.md) | [C23](#c23); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`docs/PERMANSSON_RESEARCH_ARCHITECTURE.md`](../PERMANSSON_RESEARCH_ARCHITECTURE.md) | [C01](#c01); [C31](#c31); [B](#appendix-b); [P](#appendix-p) | Dated source/scope record; acceptance unchanged |
| [`docs/PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md`](../PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md) | [C31](#c31); [P](#appendix-p) | Dated source/scope record; acceptance unchanged |
| [`docs/RESEARCH_BUILD.md`](../RESEARCH_BUILD.md) | [C30](#c30); [O](#appendix-o) | Permitted current navigation plus preserved dated build evidence |
| [`docs/V020_HARDENING.md`](../V020_HARDENING.md) | [C30](#c30); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`docs/V020_IMPLEMENTATION_INDEX.md`](../V020_IMPLEMENTATION_INDEX.md) | [C30](#c30); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`docs/V020_RESEARCH_PROOF_LEDGER.md`](../V020_RESEARCH_PROOF_LEDGER.md) | [C30](#c30); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/A3_STRATEGY_Q_SELECTED_SCOPE_REVIEW.md) | [C13](#c13); [C14](#c14); [C15](#c15); [C23](#c23); [G](#appendix-g); [H](#appendix-h); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/ACCEPTANCE_EVIDENCE_GUIDE.md`](../../research/paper_closures/ACCEPTANCE_EVIDENCE_GUIDE.md) | [C29](#c29); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md`](../../research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md) | [C24](#c24); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/README.md`](../../research/paper_closures/README.md) | [C09](#c09); [C30](#c30); [E](#appendix-e); [O](#appendix-o) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md) | [C09](#c09); [C15](#c15); [C23](#c23); [C25](#c25); [C26](#c26); [C27](#c27); [B](#appendix-b); [E](#appendix-e); [H](#appendix-h); [L](#appendix-l); [M](#appendix-m); [N](#appendix-n) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md`](../../research/paper_closures/SOLVER_SELECTED_SCOPE_REVIEW.md) | [C17](#c17); [C18](#c18); [C19](#c19); [C22](#c22); [C25](#c25); [J](#appendix-j); [K](#appendix-k); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_102/NEXT04_ORIGINAL_MARGIN_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT04_ORIGINAL_MARGIN_V2_SCOPE.md) | [C16](#c16); [I](#appendix-i) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_102/NEXT05_FULL_MARGIN_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT05_FULL_MARGIN_V2_SCOPE.md) | [C24](#c24); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_102/NEXT06_NATIVE_POLICY_V2_SCOPE.md`](../../research/paper_closures/post_merge_102/NEXT06_NATIVE_POLICY_V2_SCOPE.md) | [C21](#c21); [K](#appendix-k) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md`](../../research/paper_closures/post_merge_112/Q05_NONIDENTITY_SOURCE_SCOPE.md) | [C16](#c16); [C27](#c27); [I](#appendix-i); [N](#appendix-n) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_112/README.md`](../../research/paper_closures/post_merge_112/README.md) | [C21](#c21); [K](#appendix-k) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_112/acceptance_obligations_report.md`](../../research/paper_closures/post_merge_112/acceptance_obligations_report.md) | [C26](#c26); [C31](#c31); [B](#appendix-b); [M](#appendix-m); [P](#appendix-p) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md`](../../research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md) | [C24](#c24); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_79/NEXT03_Q03_DEPENDENT_HISTORY_SCOPE.md`](../../research/paper_closures/post_merge_79/NEXT03_Q03_DEPENDENT_HISTORY_SCOPE.md) | [C13](#c13); [G](#appendix-g) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_79/NEXT06_B01_OVERLAP.md`](../../research/paper_closures/post_merge_79/NEXT06_B01_OVERLAP.md) | [C11](#c11); [F](#appendix-f) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/post_merge_79/NEXT06_D05_CHRONOLOGICAL_SCOPE.md`](../../research/paper_closures/post_merge_79/NEXT06_D05_CHRONOLOGICAL_SCOPE.md) | [C22](#c22); [K](#appendix-k) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/01_x1.md`](../../research/paper_closures/spec/chapters/01_x1.md) | [C23](#c23); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/02_strategies.md`](../../research/paper_closures/spec/chapters/02_strategies.md) | [C23](#c23); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/03_autonomy.md`](../../research/paper_closures/spec/chapters/03_autonomy.md) | [C25](#c25); [L](#appendix-l) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/04_robustness.md`](../../research/paper_closures/spec/chapters/04_robustness.md) | [C12](#c12); [F](#appendix-f); [G](#appendix-g) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/05_long_run.md`](../../research/paper_closures/spec/chapters/05_long_run.md) | [C09](#c09); [C14](#c14); [E](#appendix-e); [H](#appendix-h) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/06_solver.md`](../../research/paper_closures/spec/chapters/06_solver.md) | [C19](#c19); [J](#appendix-j); [K](#appendix-k) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/08_grammar_economic.md`](../../research/paper_closures/spec/chapters/08_grammar_economic.md) | [C11](#c11); [C28](#c28); [B](#appendix-b); [F](#appendix-f); [N](#appendix-n) | Dated source/scope record; acceptance unchanged |
| [`research/paper_closures/spec/chapters/09_specialized.md`](../../research/paper_closures/spec/chapters/09_specialized.md) | [C26](#c26); [B](#appendix-b); [M](#appendix-m) | Dated source/scope record; acceptance unchanged |

## Maintaining the map

A new manuscript edition needs a new versioned label/statement/source index and a checked mapping to it. A source change needs a new fixed source identity and a review of affected hypothesis and proof-role differences. Keep the current publication manifest, historic source records and actual compiler/numeric receipts separate. A successful path or label check establishes a valid navigation target; it does not establish elaborated type equivalence or independent acceptance.
