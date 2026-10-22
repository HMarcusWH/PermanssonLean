# Permansson PR #113 — original acceptance obligation work queue

**CANDIDATE / NOT ACCEPTED / NO INDEPENDENT REVIEW.**

This report is derived from unchanged original criteria and source mappings. It is not an exact-head CI receipt or independent scholarly approval.

- Original cases: 45; pending: 15; partial scope: 30; independently accepted: 0.
- New claim owners: 11; accepted: 0.
- Candidate test paths below are NOT verified as sufficient for their original criteria.

## Original acceptance requirements (all 45)

| Case | Candidate state | Original required result | Historical theorem pins | Candidate tests |
|---|---|---|---:|---|
| X-01 | PENDING | Kernel-checked equality; changed world/update/action row rejected | 3 | verification/research/test_next03_stochastic_lean.py, verification/research/test_paper_x1_matrix_lean.py |
| X-02 | PARTIAL_SCOPE | Actual-kernel induction identifies each entry | 4 | verification/research/test_paper_x1_lean_closure.py, verification/research/test_x1_commons.py |
| X-03 | PARTIAL_SCOPE | Original constitutiveMargin equalities and exact attainers | 5 | verification/research/test_paper_x1_lean_closure.py, verification/research/test_x1_commons.py |
| X-04 | PENDING | Lean proof fails at arithmetic/domain obligation; parser failure alone insufficient | 5 | verification/research/test_next03_tied_start_lean.py, verification/research/test_final_closure_missing_original_positives.py |
| X-05 | PARTIAL_SCOPE | Typed kernel equality fails | 7 | verification/research/test_paper_x1_lean_closure.py, verification/research/test_final_closure_missing_original_positives.py |
| X-06 | PARTIAL_SCOPE | Rejected; leakage theorem remains unchanged | 5 | verification/research/test_x1_commons.py, verification/research/test_e1_approx_quotient.py, verification/research/test_final_closure_missing_original_positives.py, verification/research/test_final_closure_existing_false_semantics_lean.py |
| S-01 | PARTIAL_SCOPE | Exact identity including terminal beta^N value | 6 | verification/research/test_paper_strategy_economic_lean.py |
| S-02 | PARTIAL_SCOPE | Outside admitted information class; no verification theorem | 6 | verification/research/test_paper_information_lean.py, verification/research/test_d2_residence.py |
| M-01 | PARTIAL_SCOPE | Full counterfactual path laws equal under stated premises | 5 | verification/research/test_paper_autonomy_ae_lean.py, verification/research/test_f1_multiagent_protocols.py |
| M-02 | PENDING | Autonomy premise rejected; reactive witness not counted strict | 7 | verification/research/test_next03_m02_marked_coupling.py, verification/research/test_m02_marked_actual_source_lean.py, verification/research/test_m02_actual_history_kernel_lean.py |
| F-01 | PENDING | P inputs reindexed correctly, no assumed symmetry | 8 | verification/research/test_next03_asymmetric_common_swap_lean.py, verification/research/test_final05_measurable_lean.py |
| F-02 | PARTIAL_SCOPE | Projection/exogeneity fails | 5 | verification/research/test_paper_measurable_clock_lean.py, verification/research/test_f1_multiagent_protocols.py, verification/research/test_final_closure_more_false_semantics_lean.py |
| F-03 | PARTIAL_SCOPE | No feasible strict probability anchor | 4 | verification/research/test_paper_closure_boundaries.py, verification/research/test_f1_multiagent_protocols.py, verification/research/test_final_closure_missing_original_positives.py, verification/research/test_f03_actual_infeasible_strict_anchor_lean.py |
| F-04 | PARTIAL_SCOPE | Single-product claim fails; mediator mixture succeeds | 3 | verification/research/test_f1_multiagent_protocols.py, verification/research/test_final_closure_more_false_semantics_lean.py |
| F-05 | PENDING | Mediation not identified without sufficient premises | 5 | verification/research/test_next03_positive_mediation.py, verification/research/test_paper_closure_boundaries.py, verification/research/test_final_closure_more_false_semantics_lean.py |
| Q-01 | PARTIAL_SCOPE | Geometric bound holds without claiming projection Markov | 6 | verification/research/test_e1_approx_quotient.py |
| Q-02 | PENDING | Correct boundaries; mismatched unbudgeted starts rejected | 6 | verification/research/test_next04_projection_arithmetic.py, verification/research/test_final_closure_more_false_semantics_lean.py |
| Q-03 | PENDING | Product mass proved, no independence assumption | 3 | verification/research/test_next03_dependent_three_stage.py, verification/research/test_a2_primitive_tv.py, verification/research/test_final_actual_product_reporting_false_lean.py |
| Q-04 | PENDING | Intervention defect charged rather than omitted | 2 | verification/research/test_localized_prefix_compiler.py, verification/research/test_next04_original_margin.py, verification/research/test_final_actual_product_reporting_false_lean.py |
| Q-05 | PENDING | No unqualified whole-path/Exact-GR transfer | 10 | verification/research/test_final04_source_lean.py, verification/research/test_next04_original_margin_lean.py, verification/research/test_next04_projection_arithmetic.py, verification/research/test_q05_nonidentity_source_fixture.py, verification/research/test_q05_actual_source_lean.py, verification/research/test_q05_original_margin_adapter_lean.py, verification/research/test_q05_actual_atom_closure_lean.py |
| A-01 | PARTIAL_SCOPE | Finite dual equality checked; wrong supnorm test class rejected | 6 | verification/research/test_paper_metric_coupling_lean.py, verification/research/test_a3_contractive.py |
| A-02 | PARTIAL_SCOPE | Missing strict contraction/uniqueness exposed | 13 | verification/research/test_paper_invariant_lean.py, verification/research/test_a3_contractive.py |
| A-03 | PARTIAL_SCOPE | Bounded-diameter conversion not applied | 7 | verification/research/test_a3_contractive.py |
| A-04 | PARTIAL_SCOPE | Four-process wrapper unavailable, not silently three-process | 8 | verification/research/test_a3_contractive.py, verification/research/test_paper_strategy_economic_lean.py |
| A-05 | PARTIAL_SCOPE | Property identity fails rather than being assumed | 8 | verification/research/test_a3_contractive.py, verification/research/test_final_closure_missing_original_positives.py |
| D-01 | PARTIAL_SCOPE | Same literal-event value; deterministic augmented maximizer attains | 11 | verification/research/test_d2_residence.py |
| D-02 | PARTIAL_SCOPE | Exact event classification including word 1,0,1,1 | 10 | verification/research/test_d2_residence.py, verification/research/test_monitor_stationary_closures.py, verification/research/test_final_original_chronological_false_lean.py |
| D-03 | PARTIAL_SCOPE | Declared precedence and separate risk monitor preserved | 16 | verification/research/test_monitor_stationary_closures.py, verification/research/test_paper_through_risk_lean.py, verification/research/test_final_original_chronological_false_lean.py |
| D-04 | PARTIAL_SCOPE | Optimum17/20 atp1/2, unconstrained p1 infeasible | 10 | verification/research/test_d2_residence.py, verification/research/test_paper_risk_lp_lean.py, verification/research/test_final_original_risk_belief_false_lean.py |
| D-05 | PENDING | Committed value.09 differs from rectangular.01 | 9 | verification/research/test_next06_committed_path_law.py, verification/research/test_final_original_chronological_false_lean.py |
| D-06 | PENDING | Full augmented belief required | 7 | verification/research/test_next06_reachable_completion_belief.py, verification/research/test_final_original_risk_belief_false_lean.py |
| D-07 | PARTIAL_SCOPE | Infinite optimum determined by limit theorem, not one finite bound | 9 | verification/research/test_paper_infinite_safety_lean.py, verification/research/test_d2_residence.py |
| D-08 | PENDING | No admissible typed controlled row | 5 | verification/research/test_final_d08_admission.py, verification/research/test_next06_d08_joint_only_compiler.py |
| D-09 | PENDING | Class identity retained; descriptor score aggregates correctly | 7 | verification/research/test_final_d09_multichain.py, verification/research/test_final06_phaseblind_original.py |
| C11-01 | PARTIAL_SCOPE | Valid nonempty families accepted; n0 rejected | 7 | verification/research/test_lane_c11_stationary.py |
| C11-02 | PARTIAL_SCOPE | Existing checker rejects complete faulty output | 7 | verification/research/test_lane_c11_stationary.py, verification/research/test_final_closure_missing_original_positives.py |
| C-01 | PARTIAL_SCOPE | No unrestricted nonfinite occupation theorem | 11 | verification/research/test_paper_nonfinite_counterexample_lean.py |
| B-01 | PENDING | Compatibility rejected; order dependence exposed | 6 | verification/research/test_next06_overlap_lean.py, verification/research/test_lane_b2_sequential_effects.py, verification/research/test_final_closure_missing_original_positives.py |
| B-02 | PENDING | No unique-minimum or monotonicity inference | 3 | verification/research/test_lane_b2_sequential_effects.py, verification/research/test_b02_actual_original_margin_lean.py, verification/research/test_b02_local_nonisomorphic_margin_lean.py |
| XPLUS-01 | PARTIAL_SCOPE | Correct source constructors and kappa1; no edit to old X1 | 4 | verification/research/test_paper_strategy_economic_lean.py, verification/research/test_x1_commons.py |
| E-01 | PARTIAL_SCOPE | Rank-one/scalar promotion rejected | 4 | verification/research/test_paper_closure_boundaries.py, verification/research/test_paper_specialized_boundary_lean.py |
| E-02 | PARTIAL_SCOPE | No persistent witness transfer | 4 | verification/research/test_paper_closure_boundaries.py, verification/research/test_final_closure_missing_original_positives.py, verification/research/test_final_closure_existing_false_semantics_lean.py |
| E-03 | PARTIAL_SCOPE | No scalar shell reduction or unjustified inverse | 4 | verification/research/test_paper_closure_boundaries.py, verification/research/test_final_closure_missing_original_positives.py, verification/research/test_final_closure_existing_false_semantics_lean.py |
| E-04 | PARTIAL_SCOPE | No pseudoinverse positivity certificate or cancellation | 5 | verification/research/test_paper_closure_boundaries.py, verification/research/test_final_closure_missing_original_positives.py, verification/research/test_final_closure_existing_false_semantics_lean.py |
| E-05 | PARTIAL_SCOPE | No unqualified negative full-form conclusion | 4 | verification/research/test_paper_closure_boundaries.py, verification/research/test_paper_specialized_boundary_lean.py |

## Fifteen case-specific historical objections

| Case | Still-to-be-reconciled obligation(s) |
|---|---|
| X-01 | R2-A01: emitted-literal corruption is not stochasticity-preserving. |
| X-04 | R2-A02: unique learner attainer removal is tested, not tied-equilibrium domain removal. |
| M-02 | R2-A04: marked-versus-unmarked action-coupling distinction has no dedicated tracked countermodel. |
| F-01 | R2-A03: asymmetric common/private-update swap fixture missing. / R2-I02: general measurable n=2 product identity is distinct from the finite full model/path recovery. |
| F-05 | R2-A05: positive exact SCM test is in the full suite, but not this 48-check route; dedicated positive Lean instantiation is absent. |
| Q-02 | ANA-03: direct projected theorem uses matched starts/homogeneous kernels; expanded projected adapter remains open. |
| Q-03 | ANA-01: routed executable tests the old additive primitive budget, not product saturation. |
| Q-04 | ANA-02: selected localized visit/original-margin/reporting integration missing. |
| Q-05 | ANA-04: generic discounted/whole-law results are proved; a quotient-native original-margin application must still supply its actual bindings. |
| D-05 | SR-A04: 9/100 versus1/100 boundary is scalar arithmetic rather than an instantiated committed-model path-law fixture. |
| D-06 | SR-A05: hidden-flag fixture uses different pure priors, not two reachable histories from one fixed initial law. |
| D-08 | SR-A02: concrete typed compatible-overlap and joint-only certified block fixture missing. |
| D-09 | SR-A01: concrete ExactClassFunctional and two-state5/6-versus1 regression missing. |
| B-01 | SR-A02: generic compatible overlap proved; concrete typed positive/negative overlap fixtures missing. |
| B-02 | SR-A03: non-global-isomorphism positive local-margin transport fixture missing. / R2-C01: preserved OR/AND labels are correct for ablation margins. |

## Eleven candidate claim owners (not yet accepted)

| Claim | Owner source | Fully qualified declaration count | Status |
|---|---|---:|---|
| Q1 | PermanssonResearch/Quotient/DiscountedCanonicalSourceWitness.lean | 1 | SOURCE_PRESENT_REVIEW_PENDING |
| Q2 | PermanssonResearch/Quotient/DiscountedCanonicalMarginClosure.lean | 2 | SOURCE_PRESENT_REVIEW_PENDING |
| Q3 | PermanssonResearch/Quotient/DiscountedCanonicalWitnessExamples.lean | 3 | SOURCE_PRESENT_REVIEW_PENDING |
| M1 | PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedProtocols.lean | 2 | SOURCE_PRESENT_REVIEW_PENDING |
| M2 | PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean | 4 | SOURCE_PRESENT_REVIEW_PENDING |
| M3 | PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedExamples.lean | 3 | SOURCE_PRESENT_REVIEW_PENDING |
| N1 | PermanssonResearch/ReverseSolver/NonlinearPeriodThreeStationary.lean | 2 | SOURCE_PRESENT_REVIEW_PENDING |
| N2 | PermanssonResearch/ReverseSolver/NonlinearPeriodThreeExpectedScore.lean | 5 | SOURCE_PRESENT_REVIEW_PENDING |
| N3 | PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean | 4 | SOURCE_PRESENT_REVIEW_PENDING |
| D8 | PermanssonResearch/ReverseSolver/AdaptiveGrammarAdmissionFixture.lean | 3 | SOURCE_PRESENT_REVIEW_PENDING |
| D9 | PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean | 6 | SOURCE_PRESENT_REVIEW_PENDING |

## Executable-route gaps (unreviewed; not acceptance)

- Missing selected positive controls: 0 of 45.
- Missing selected semantic false-mutant routes: 17 of 45.
- Passing scope-boundary checks do **not** discharge the mandatory compiler-negative evidence obligation.
- A selected method still requires source relevance, actual exact-head execution, intact logs, authenticated check-run attribution and independent approval.

| Case | Positive method routes | Semantic-negative routes | Scope-boundary observations |
|---|---:|---:|---:|
| X-01 | 1 | 1 | 0 |
| X-02 | 1 | 2 | 0 |
| X-03 | 2 | 1 | 0 |
| X-04 | 1 | 1 | 0 |
| X-05 | 1 | 3 | 0 |
| X-06 | 1 | 1 | 2 |
| S-01 | 1 | 0 | 0 |
| S-02 | 1 | 0 | 1 |
| M-01 | 2 | 0 | 0 |
| M-02 | 3 | 2 | 1 |
| F-01 | 2 | 1 | 0 |
| F-02 | 1 | 1 | 1 |
| F-03 | 2 | 1 | 2 |
| F-04 | 1 | 1 | 1 |
| F-05 | 1 | 1 | 1 |
| Q-01 | 1 | 0 | 1 |
| Q-02 | 1 | 1 | 1 |
| Q-03 | 2 | 1 | 0 |
| Q-04 | 2 | 1 | 0 |
| Q-05 | 5 | 3 | 2 |
| A-01 | 2 | 0 | 0 |
| A-02 | 1 | 0 | 1 |
| A-03 | 1 | 0 | 1 |
| A-04 | 1 | 0 | 1 |
| A-05 | 1 | 0 | 2 |
| D-01 | 2 | 0 | 0 |
| D-02 | 1 | 1 | 1 |
| D-03 | 2 | 1 | 0 |
| D-04 | 2 | 1 | 0 |
| D-05 | 1 | 1 | 1 |
| D-06 | 1 | 1 | 1 |
| D-07 | 2 | 0 | 0 |
| D-08 | 1 | 1 | 0 |
| D-09 | 3 | 1 | 0 |
| C11-01 | 1 | 0 | 1 |
| C11-02 | 1 | 0 | 2 |
| C-01 | 1 | 0 | 0 |
| B-01 | 1 | 1 | 1 |
| B-02 | 3 | 2 | 1 |
| XPLUS-01 | 1 | 0 | 1 |
| E-01 | 1 | 0 | 1 |
| E-02 | 1 | 1 | 2 |
| E-03 | 1 | 1 | 2 |
| E-04 | 1 | 1 | 2 |
| E-05 | 1 | 0 | 1 |

## Closure protocol

Each original case requires a correct Lean source/premise binding, a positive control and semantically false mutant, genuine check-run IDs and a separately authenticated non-author exact-H case-specific review. Source-only PENDING/PARTIAL decisions cannot self-promote.

After source H freezes, signed reviewer and effective acceptance overlays remain DETACHED. Any approved mathematical paper additionally requires genuine merged M, page-by-page PDF inspection and independent postmerge scholarly signoff. A compiler-green source does not certify empirical GR/PR or unrestricted randomized policy optimality.
