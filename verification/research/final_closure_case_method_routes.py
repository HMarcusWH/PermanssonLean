"""Original 45-case test-method discovery routes for source review (ENG-04).

Each route identifies an *existing test method*, not an executed CI receipt,
proved criterion, accepted negative mutation, or reviewer authorization.
Roles describe what the candidate test attempts to inspect. A case is not
accepted until the original expected result, full proof dependency graph,
required positive/negative controls, execution provenance, and independent
review have all been separately authenticated.
"""
from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
METHOD_ROUTES = {
  "X-01": [
    [
      "test_next03_stochastic_lean.py",
      "test_actual_kernel_equality_rejects_normalized_wrong_row",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_paper_x1_matrix_lean.py",
      "test_source_bound_transitive_audit",
      "COMPILER_SOURCE"
    ]
  ],
  "X-02": [
    [
      "test_paper_x1_lean_closure.py",
      "test_corrupt_terminal_literal",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_paper_x1_lean_closure.py",
      "test_wrong_terminal_horizon",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_x1_commons.py",
      "test_paths_match_matrix_properties_and_killed_recursion",
      "EXACT_CHECK"
    ]
  ],
  "X-03": [
    [
      "test_paper_x1_lean_closure.py",
      "test_exact_positive_controls",
      "COMPILER_SOURCE"
    ],
    [
      "test_x1_commons.py",
      "test_prospective_full_region_infima_check_every_start",
      "EXACT_CHECK"
    ],
    [
      "test_paper_x1_lean_closure.py",
      "test_omitted_minimizing_start",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "X-04": [
    [
      "test_next03_tied_start_lean.py",
      "test_lean_false_original_domain_mutation",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_X_04_original_source_positive",
      "COMPILER_SOURCE"
    ]
  ],
  "X-05": [
    [
      "test_paper_x1_lean_closure.py",
      "test_reset_before_action",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_paper_x1_lean_closure.py",
      "test_new_world_learning",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_paper_x1_lean_closure.py",
      "test_swapped_update_protocol",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_X_05_original_source_positive",
      "COMPILER_SOURCE"
    ]
  ],
  "X-06": [
    [
      "test_x1_commons.py",
      "test_leaking_region_not_exact_gr_and_persistence_decay",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_e1_approx_quotient.py",
      "test_positive_quotient_margin_not_exact_gr",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_X_06_original_source_positive",
      "COMPILER_SOURCE"
    ],
    [
      "test_final_closure_existing_false_semantics_lean.py",
      "test_X_06_false_exact_gr_under_real_leakage",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "S-01": [
    [
      "test_paper_strategy_economic_lean.py",
      "test_source_bound_transitive_axioms",
      "COMPILER_SOURCE"
    ]
  ],
  "S-02": [
    [
      "test_paper_information_lean.py",
      "test_original_information_class_and_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_d2_residence.py",
      "test_history_sensitive_policy_no_future_information",
      "SCOPE_BOUNDARY"
    ]
  ],
  "M-01": [
    [
      "test_paper_autonomy_ae_lean.py",
      "test_actual_all_time_autonomy_and_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_f1_multiagent_protocols.py",
      "test_strict_autonomous_off_support_difference_stochastic_crosscheck",
      "EXACT_CHECK"
    ]
  ],
  "M-02": [
    [
      "test_next03_m02_marked_coupling.py",
      "test_unmarked_key_laws_identical",
      "EXACT_CHECK"
    ],
    [
      "test_next03_m02_marked_coupling.py",
      "test_marked_diagonal_is_maximally_separating",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_m02_marked_actual_source_lean.py",
      "test_original_typed_generator_source_and_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_m02_marked_actual_source_lean.py",
      "test_invalid_strict_autonomy_promotion_fails_semantically",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_m02_actual_history_kernel_lean.py",
      "test_real_marked_history_full_source_and_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_m02_actual_history_kernel_lean.py",
      "test_falsified_actual_marked_diagonal_is_rejected",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "F-01": [
    [
      "test_next03_asymmetric_common_swap_lean.py",
      "test_actual_common_update_false_same_input_claim",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_final05_measurable_lean.py",
      "test_matched_asymmetric_source_witnesses",
      "COMPILER_SOURCE"
    ],
    [
      "test_next03_asymmetric_common_swap_lean.py",
      "test_source_bound_non_dirac_asymmetric_whole_path",
      "COMPILER_SOURCE"
    ]
  ],
  "F-02": [
    [
      "test_paper_measurable_clock_lean.py",
      "test_actual_measurable_clock_projection_and_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_f1_multiagent_protocols.py",
      "test_nonstationary_anchor_needs_clock_in_baseline",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_more_false_semantics_lean.py",
      "test_F_02_false_stalled_original_natural_clock",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "F-03": [
    [
      "test_paper_closure_boundaries.py",
      "test_nonempty_state_menus_can_have_empty_key_intersection",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_f1_multiagent_protocols.py",
      "test_infeasible_anchor_excluded_separate_toy",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_F_03_original_source_positive",
      "COMPILER_SOURCE"
    ],
    [
      "test_f03_actual_infeasible_strict_anchor_lean.py",
      "test_actual_all_state_legal_fibre_and_original_existence_theorems",
      "COMPILER_SOURCE"
    ],
    [
      "test_f03_actual_infeasible_strict_anchor_lean.py",
      "test_false_feasible_anchor_with_conflicting_own_fibre_rejected",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "F-04": [
    [
      "test_f1_multiagent_protocols.py",
      "test_ma3_correlated_law_not_product_exact",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_f1_multiagent_protocols.py",
      "test_ma3_shared_source_is_representable",
      "EXACT_CHECK"
    ],
    [
      "test_final_closure_more_false_semantics_lean.py",
      "test_F_04_false_product_representation_of_correlated_law",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "F-05": [
    [
      "test_next03_positive_mediation.py",
      "test_mediator_matters_not_only_direct_treatment",
      "EXACT_CHECK"
    ],
    [
      "test_paper_closure_boundaries.py",
      "test_observed_mediation_does_not_identify_joint_intervention",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_more_false_semantics_lean.py",
      "test_F_05_false_identification_of_original_joint_do",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "Q-01": [
    [
      "test_e1_approx_quotient.py",
      "test_projection_is_not_markov_from_one_start",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_e1_approx_quotient.py",
      "test_geometric_bound_numeric_only",
      "EXACT_CHECK"
    ]
  ],
  "Q-02": [
    [
      "test_next04_projection_arithmetic.py",
      "test_zero_kernel_defect_does_not_delete_initial_mismatch",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_next04_projection_arithmetic.py",
      "test_time_varying_initial_and_row_budget",
      "EXACT_CHECK"
    ],
    [
      "test_final_closure_more_false_semantics_lean.py",
      "test_Q_02_false_zero_initial_error_under_zero_row_defect",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "Q-03": [
    [
      "test_next03_dependent_three_stage.py",
      "test_true_conditional_history_dependence",
      "EXACT_CHECK"
    ],
    [
      "test_a2_primitive_tv.py",
      "test_a2_15_seeded_exact_rational_primitive_rows",
      "EXACT_CHECK"
    ],
    [
      "test_final_actual_product_reporting_false_lean.py",
      "test_Q_03_false_independent_error_mass",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "Q-04": [
    [
      "test_localized_prefix_compiler.py",
      "test_actual_final_source_and_semantic_mutations",
      "COMPILER_SOURCE"
    ],
    [
      "test_next04_original_margin.py",
      "test_both_error_sides",
      "EXACT_CHECK"
    ],
    [
      "test_final_actual_product_reporting_false_lean.py",
      "test_Q_04_false_zero_intervention_report_error",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "Q-05": [
    [
      "test_final04_source_lean.py",
      "test_actual_kernel_witness_examples_and_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_next04_projection_arithmetic.py",
      "test_repeated_tiny_leaks_do_not_justify_exact_invariance",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_q05_nonidentity_source_fixture.py",
      "test_exact_canonical_discounted_values_for_both_original_starts",
      "EXACT_CHECK"
    ],
    [
      "test_q05_nonidentity_source_fixture.py",
      "test_baseline_only_witness_misses_treatment_reachable_state",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_q05_actual_source_lean.py",
      "test_actual_typed_primitive_models_and_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_q05_actual_source_lean.py",
      "test_wrong_original_effect_cannot_compile",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_q05_original_margin_adapter_lean.py",
      "test_exact_original_margin_type_and_axiom_dependencies",
      "COMPILER_SOURCE"
    ],
    [
      "test_q05_original_margin_adapter_lean.py",
      "test_unproved_source_domination_cannot_be_ignored",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_q05_actual_atom_closure_lean.py",
      "test_all_original_kernel_atoms_pointwitness_and_margin_compiler",
      "COMPILER_SOURCE"
    ],
    [
      "test_q05_actual_atom_closure_lean.py",
      "test_actual_baseline_nonzero_atom_cannot_be_erased",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "A-01": [
    [
      "test_paper_metric_coupling_lean.py",
      "test_actual_metric_certificates_and_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_a3_contractive.py",
      "test_dual_equals_coupling_on_the_line",
      "EXACT_CHECK"
    ]
  ],
  "A-02": [
    [
      "test_paper_invariant_lean.py",
      "test_source_bound_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_a3_contractive.py",
      "test_no_contraction_no_bound",
      "SCOPE_BOUNDARY"
    ]
  ],
  "A-03": [
    [
      "test_a3_contractive.py",
      "test_bounded_diameter_conversion",
      "EXACT_CHECK"
    ],
    [
      "test_a3_contractive.py",
      "test_unbounded_no_conversion",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_pr113_semantic_boundary_candidates.py",
      "test_A_03_unbounded_TV_does_not_bound_W1",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "A-04": [
    [
      "test_a3_contractive.py",
      "test_four_process_factorization_cannot_be_deleted",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_paper_strategy_economic_lean.py",
      "test_source_bound_transitive_axioms",
      "COMPILER_SOURCE"
    ]
  ],
  "A-05": [
    [
      "test_a3_contractive.py",
      "test_a3_3_survival_flips",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_a3_contractive.py",
      "test_four_process_factorization_cannot_be_deleted",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_A_05_original_source_positive",
      "COMPILER_SOURCE"
    ]
  ],
  "D-01": [
    [
      "test_d2_residence.py",
      "test_bellman_equals_enumerated_deterministic_policies",
      "EXACT_CHECK"
    ],
    [
      "test_d2_residence.py",
      "test_product_clock_and_history_values_agree",
      "EXACT_CHECK"
    ]
  ],
  "D-02": [
    [
      "test_d2_residence.py",
      "test_retry_is_distinct_from_first_ever_entry",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_monitor_stationary_closures.py",
      "test_all_short_physical_words",
      "EXACT_CHECK"
    ],
    [
      "test_final_original_chronological_false_lean.py",
      "test_D_02_false_retryable_residence_word",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "D-03": [
    [
      "test_monitor_stationary_closures.py",
      "test_retry_first_and_danger_boundaries",
      "EXACT_CHECK"
    ],
    [
      "test_paper_through_risk_lean.py",
      "test_actual_history_risk_flag_and_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_final_original_chronological_false_lean.py",
      "test_D_03_false_danger_after_success_revokes_it",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "D-04": [
    [
      "test_d2_residence.py",
      "test_risk_budget_changes_optimum",
      "EXACT_CHECK"
    ],
    [
      "test_paper_risk_lp_lean.py",
      "test_actual_solver_signatures_and_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_final_original_risk_belief_false_lean.py",
      "test_D_04_false_hard_risk_budget_accepts_p_one",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "D-05": [
    [
      "test_next06_committed_path_law.py",
      "test_rectangular_reselection_is_a_different_path_law",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_next06_committed_path_law.py",
      "test_committed_model_identity_persists_between_stages",
      "EXACT_CHECK"
    ],
    [
      "test_final_original_chronological_false_lean.py",
      "test_D_05_false_committed_rectangular_path_law_equality",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "D-06": [
    [
      "test_next06_reachable_completion_belief.py",
      "test_both_histories_have_mass_under_the_same_law",
      "EXACT_CHECK"
    ],
    [
      "test_next06_reachable_completion_belief.py",
      "test_same_physical_readout_does_not_identify_completion",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_original_risk_belief_false_lean.py",
      "test_D_06_false_same_readout_identifies_completion",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "D-07": [
    [
      "test_paper_infinite_safety_lean.py",
      "test_actual_infinite_safety_audit",
      "COMPILER_SOURCE"
    ],
    [
      "test_d2_residence.py",
      "test_deterministic_robust_value_zero",
      "EXACT_CHECK"
    ],
    [
      "test_pr113_semantic_boundary_candidates.py",
      "test_D_07_finite_survival_does_not_imply_infinite_safety",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "D-08": [
    [
      "test_final_d08_admission.py",
      "test_false_frozen_joint_admission_is_semantic_mutant",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_next06_d08_joint_only_compiler.py",
      "test_actual_original_margin_control_and_false_mutant",
      "COMPILER_SOURCE"
    ]
  ],
  "D-09": [
    [
      "test_final_d09_multichain.py",
      "test_exact_expected_score_not_score_of_expected_law",
      "EXACT_CHECK"
    ],
    [
      "test_final06_phaseblind_original.py",
      "test_exact_policy_scores_not_just_orbit_table",
      "EXACT_CHECK"
    ],
    [
      "test_final_d09_multichain.py",
      "test_compiled_distinct_physical_classes_and_nonlinear_lemma",
      "COMPILER_SOURCE"
    ],
    [
      "test_final_d09_multichain.py",
      "test_wrong_single_mixed_canonical_score_cannot_be_five_sixths",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "C11-01": [
    [
      "test_lane_c11_stationary.py",
      "test_02_periodic_alternation",
      "EXACT_CHECK"
    ],
    [
      "test_lane_c11_stationary.py",
      "test_13_zero_and_resource_limits",
      "SCOPE_BOUNDARY"
    ]
  ],
  "C11-02": [
    [
      "test_lane_c11_stationary.py",
      "test_07_forged_share_after_hash_repair",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_lane_c11_stationary.py",
      "test_09_missing_extra_and_duplicate_classes",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_C11_02_original_source_positive",
      "COMPILER_SOURCE"
    ]
  ],
  "C-01": [
    [
      "test_paper_nonfinite_counterexample_lean.py",
      "test_source_bound_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_pr113_semantic_boundary_candidates.py",
      "test_C_01_bounded_descriptor_occupation_nonconvergence",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "B-01": [
    [
      "test_next06_overlap_lean.py",
      "test_positive_and_false_compatibility_compile",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_lane_b2_sequential_effects.py",
      "test_14_invalid_order_or_noncommuting_patch",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_B_01_original_source_positive",
      "COMPILER_SOURCE"
    ]
  ],
  "B-02": [
    [
      "test_lane_b2_sequential_effects.py",
      "test_09_AND_incomparable_singleton_supports",
      "EXACT_CHECK"
    ],
    [
      "test_lane_b2_sequential_effects.py",
      "test_10_XOR_destroys_upward_monotonicity",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_b02_actual_original_margin_lean.py",
      "test_actual_original_margin_minimality_and_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_b02_actual_original_margin_lean.py",
      "test_false_joint_minimality_is_rejected_semantically",
      "SEMANTIC_NEGATIVE"
    ],
    [
      "test_b02_local_nonisomorphic_margin_lean.py",
      "test_original_nonisomorphic_local_margin_compiles",
      "COMPILER_SOURCE"
    ],
    [
      "test_b02_local_nonisomorphic_margin_lean.py",
      "test_inadmissible_original_singleton_false_claim_rejected",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "XPLUS-01": [
    [
      "test_paper_strategy_economic_lean.py",
      "test_source_bound_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_x1_commons.py",
      "test_leaking_region_not_exact_gr_and_persistence_decay",
      "SCOPE_BOUNDARY"
    ]
  ],
  "E-01": [
    [
      "test_paper_closure_boundaries.py",
      "test_seam_invisibility_can_have_rank_two",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_paper_specialized_boundary_lean.py",
      "test_negative_statements_and_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_pr113_semantic_boundary_candidates.py",
      "test_E_01_seam_invisibility_does_not_force_rank_one",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "E-02": [
    [
      "test_paper_closure_boundaries.py",
      "test_exact_approximant_can_violate_legal_carrier",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_paper_closure_boundaries.py",
      "test_embedding_without_form_preservation_loses_negative_witness",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_E_02_original_source_positive",
      "COMPILER_SOURCE"
    ],
    [
      "test_final_closure_existing_false_semantics_lean.py",
      "test_E_02_false_legal_negative_witness_from_illegal_approximation",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "E-03": [
    [
      "test_paper_closure_boundaries.py",
      "test_two_dimensional_shell_needs_second_equation",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_paper_closure_boundaries.py",
      "test_zero_shift_does_not_invert_psd_singular_core",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_E_03_original_source_positive",
      "COMPILER_SOURCE"
    ],
    [
      "test_final_closure_existing_false_semantics_lean.py",
      "test_E_03_false_two_dimensional_shell_collapse",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "E-04": [
    [
      "test_paper_closure_boundaries.py",
      "test_singular_missing_preimage_produces_negative_vector",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_paper_closure_boundaries.py",
      "test_source_exceptional_branch_does_not_force_vanishing",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_final_closure_missing_original_positives.py",
      "test_E_04_original_source_positive",
      "COMPILER_SOURCE"
    ],
    [
      "test_final_closure_existing_false_semantics_lean.py",
      "test_E_04_false_zero_shift_inverse",
      "SEMANTIC_NEGATIVE"
    ]
  ],
  "E-05": [
    [
      "test_paper_closure_boundaries.py",
      "test_positive_component_can_mask_gram_negative_direction",
      "SCOPE_BOUNDARY"
    ],
    [
      "test_paper_specialized_boundary_lean.py",
      "test_negative_statements_and_transitive_axioms",
      "COMPILER_SOURCE"
    ],
    [
      "test_e05_full_gram_masking_lean.py",
      "test_original_signed_negative_and_masked_total_compiler",
      "COMPILER_SOURCE"
    ],
    [
      "test_e05_full_gram_masking_lean.py",
      "test_false_unqualified_full_gram_negativity_rejected",
      "SEMANTIC_NEGATIVE"
    ]
  ]
}
ROLES = frozenset({"COMPILER_SOURCE", "EXACT_CHECK", "SEMANTIC_NEGATIVE", "SCOPE_BOUNDARY"})


def validated_routes(case_ids, *, root=ROOT, routes=METHOD_ROUTES):
    """Fail before emitting a map if the exact original IDs/tests drift."""
    case_ids = tuple(case_ids)
    if len(case_ids) != 45 or len(set(case_ids)) != 45 or set(routes) != set(case_ids):
        raise ValueError("test selection does not cover the exact 45 original IDs")
    cache = {}
    selected = {}
    for cid in case_ids:
        rows = routes[cid]
        if not isinstance(rows, list) or not rows:
            raise ValueError("unassigned test-method selection: " + cid)
        seen = set()
        chosen = []
        for row in rows:
            if not isinstance(row, list) or len(row) != 3:
                raise ValueError("malformed test-method route: " + cid)
            fname, method, role = row
            if (not isinstance(fname, str) or not fname.startswith("test_") or
                not fname.endswith(".py") or "/" in fname or "\\" in fname or
                not isinstance(method, str) or not method.startswith("test_") or
                role not in ROLES):
                raise ValueError("unsupported test-method identity: " + cid)
            if (fname, method) in seen:
                raise ValueError("duplicate candidate test-method route: " + cid)
            seen.add((fname, method))
            path = root / "verification" / "research" / fname
            if fname not in cache:
                if not path.is_file() or path.is_symlink():
                    raise ValueError("candidate test source missing: " + str(path))
                syntax = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
                cache[fname] = {
                    n.name for n in ast.walk(syntax)
                    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and n.name.startswith("test_")
                }
            if method not in cache[fname]:
                raise ValueError("candidate test-method absent: " + cid + "/" + fname + ":" + method)
            chosen.append({"path": "verification/research/" + fname,
                           "method": method, "role": role,
                           "status": "DISCOVERED_UNREVIEWED_NOT_EXECUTION_EVIDENCE"})
        selected[cid] = chosen
    return selected
