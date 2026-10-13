"""C9 independent exact-Fraction finite-menu constitution adversaries.

This tests the C9 mathematical objective and a reference rational oracle,
NOT evaluation of a noncomputable Lean Classical.choose and NOT a verified
executable infinite-horizon C9 optimizer. Structural support is screened
using exact rational graph edges; class weights are independently computed
by the existing C6 exact Gauss-Jordan absorption solver.
"""
from fractions import Fraction as F
import unittest

import test_lane_c6_typed_response as c6
import test_lane_c8_support_graph as c8

Z, O = F(0), F(1)
BASE, FULL = c6.BASE, c6.RESPONSE
HALF, TINY = c8.SIX_HALF, c8.SIX_TINY
U_ONLY, B_ONLY = c6.U_ONLY, c6.B_ONLY
BASIN, OBS = c6.BASIN, c6.OBS


def valid_menu(entries):
    """An ordered finite list; a repeated INDEX has only one assigned matrix."""
    if not entries:
        raise ValueError("empty frozen menu")
    out = {}
    for label, matrix in entries:
        c6.checked(matrix)
        if label in out and out[label] != matrix:
            raise ValueError("conflicting matrix for one fixed index")
        if label not in out:
            out[label] = matrix
    return out


def assert_frozen_basin(states):
    if frozenset(states) != BASIN:
        raise ValueError("not the original B1")


def eligible_matrix(matrix, starts=BASIN, obs=OBS, target_true=True):
    chooser = c8.bad_reachable if target_true else c8.good_reachable
    return all(chooser(matrix, obs, y) for y in starts)


def original_margin(matrix, starts=BASIN, obs=OBS):
    assert_frozen_basin(starts)
    return min((abs(c6.observed_limit_probability(BASE, c6.basis(y), obs) -
                    c6.observed_limit_probability(matrix, c6.basis(y), obs))
                for y in starts))


def support_screen(menu, starts=BASIN):
    assert_frozen_basin(starts)
    return {i for i, matrix in menu.items()
            if eligible_matrix(matrix, starts)}


def sample_certificate(menu, baseline_proof="missing", literal_mode=True):
    """EVIDENCE-STATUS oracle for tests; not automatic discovery of Exact GR."""
    if baseline_proof == "missing":
        return ("BASELINE_UNVERIFIED", None)
    if baseline_proof == "refuted":
        return ("BASELINE_REFUTED_WITH_PROOF", None)
    if baseline_proof != "certified" or not literal_mode:
        return ("MODE_OR_BASELINE_UNVERIFIED", None)
    eligible = support_screen(menu)
    if not eligible:
        return ("LISTED_INFEASIBLE", set())
    return ("LISTED_FEASIBLE", eligible)


def six_reverse_only_a0_bad():
    """A countermodel: A0 reaches false 0; u goes directly to good B."""
    rows = [list(r) for r in BASE]
    rows[0] = list(c6.basis(0))
    rows[1] = list(c6.basis(4))
    rows[2] = list(c6.basis(0))
    return c6.checked(rows)


REVERSE = six_reverse_only_a0_bad()
EPS35 = c8.SIX_EPS35


class C9CertifiedMenuReferenceTests(unittest.TestCase):
    def test_01_accept_nonempty_frozen_menu(self):
        self.assertEqual(len(valid_menu([("half", HALF)])), 1)

    def test_02_duplicate_same_index_collapses(self):
        self.assertEqual(len(valid_menu([("h", HALF), ("h", HALF)])), 1)

    def test_03_duplicate_index_conflict_rejected(self):
        with self.assertRaises(ValueError):
            valid_menu([("h", HALF), ("h", TINY)])

    def test_04_distinct_indices_same_kernel_preserved(self):
        self.assertEqual(len(valid_menu([("a", HALF), ("b", HALF)])), 2)

    def test_05_unlisted_good_interventions_not_considered(self):
        self.assertEqual(support_screen(valid_menu([("identity", BASE)])), set())

    def test_06_proved_baseline_accepts_real_positive_witness(self):
        state, out = sample_certificate(valid_menu([("full", FULL)]),
                                        baseline_proof="certified")
        self.assertEqual((state, out), ("LISTED_FEASIBLE", {"full"}))

    def test_07_missing_GR_proof_is_not_a_negative_GR_result(self):
        self.assertEqual(sample_certificate(valid_menu([("full", FULL)]))[0],
                         "BASELINE_UNVERIFIED")

    def test_08_explicit_GR_refutation_has_separate_status(self):
        self.assertEqual(sample_certificate(valid_menu([("full", FULL)]),
                                            baseline_proof="refuted")[0],
                         "BASELINE_REFUTED_WITH_PROOF")

    def test_09_nonliteral_mode_not_certified_as_C8_result(self):
        self.assertEqual(sample_certificate(valid_menu([("full", FULL)]),
                                            baseline_proof="certified",
                                            literal_mode=False)[0],
                         "MODE_OR_BASELINE_UNVERIFIED")

    def test_10_no_arbitrary_external_model_rational_bridging(self):
        # The D0 adapter requires the constructed alpha/P/U type.
        with self.assertRaises(ValueError):
            valid_menu([("external", ((F(1), F(1)), (Z, O)))])

    def test_11_all_structurally_ineligible_menu(self):
        self.assertEqual(support_screen(valid_menu([
            ("id", BASE), ("one", U_ONLY), ("physical", B_ONLY)])), set())

    def test_12_exactly_one_structurally_eligible(self):
        self.assertEqual(support_screen(valid_menu([
            ("id", BASE), ("half", HALF)])), {"half"})

    def test_13_three_eligible_members(self):
        self.assertEqual(support_screen(valid_menu([
            ("full", FULL), ("half", HALF), ("tiny", TINY)])),
            {"full", "half", "tiny"})

    def test_14_empty_filtered_set_is_not_empty_frozen_menu(self):
        self.assertTrue(valid_menu([("id", BASE)]))
        self.assertFalse(support_screen(valid_menu([("id", BASE)])))

    def test_15_existence_witness_iff_eligible_nonempty_for_valid_GR(self):
        for cases in ([("id", BASE)], [("h", HALF)],
                      [("f", FULL), ("t", TINY)]):
            menu = valid_menu(cases)
            status, members = sample_certificate(menu, "certified")
            self.assertEqual(status == "LISTED_FEASIBLE",
                             bool(support_screen(menu)))
            self.assertEqual(bool(members), bool(support_screen(menu)))

    def test_16_family_can_have_PR_when_declared_menu_is_negative(self):
        self.assertEqual(support_screen(valid_menu([("id", BASE)])), set())
        self.assertTrue(eligible_matrix(FULL))

    def test_17_ineligible_means_zero_margin_in_valid_original_baseline(self):
        for m in (BASE, U_ONLY, B_ONLY):
            self.assertFalse(eligible_matrix(m))
            self.assertEqual(original_margin(m), Z)

    def test_18_one_row_u_only_fails_at_original_a0(self):
        self.assertTrue(c8.bad_reachable(U_ONLY, OBS, 1))
        self.assertFalse(c8.bad_reachable(U_ONLY, OBS, 2))

    def test_19_reverse_only_a0_bad_not_u(self):
        self.assertTrue(c8.bad_reachable(REVERSE, OBS, 2))
        self.assertFalse(c8.bad_reachable(REVERSE, OBS, 1))

    def test_20_both_states_reach_bad_for_half(self):
        self.assertTrue(all(c8.bad_reachable(HALF, OBS, y) for y in BASIN))

    def test_21_two_point_original_comparison_required(self):
        self.assertEqual(BASIN, frozenset({1, 2}))
        self.assertFalse(eligible_matrix(U_ONLY, BASIN))

    def test_22_posthoc_singleton_not_original_B1(self):
        with self.assertRaises(ValueError):
            original_margin(U_ONLY, {1})

    def test_23_half_and_tiny_have_equal_support(self):
        self.assertEqual(c8.support(HALF), c8.support(TINY))

    def test_24_different_actual_margins_on_same_support(self):
        self.assertEqual(original_margin(HALF), F(1, 2))
        self.assertEqual(original_margin(TINY), F(1, 1000))

    def test_25_full_disruption_attains_upper_bound_one(self):
        self.assertEqual(original_margin(FULL), O)

    def test_26_positive_one_over_ten_to_35_is_not_zero(self):
        self.assertTrue(eligible_matrix(EPS35))
        self.assertEqual(original_margin(EPS35), F(1, 10**35))

    def test_27_exact_zero_edges_do_not_create_reachability(self):
        self.assertFalse(c8.bad_reachable(BASE, OBS, 2))
        self.assertFalse(c8.bad_reachable(U_ONLY, OBS, 2))

    def test_28_support_grouping_cannot_drop_best_probability_candidate(self):
        self.assertEqual(c8.support(HALF), c8.support(TINY))
        self.assertGreater(original_margin(HALF), original_margin(TINY))

    def test_29_transient_false_prefix_not_bad_class(self):
        self.assertEqual(c8.event_prob(BASE, OBS, 0), O)

    def test_30_mixed_period_two_recurrent_class_is_bad(self):
        m = c6.checked(((Z, O), (O, Z)))
        self.assertEqual(c8.event_prob(m, (True, False), 0), Z)

    def test_31_all_true_periodic_class_is_good(self):
        m = c6.checked(((Z, O), (O, Z)))
        self.assertEqual(c8.event_prob(m, (True, True), 0), O)

    def test_32_unreachable_bad_class_does_not_disqualify(self):
        self.assertFalse(c8.bad_reachable(BASE, OBS, 1))
        self.assertEqual(original_margin(BASE), Z)

    def test_33_kernel_specific_classes_not_interchanged(self):
        self.assertNotEqual(c6.recurrent_classes(BASE),
                            c6.recurrent_classes(FULL))

    def test_34_half_one_step_hitting_goal_4(self):
        self.assertEqual(HALF[2][4], F(1, 2))

    def test_35_tiny_one_step_hitting_goal_4(self):
        self.assertEqual(TINY[2][4], F(999, 1000))

    def test_36_full_disruption_one_step_hitting_goal_4(self):
        self.assertEqual(FULL[2][4], Z)

    def test_37_one_step_D0_ranking_reverses_C9_margin_ranking(self):
        self.assertGreater(TINY[2][4], HALF[2][4])
        self.assertLess(original_margin(TINY), original_margin(HALF))

    def test_38_listed_negative_excludes_only_listed_members(self):
        menu = valid_menu([("id", BASE), ("one", U_ONLY)])
        self.assertEqual(sample_certificate(menu, "certified")[0],
                         "LISTED_INFEASIBLE")
        self.assertTrue(eligible_matrix(FULL))

    def test_39_missing_baseline_does_not_yield_listed_infeasible(self):
        menu = valid_menu([("id", BASE)])
        self.assertEqual(sample_certificate(menu)[0], "BASELINE_UNVERIFIED")

    def test_40_graph_equivalence_does_not_prove_margin_equality(self):
        self.assertEqual(c8.support(HALF), c8.support(TINY))
        self.assertNotEqual(original_margin(HALF), original_margin(TINY))

    def test_41_evidence_is_not_empirical_identification(self):
        label, _ = sample_certificate(valid_menu([("f", FULL)]), "certified")
        self.assertEqual(label, "LISTED_FEASIBLE")
        self.assertNotIn("EMPIRICAL", label)

    def test_42_empty_input_menu_rejected(self):
        with self.assertRaises(ValueError):
            valid_menu([])

    def test_43_alpha_only_semantics_preserve_unedited_rows(self):
        for m in (HALF, TINY):
            self.assertEqual(m[0], BASE[0])
            self.assertEqual(m[3:], BASE[3:])

    def test_44_descriptor_and_original_basin_stay_frozen(self):
        self.assertEqual(OBS, (False, False, True, True, True, True))
        self.assertEqual(BASIN, frozenset({1, 2}))

    def test_45_original_baseline_is_constitutively_extremal(self):
        self.assertTrue(all(c6.observed_limit_probability(BASE, c6.basis(y)) == O
                            for y in BASIN))

    def test_46_margin_global_argmax_actual_scores(self):
        menu = valid_menu([("half", HALF), ("tiny", TINY), ("full", FULL)])
        margins = {i: original_margin(m) for i,m in menu.items()}
        self.assertEqual(margins["full"], max(margins.values()))
        self.assertEqual(margins["full"], O)

    def test_47_tied_indices_do_not_claim_unique_margin_optimum(self):
        menu = valid_menu([("a", FULL), ("b", FULL)])
        margins = {i: original_margin(m) for i,m in menu.items()}
        self.assertEqual(margins["a"], margins["b"])

    def test_48_inequality_over_all_listed_including_ineligible(self):
        menu = valid_menu([("id", BASE), ("one", U_ONLY), ("half", HALF),
                           ("tiny", TINY), ("full", FULL)])
        self.assertTrue(all(original_margin(m) <= original_margin(FULL)
                            for m in menu.values()))

    def test_49_rational_positive_edge_is_exact(self):
        self.assertGreater(TINY[2][1], Z)
        self.assertEqual(BASE[2][1], Z)

    def test_50_typed_member_world_update_guarantees_are_constructed_only(self):
        # C9 Lean proves this via D0 alpha-only constructions; the
        # independent oracle verifies only which transition rows differ.
        self.assertNotEqual(FULL, BASE)
        self.assertTrue(eligible_matrix(FULL))


if __name__ == "__main__":
    unittest.main()
