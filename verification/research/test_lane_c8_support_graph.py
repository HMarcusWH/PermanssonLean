"""C8 support-graph qualitative constitution: independent exact-Fraction adversaries.

This script transcribes finite transition rows and graph reachability
directly. It is a computation/falsification suite, not the Lean proof
of any almost-sure canonical path property. Exact probability only.
"""
import unittest
from fractions import Fraction as F
import test_lane_c6_typed_response as c6

Z, O = F(0), F(1)
LABEL = (False, False, False, True, False)
STARTS = frozenset((1, 2))


def checked(rows):
    return c6.checked(rows)


def baseline():
    return checked(((Z, O, Z, Z, Z),
                    (Z, Z, Z, O, Z),
                    (Z, Z, Z, O, Z),
                    (Z, Z, Z, O, Z),
                    (Z, Z, Z, Z, O)))


def response(eu, ev=None):
    eu, ev = F(eu), F(eu if ev is None else ev)
    if not (Z <= eu <= O and Z <= ev <= O):
        raise ValueError("invalid response probability")
    return checked(((Z, O, Z, Z, Z),
                    (Z, Z, Z, O-eu, eu),
                    (Z, Z, Z, O-ev, ev),
                    (Z, Z, Z, O, Z),
                    (Z, Z, Z, Z, O)))


BASE = baseline()
HALF = response(F(1, 2))
TINY = response(F(1, 1000))
ONE_ROW = response(F(1, 2), Z)
EPS35 = response(F(1, 10**35))


def good(cls, labels):
    return all(labels[x] is True for x in cls)


def closed_classes(matrix):
    return tuple(c6.recurrent_classes(matrix))


def class_weight(matrix, y, cls):
    return c6.absorption_probabilities(matrix)[cls][y]


def graph_reaches_class(matrix, y, cls):
    return bool(c6.reachable(matrix, y).intersection(cls))


def good_reachable(matrix, labels, y):
    return any(good(cls, labels) and graph_reaches_class(matrix, y, cls)
               for cls in closed_classes(matrix))


def bad_reachable(matrix, labels, y):
    return any(not good(cls, labels) and graph_reaches_class(matrix, y, cls)
               for cls in closed_classes(matrix))


def event_prob(matrix, labels, y):
    return sum((class_weight(matrix, y, cls)
                for cls in closed_classes(matrix) if good(cls, labels)), Z)


def opposite_mass(matrix, labels, y, baseline_true):
    return sum((class_weight(matrix, y, cls)
                for cls in closed_classes(matrix)
                if good(cls, labels) is not baseline_true), Z)


def margin(baseline_matrix, response_matrix, labels, starts):
    if len(starts) < 2:
        raise ValueError("original constitutive comparison needs distinct starts")
    return min((abs(event_prob(baseline_matrix, labels, y)
                    - event_prob(response_matrix, labels, y))
                for y in starts))


def support(matrix):
    return tuple(tuple(x > Z for x in row) for row in matrix)


def support_pr(matrix, labels, starts, target_is_true):
    opposite = bad_reachable if target_is_true else good_reachable
    return all(opposite(matrix, labels, y) for y in starts)


class C8SupportGraphTests(unittest.TestCase):
    def test_01_baseline_rows_normalized(self):
        self.assertEqual(checked(BASE), BASE)

    def test_02_half_rows_normalized(self):
        self.assertEqual(checked(HALF), HALF)

    def test_03_tiny_rows_normalized(self):
        self.assertEqual(checked(TINY), TINY)

    def test_04_same_support_for_distinct_probabilities(self):
        self.assertEqual(support(HALF), support(TINY))

    def test_05_different_probabilities_same_graph(self):
        self.assertNotEqual(HALF, TINY)

    def test_06_closed_classes_baseline(self):
        self.assertEqual(closed_classes(BASE), (frozenset({3}), frozenset({4})))

    def test_07_closed_classes_response(self):
        self.assertEqual(closed_classes(HALF), closed_classes(BASE))

    def test_08_baseline_event_probability_one_from_u(self):
        self.assertEqual(event_prob(BASE, LABEL, 1), O)

    def test_09_baseline_event_probability_one_from_v(self):
        self.assertEqual(event_prob(BASE, LABEL, 2), O)

    def test_10_baseline_from_false_transient_t_is_eventually_true(self):
        self.assertEqual(event_prob(BASE, LABEL, 0), O)

    def test_11_good_destination_reachable_iff_positive_probability(self):
        for model in (BASE, HALF, TINY, ONE_ROW, EPS35):
            for y in range(5):
                self.assertEqual(event_prob(model, LABEL, y) > Z,
                                 good_reachable(model, LABEL, y))

    def test_12_bad_destination_reachable_iff_prob_below_one(self):
        for model in (BASE, HALF, TINY, ONE_ROW, EPS35):
            for y in range(5):
                self.assertEqual(event_prob(model, LABEL, y) < O,
                                 bad_reachable(model, LABEL, y))

    def test_13_half_effect_at_u(self):
        self.assertEqual(abs(event_prob(BASE, LABEL, 1) -
                             event_prob(HALF, LABEL, 1)), F(1, 2))

    def test_14_half_effect_at_v(self):
        self.assertEqual(abs(event_prob(BASE, LABEL, 2) -
                             event_prob(HALF, LABEL, 2)), F(1, 2))

    def test_15_half_margin(self):
        self.assertEqual(margin(BASE, HALF, LABEL, STARTS), F(1, 2))

    def test_16_thousandth_margin(self):
        self.assertEqual(margin(BASE, TINY, LABEL, STARTS), F(1, 1000))

    def test_17_same_graph_does_not_preserve_margin(self):
        self.assertEqual(support(HALF), support(TINY))
        self.assertNotEqual(margin(BASE, HALF, LABEL, STARTS),
                            margin(BASE, TINY, LABEL, STARTS))

    def test_18_both_same_graph_interventions_qualitatively_constitutive(self):
        self.assertTrue(support_pr(HALF, LABEL, STARTS, True))
        self.assertTrue(support_pr(TINY, LABEL, STARTS, True))

    def test_19_one_row_only_not_uniform(self):
        self.assertEqual(margin(BASE, ONE_ROW, LABEL, STARTS), Z)
        self.assertFalse(support_pr(ONE_ROW, LABEL, STARTS, True))

    def test_20_opposite_mass_matches_effect_at_u(self):
        for m in (HALF, TINY, ONE_ROW, EPS35):
            self.assertEqual(opposite_mass(m, LABEL, 1, True),
                             abs(event_prob(BASE, LABEL, 1) -
                                 event_prob(m, LABEL, 1)))

    def test_21_opposite_mass_matches_effect_at_v(self):
        for m in (HALF, TINY, ONE_ROW, EPS35):
            self.assertEqual(opposite_mass(m, LABEL, 2, True),
                             abs(event_prob(BASE, LABEL, 2) -
                                 event_prob(m, LABEL, 2)))

    def test_22_tiny_positive_graph_edge_is_not_zero(self):
        self.assertEqual(event_prob(EPS35, LABEL, 1), O-F(1, 10**35))
        self.assertTrue(bad_reachable(EPS35, LABEL, 1))
        self.assertEqual(margin(BASE, EPS35, LABEL, STARTS), F(1, 10**35))

    def test_23_unreachable_bad_absorber_does_not_impact_original(self):
        self.assertFalse(bad_reachable(BASE, LABEL, 1))
        self.assertFalse(bad_reachable(BASE, LABEL, 2))

    def test_24_positive_absorbing_bad_state_obstructs_if_started_there(self):
        self.assertEqual(event_prob(BASE, LABEL, 4), Z)
        self.assertTrue(bad_reachable(BASE, LABEL, 4))

    def test_25_original_comparison_rejects_single_state(self):
        with self.assertRaises(ValueError):
            margin(BASE, HALF, LABEL, {1})

    def test_26_mixed_period_two_not_eventually_true(self):
        model = checked(((Z,O),(O,Z)))
        self.assertEqual(event_prob(model, (True, False), 0), Z)
        self.assertFalse(good_reachable(model, (True, False), 0))
        self.assertTrue(bad_reachable(model, (True, False), 0))

    def test_27_all_true_period_two_reachable(self):
        model = checked(((Z,O),(O,Z)))
        self.assertEqual(event_prob(model, (True, True), 0), O)

    def test_28_no_graph_qualitative_invariance_without_extreme_baseline(self):
        weak_base = response(F(1, 2))
        change = response(F(1, 4))
        same = response(F(1, 2))
        self.assertEqual(support(change), support(same))
        self.assertEqual(abs(event_prob(weak_base,LABEL,1)-
                             event_prob(same,LABEL,1)), Z)
        self.assertEqual(abs(event_prob(weak_base,LABEL,1)-
                             event_prob(change,LABEL,1)), F(1,4))

    def test_29_false_target_branch_opposite_is_good(self):
        self.assertTrue(support_pr(BASE, LABEL, STARTS, False))
        self.assertEqual(opposite_mass(BASE,LABEL,1,False), O)

    def test_30_stochastic_probabilities_affect_magnitude_not_reachability(self):
        for m in (HALF,TINY,EPS35):
            self.assertTrue(bad_reachable(m,LABEL,1))
            self.assertTrue(bad_reachable(m,LABEL,2))
            self.assertTrue(support_pr(m,LABEL,STARTS,True))

    def test_31_zero_transition_does_not_count_as_reachable(self):
        self.assertFalse(bad_reachable(ONE_ROW,LABEL,2))
        self.assertEqual(event_prob(ONE_ROW,LABEL,2), O)

    def test_32_two_absorbers_not_interchangeable_labels(self):
        self.assertEqual(event_prob(HALF,LABEL,3), O)
        self.assertEqual(event_prob(HALF,LABEL,4), Z)

    def test_33_graph_invariance_persists_for_false_transient_prefix(self):
        self.assertTrue(bad_reachable(HALF,LABEL,0))
        self.assertTrue(bad_reachable(TINY,LABEL,0))

    def test_34_invalid_probabilities_rejected(self):
        with self.assertRaises(ValueError):
            response(F(-1,100))
        with self.assertRaises(ValueError):
            response(F(101,100))

    def test_35_event_probability_never_conflates_with_barycenter(self):
        model = checked(((Z,O),(O,Z)))
        self.assertEqual(event_prob(model,(True,False),0),Z)
        self.assertEqual(F(1,2)*O+F(1,2)*Z,F(1,2))


if __name__ == "__main__":
    unittest.main()
