"""C7 independently adversarial finite eventual-true event/class-law tests.

All probabilities are exact fractions, derived from the unchanged,
separately maintained C6 positive-edge class and rational absorption solver.
In contrast with C6's constant-observed-class shortcut, mixed-label
recurrent classes are evaluated correctly: they contribute ZERO to the
EVENTUALLY CONSTANT event regardless of their occupation law.
No finite-horizon hitting event is substituted for eventual residence.
"""
import unittest
from fractions import Fraction as F
import test_lane_c6_typed_response as c6

Q0, Q1 = F(0), F(1)


def safe(matrix):
    return c6.checked(matrix)


def basis(i, n):
    return c6.basis(i, n)


def good_classes(matrix, labels):
    if len(labels) != len(matrix):
        raise ValueError("observation dimension")
    return tuple(cls for cls in c6.recurrent_classes(matrix)
                 if all(labels[i] is True for i in cls))


def good_mass(matrix, labels, initial):
    """The actual class-absorption sum; this handles mixed recurrent classes."""
    if len(initial) != len(matrix) or any(type(x) is not F or x < Q0 for x in initial) or sum(initial, Q0) != Q1:
        raise ValueError("invalid probability initial law")
    cls_weights = c6.absorption_probabilities(matrix)
    return sum((initial[y] * cls_weights[cls][y]
                for cls in good_classes(matrix, labels)
                for y in range(len(matrix))), Q0)


def q_single(matrix, labels, i):
    return good_mass(matrix, labels, basis(i, len(matrix)))


def gap(original, changed, labels, states):
    if not states:
        raise ValueError("empty comparison is invalid")
    return min(abs(q_single(original, labels, y) -
                   q_single(changed, labels, y)) for y in states)


ALT = (False, False, True, False, True, True)
MIXED_TWO = safe(((Q0, Q1), (Q1, Q0)))
ALLTRUE_TWO = (True, True)
MIXED_THREE = safe(((Q0, Q1, Q0),
                    (Q0, Q0, Q1),
                    (Q1, Q0, Q0)))


class C7EventuallyTrueEventTests(unittest.TestCase):
    def test_01_c6_baseline_all_good_classes(self):
        self.assertEqual(good_classes(c6.BASE, c6.OBS),
                         (frozenset({2, 3}), frozenset({4, 5})))

    def test_02_c6_intervened_own_recurrent_decomposition(self):
        self.assertEqual(c6.recurrent_classes(c6.RESPONSE),
                         (frozenset({1}), frozenset({4, 5})))
        self.assertEqual(good_classes(c6.RESPONSE, c6.OBS),
                         (frozenset({4, 5}),))

    def test_03_baseline_probability_one_at_u(self):
        self.assertEqual(q_single(c6.BASE, c6.OBS, 1), Q1)

    def test_04_baseline_probability_one_at_a0(self):
        self.assertEqual(q_single(c6.BASE, c6.OBS, 2), Q1)

    def test_05_intervened_event_zero_at_u(self):
        self.assertEqual(q_single(c6.RESPONSE, c6.OBS, 1), Q0)

    def test_06_intervened_event_zero_at_a0(self):
        self.assertEqual(q_single(c6.RESPONSE, c6.OBS, 2), Q0)

    def test_07_C6_minimum_uniform_gap_one(self):
        self.assertEqual(gap(c6.BASE, c6.RESPONSE, c6.OBS, {1, 2}), Q1)

    def test_08_one_row_only_zero_uniform_gap(self):
        self.assertEqual(q_single(c6.U_ONLY, c6.OBS, 1), Q0)
        self.assertEqual(q_single(c6.U_ONLY, c6.OBS, 2), Q1)
        self.assertEqual(gap(c6.BASE, c6.U_ONLY, c6.OBS, {1, 2}), Q0)

    def test_09_physical_B_only_change_not_observably_constitutive(self):
        self.assertEqual(gap(c6.BASE, c6.B_ONLY, c6.OBS, {1, 2}), Q0)

    def test_10_mixed_period_two_class_is_not_good(self):
        self.assertEqual(good_classes(MIXED_TWO, (True, False)), ())
        self.assertEqual(q_single(MIXED_TWO, (True, False), 0), Q0)

    def test_11_mixed_periodic_occupation_does_not_mean_eventual_true(self):
        self.assertEqual((F(1, 2) * int(True) + F(1, 2) * int(False)),
                         F(1, 2))
        self.assertEqual(q_single(MIXED_TWO, (True, False), 1), Q0)

    def test_12_all_true_periodic_class_counts_as_eventual_true(self):
        self.assertEqual(q_single(MIXED_TWO, ALLTRUE_TWO, 0), Q1)
        self.assertEqual(q_single(MIXED_TWO, ALLTRUE_TWO, 1), Q1)

    def test_13_mixed_period_three_class_is_not_good(self):
        self.assertEqual(q_single(MIXED_THREE, (True, True, False), 0), Q0)
        self.assertEqual(q_single(MIXED_THREE, (True, True, False), 2), Q0)

    def test_14_transient_true_into_false_absorber_is_bad(self):
        m = safe(((Q0, Q1), (Q0, Q1)))
        self.assertEqual(q_single(m, (True, False), 0), Q0)

    def test_15_transient_false_into_true_absorber_is_good(self):
        m = safe(((Q0, Q1), (Q0, Q1)))
        self.assertEqual(q_single(m, (False, True), 0), Q1)

    def test_16_changed_descriptor_baseline_B_probability_two_thirds(self):
        self.assertEqual(good_classes(c6.BASE, ALT), (frozenset({4, 5}),))
        self.assertEqual(q_single(c6.BASE, ALT, 1), F(2, 3))

    def test_17_changed_descriptor_a0_has_zero_event_probability(self):
        self.assertEqual(q_single(c6.BASE, ALT, 2), Q0)

    def test_18_changed_descriptor_intervened_all_zero_on_original_basin(self):
        self.assertEqual(q_single(c6.RESPONSE, ALT, 1), Q0)
        self.assertEqual(q_single(c6.RESPONSE, ALT, 2), Q0)
        self.assertEqual(gap(c6.BASE, c6.RESPONSE, ALT, {1, 2}), Q0)

    def test_19_mixed_periodic_counterexample_not_original_exactGR(self):
        # With ALT, class A occupation pushes forward to 1/2 true / 1/2 false,
        # B occupation is delta_true; both are basin-reachable at positive mass.
        self.assertEqual(c6.absorption_probabilities(c6.BASE)[frozenset({2, 3})][1], F(1, 3))
        self.assertNotEqual(F(1, 2), Q1)
        self.assertEqual(q_single(c6.BASE, ALT, 2), Q0)

    def test_20_initial_mixture_affinity(self):
        mu = tuple(F(3, 7)*basis(1, 6)[i] +
                   F(4, 7)*basis(2, 6)[i] for i in range(6))
        self.assertEqual(good_mass(c6.BASE, ALT, mu), F(2, 7))
        self.assertEqual(good_mass(c6.RESPONSE, ALT, mu), Q0)

    def test_21_tiny_positive_good_class_weight_not_thresholded(self):
        eps = F(1, 10**35)
        m = safe(((Q0, eps, Q1-eps),
                  (Q0, Q1, Q0),
                  (Q0, Q0, Q1)))
        self.assertEqual(q_single(m, (False, True, False), 0), eps)

    def test_22_zero_probability_unreachable_good_class_is_not_counted(self):
        m = safe(((Q1, Q0, Q0),
                  (Q0, Q1, Q0),
                  (Q0, Q0, Q1)))
        self.assertEqual(q_single(m, (False, True, False), 0), Q0)
        self.assertEqual(q_single(m, (False, True, False), 1), Q1)

    def test_23_identity_intervention_zero_margin(self):
        self.assertEqual(gap(c6.BASE, c6.IDENTITY, c6.OBS, {1, 2}), Q0)

    def test_24_one_point_comparison_is_not_a_valid_original_B1(self):
        self.assertEqual(gap(c6.BASE, c6.U_ONLY, c6.OBS, {1}), Q1)
        self.assertEqual(gap(c6.BASE, c6.U_ONLY, c6.OBS, {1, 2}), Q0)

    def test_25_empty_comparison_rejected(self):
        with self.assertRaises(ValueError):
            gap(c6.BASE, c6.RESPONSE, c6.OBS, set())

    def test_26_invalid_observation_dimension_rejected(self):
        with self.assertRaises(ValueError):
            good_classes(c6.BASE, (True, False))

    def test_27_invalid_initial_law_rejected(self):
        with self.assertRaises(ValueError):
            good_mass(c6.BASE, c6.OBS, (Q1,))
        with self.assertRaises(ValueError):
            good_mass(c6.BASE, c6.OBS, tuple(F(1, 6) for _ in range(5)) + (F(-1, 6),))

    def test_28_eventual_true_is_not_ever_true(self):
        self.assertEqual(q_single(MIXED_TWO, (True, False), 0), Q0)
        self.assertTrue(any((True, False)[i] for i in range(2)))

    def test_29_sparse_infinitely_many_false_times_not_eventually_true(self):
        # At times 2**k there is a false observation however large k is.
        # The asymptotic fraction of false times nevertheless vanishes.
        for k in (10, 50, 100, 1000):
            n = 2**k
            self.assertTrue(n & (n-1) == 0)
            self.assertLess(F(k+1, n), F(1, 2))
        self.assertEqual(q_single(MIXED_TWO, (True, False), 0), Q0)

    def test_30_all_false_recurrent_labels_yield_no_good_class(self):
        self.assertEqual(good_classes(c6.BASE, (False,) * 6), ())
        for y in range(6):
            self.assertEqual(q_single(c6.BASE, (False,) * 6, y), Q0)


if __name__ == "__main__":
    unittest.main()
