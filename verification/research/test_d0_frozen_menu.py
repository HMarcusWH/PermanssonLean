"""Adversarial D0 frozen-menu solver tests with exact rational probabilities."""
import itertools
import math
from dataclasses import replace
import unittest
from fractions import Fraction as Q

from d0_finite_solver import (
    prefix_law, value_by_enumeration, value_by_recursion, solve_frozen_menu,
    validate_kernel, verify_frozen_menu_result,
)

# 0 = starting state, 1 = goal, 2 = forbidden.
G, D = {1}, {2}
A = (
    (Q(1,2), Q(1,2), Q(0)),
    (Q(0), Q(1), Q(0)),
    (Q(0), Q(0), Q(1)),
)
B = (
    (Q(0), Q(3,4), Q(1,4)),
    (Q(0), Q(1), Q(0)),
    (Q(0), Q(0), Q(1)),
)
C = (
    (Q(1,4), Q(1,4), Q(1,2)),
    (Q(0), Q(1), Q(0)),
    (Q(0), Q(0), Q(1)),
)
STAY = (
    (Q(1), Q(0), Q(0)),
    (Q(0), Q(1), Q(0)),
    (Q(0), Q(0), Q(1)),
)
DANGER = (
    (Q(0), Q(0), Q(1)),
    (Q(0), Q(1), Q(0)),
    (Q(0), Q(0), Q(1)),
)


class D0FixedMenuTests(unittest.TestCase):
    def test_exact_recursion_agrees_with_full_forward_path_enumeration(self):
        for K, initial, T in itertools.product((A, B, C, STAY, DANGER), range(3), range(6)):
            self.assertEqual(value_by_recursion(K, initial, G, D, T),
                             value_by_enumeration(K, initial, G, D, T))
            self.assertEqual(sum(prefix_law(K, initial, T).values(), Q(0)), 1)

    def test_horizon_zero_and_initial_membership(self):
        self.assertEqual(value_by_recursion(B, 1, G, D, 0), 1)
        self.assertEqual(value_by_recursion(B, 2, G, D, 0), 0)
        self.assertEqual(value_by_recursion(B, 0, G, D, 0), 0)

    def test_forbidden_entry_precedes_later_goal(self):
        K = (
            (Q(0), Q(0), Q(1)),
            (Q(0), Q(1), Q(0)),
            (Q(0), Q(1), Q(0)),
        )
        self.assertEqual(value_by_recursion(K, 0, G, D, 2), 0)
        self.assertEqual(value_by_enumeration(K, 0, G, D, 2), 0)

    def test_best_fixed_menu_member(self):
        out = solve_frozen_menu([("A", A), ("B", B), ("C", C)], 0, G, D, 1)
        self.assertEqual(out.selected, "B")
        self.assertEqual(out.value, Q(3, 4))
        self.assertEqual(dict(out.values)["A"], Q(1, 2))
        self.assertTrue(all(x <= out.value for _, x in out.values))

    def test_optimality_is_horizon_specific(self):
        out = solve_frozen_menu([("A", A), ("B", B)], 0, G, D, 3)
        self.assertEqual(out.selected, "A")
        self.assertEqual(out.value, Q(7, 8))

    def test_ties_resolved_by_frozen_menu_order(self):
        out = solve_frozen_menu([("first", B), ("second", B)], 0, G, D, 2)
        self.assertEqual(out.selected, "first")

    def test_no_selected_menu_members_reach_goal(self):
        out = solve_frozen_menu([("stay", STAY), ("danger", DANGER)], 0, G, D, 5)
        self.assertEqual(out.value, 0)
        self.assertTrue(all(v == 0 for _, v in out.values))
        # This says nothing about an unlisted intervention, including B.

    def test_sampling_false_negative_does_not_prove_unreachability(self):
        sampled = solve_frozen_menu([("stay", STAY)], 0, G, D, 1)
        complete = solve_frozen_menu([("stay", STAY), ("good", B)], 0, G, D, 1)
        self.assertEqual(sampled.value, 0)
        self.assertEqual(complete.value, Q(3, 4))

    def test_no_baseline_unless_explicitly_listed(self):
        only_B = solve_frozen_menu([("replacement_B", B)], 0, G, D, 1)
        self.assertEqual(tuple(name for name, _ in only_B.values), ("replacement_B",))

    def test_disjointness_and_row_stochastic_gates(self):
        with self.assertRaises(ValueError):
            solve_frozen_menu([], 0, G, D, 1)
        with self.assertRaises(ValueError):
            solve_frozen_menu([("A", A)], 0, {1, 2}, {2}, 1)
        with self.assertRaises(ValueError):
            solve_frozen_menu([("bad", ((Q(1,2), Q(0)),(Q(0),Q(1))))], 0, {1}, set(), 1)
        with self.assertRaises(ValueError):
            solve_frozen_menu([("A", A), ("A", B)], 0, G, D, 1)
        self.assertEqual(validate_kernel(A), 3)


    def test_exact_input_firewall(self):
        """Untrusted floats must not be mislabeled exact-rational results."""
        bad_entries = (0.5, float("nan"), float("inf"), True, "1/2", 0.0)
        for p in bad_entries:
            with self.subTest(p=repr(p)):
                rows = ((p, Q(1)), (Q(0), Q(1)))
                with self.assertRaises(ValueError):
                    validate_kernel(rows)
        self.assertEqual(validate_kernel(((1, 0), (Q(1, 3), Q(2, 3)))), 2)
        self.assertEqual(type(value_by_recursion(A, 0, G, D, 4)), Q)
        for h in (-1, 1.0, True):
            with self.assertRaises(ValueError):
                value_by_recursion(A, 0, G, D, h)
        for s in (False, 0.0, Q(0)):
            with self.assertRaises(ValueError):
                value_by_recursion(A, s, G, D, 1)
        with self.assertRaises(ValueError):
            value_by_recursion(A, 0, {True}, D, 1)

    def test_exact_forward_backward_exhaustive_three_state_tables(self):
        """Exhaustively sample every 3x3 row built from halves and integers."""
        row_options = []
        for a in (Q(0), Q(1, 2), Q(1)):
            for b in (Q(0), Q(1, 2), Q(1)):
                c = Q(1) - a - b
                if c in (Q(0), Q(1, 2), Q(1)):
                    row_options.append((a, b, c))
        for matrix in itertools.product(row_options, repeat=3):
            for start in range(3):
                for horizon in range(4):
                    self.assertEqual(
                        value_by_recursion(matrix, start, G, D, horizon),
                        value_by_enumeration(matrix, start, G, D, horizon),
                    )


    def test_independent_exact_report_rechecker(self):
        menu = [("A", A), ("B", B), ("C", C)]
        for T in range(4):
            result = solve_frozen_menu(menu, 0, G, D, T)
            self.assertTrue(verify_frozen_menu_result(menu, 0, G, D, T, result))
            self.assertFalse(verify_frozen_menu_result(menu, 0, G, D, T,
                replace(result, value=result.value + Q(1, 7))))
            self.assertFalse(verify_frozen_menu_result(menu, 0, G, D, T,
                replace(result, selected="unlisted")))
            self.assertFalse(verify_frozen_menu_result(menu, 0, G, D, T,
                replace(result, values=result.values[:-1])))
            self.assertFalse(verify_frozen_menu_result(menu, 0, G, D, T,
                replace(result, value=float(result.value))))
        tied = [("first", B), ("second", B)]
        result = solve_frozen_menu(tied, 0, G, D, 2)
        self.assertTrue(verify_frozen_menu_result(tied, 0, G, D, 2, result))
        self.assertFalse(verify_frozen_menu_result(tied, 0, G, D, 2,
            replace(result, selected="second")))



    def test_shared_state_space_menu(self):
        two = ((Q(0), Q(1)), (Q(0), Q(1)))
        for menu in ([("three", A), ("two", two)],
                     [("two", two), ("three", A)]):
            with self.assertRaisesRegex(ValueError, "share one state space"):
                solve_frozen_menu(menu, 0, {1}, set(), 1)
            with self.assertRaisesRegex(ValueError, "share one state space"):
                verify_frozen_menu_result(menu, 0, {1}, set(), 1,
                    solve_frozen_menu([("three", A)], 0, {1}, set(), 1))

    def test_single_use_target_iterables(self):
        g = lambda: (x for x in [1])
        d = lambda: (x for x in [2])
        self.assertEqual(value_by_recursion(A, 0, g(), d(), 1), Q(1, 2))
        self.assertEqual(value_by_enumeration(A, 0, g(), d(), 1), Q(1, 2))
        menu = [("A", A), ("B", B)]
        reported = solve_frozen_menu(menu, 0, g(), d(), 1)
        self.assertEqual(reported.selected, "B")
        self.assertEqual(reported.value, Q(3, 4))
        self.assertTrue(verify_frozen_menu_result(menu, 0, g(), d(), 1, reported))
        with self.assertRaisesRegex(ValueError, "disjoint"):
            solve_frozen_menu(menu, 0, (x for x in [1]), (x for x in [1]), 1)
        # Discarding duplicates must not erase malformed Boolean indices.
        with self.assertRaisesRegex(ValueError, "indices must be integers"):
            value_by_recursion(A, 0, (x for x in [1, True]), d(), 1)

    def test_report_scope_is_part_of_integrity_contract(self):
        out = solve_frozen_menu([("A", A), ("B", B)], 0, G, D, 2)
        self.assertTrue(verify_frozen_menu_result([("A", A), ("B", B)], 0, G, D, 2, out))
        for forged in ("PROVED_OPTIMUM", "EXACT_PR", "", None):
            with self.subTest(scope=forged):
                self.assertFalse(verify_frozen_menu_result(
                    [("A", A), ("B", B)], 0, G, D, 2,
                    replace(out, scope=forged)))

    def test_disjoint_target_forbidden_partitions(self):
        # Every state is goal, forbidden or neither; each pair is disjoint.
        # Keep the exhaustive matrix search in the separate fixed-target test.
        for classification in itertools.product(range(3), repeat=3):
            goal = {i for i, label in enumerate(classification) if label == 1}
            forbidden = {i for i, label in enumerate(classification) if label == 2}
            for kernel, start, horizon in itertools.product(
                    (A, B, C, STAY, DANGER), range(3), range(4)):
                self.assertEqual(
                    value_by_recursion(kernel, start, goal, forbidden, horizon),
                    value_by_enumeration(kernel, start, goal, forbidden, horizon))


if __name__ == "__main__":
    unittest.main()
