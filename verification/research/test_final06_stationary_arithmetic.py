"""Independent Fraction evaluator for the *native* deterministic Fin 3/Bool policies.

This verifies finite rational dynamics, not the Lean canonical class-law proof.
"""
from fractions import Fraction as Q
from itertools import product
import unittest


def periodic_tail(policy, *, phase_aware=False):
    """Canonical recurrent orbit of the phase/physical state from (0, False)."""
    state = (0, False)
    visited = {}
    orbit = []
    while state not in visited:
        visited[state] = len(orbit)
        orbit.append(state)
        phase, physical = state
        action = phase != 2 if phase_aware else policy[physical]
        state = ((phase + 1) % 3, action)
        if len(orbit) > 6:
            raise AssertionError("finite six-state deterministic orbit did not close")
    cycle = orbit[visited[state]:]
    return tuple(orbit), tuple(cycle)


def score(cycle):
    physical_true_mass = Q(sum(int(x) for _, x in cycle), len(cycle))
    return Q(1) - abs(physical_true_mass - Q(2, 3))


class NativeExactPeriodicPolicyArithmetic(unittest.TestCase):
    def test_phase_aware_real_native_three_cycle(self):
        orbit, cycle = periodic_tail(None, phase_aware=True)
        self.assertEqual(cycle, ((0, False), (1, True), (2, True)))
        self.assertEqual(score(cycle), Q(1))

    def test_all_four_deterministic_physical_only_feedbacks(self):
        results = {p: score(periodic_tail(p)[1]) for p in product((False, True), repeat=2)}
        self.assertEqual(results[(False, False)], Q(1, 3))
        self.assertEqual(results[(True, True)], Q(2, 3))
        self.assertEqual(results[(False, True)], Q(1, 3))
        self.assertEqual(results[(True, False)], Q(5, 6))
        self.assertEqual(max(results.values()), Q(5, 6))
        self.assertLess(max(results.values()), Q(1))

    def test_randomized_class_tie_not_unrestricted_dominance(self):
        self.assertEqual(Q(1) - abs(Q(2, 3) - Q(2, 3)), Q(1))

    def test_cannot_replace_classwise_expectation_with_nonlinear_barycenter(self):
        class_expectation = (Q(1) - abs(Q(0)-Q(2,3))
                             + Q(1) - abs(Q(1)-Q(2,3)))/2
        barycenter_score = Q(1) - abs(Q(1,2) - Q(2,3))
        self.assertEqual(class_expectation, Q(1,2))
        self.assertEqual(barycenter_score, Q(5,6))
        self.assertNotEqual(class_expectation,barycenter_score)


if __name__ == "__main__":
    unittest.main()
