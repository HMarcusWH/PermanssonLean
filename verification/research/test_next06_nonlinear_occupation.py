"""Independent exact-rational boundary checks for the constructed D2-P09 case.

Finite trajectory verification; not a proof of general infinite-path laws.
"""
import itertools
import unittest
from fractions import Fraction as F


def physical_transition(state: bool, action: bool) -> bool:
    return action


def orbit(policy, steps):
    states = [False]
    for _ in range(steps):
        states.append(physical_transition(states[-1], policy(states[-1])))
    return states


def nonlinear_score(share):
    return F(1) - abs(share - F(2, 3))


class NonlinearOccupationBoundary(unittest.TestCase):
    def test_all_four_stationary_feedback_maps(self):
        values = {}
        for a0, a1 in itertools.product((False, True), repeat=2):
            policy = lambda z, a0=a0, a1=a1: a1 if z else a0
            states = orbit(policy, 51)
            self.assertTrue(all(states[n+2] == states[n+4] for n in range(48)))
            share = F(int(states[2]) + int(states[3]), 2)
            values[(a0, a1)] = nonlinear_score(share)
        self.assertEqual(values[(False, False)], F(1, 3))
        self.assertEqual(values[(False, True)], F(1, 3))
        self.assertEqual(values[(True, True)], F(2, 3))
        self.assertEqual(values[(True, False)], F(5, 6))
        self.assertEqual(max(values.values()), F(5, 6))

    def test_fixed_period_three_policy_true_frequency(self):
        states = [False]
        for n in range(3 * 30):
            states.append(physical_transition(states[-1], n % 3 != 2))
        for k in range(30):
            self.assertEqual(states[3*k+1:3*k+4], [True, True, False])
            count = sum(states[1:3*(k+1)+1])
            self.assertEqual(F(count, 3*(k+1)), F(2, 3))
        self.assertEqual(nonlinear_score(F(2, 3)), F(1))

    def test_nonstationary_value_exceeds_stationary_maximum(self):
        static = [nonlinear_score(p) for p in (F(0), F(1), F(1, 2))]
        self.assertEqual(max(static), F(5, 6))
        self.assertTrue(all(value < F(1) for value in static))


if __name__ == "__main__":
    unittest.main()
