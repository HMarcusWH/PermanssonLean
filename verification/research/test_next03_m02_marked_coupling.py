"""Independent finite action-marked coupling check for M-02.

Real rational probability atoms, not a parser-normalization rejection.
"""
import unittest
from fractions import Fraction as Q
from itertools import product

KEYS = (False, True)
MARKS = tuple(product(KEYS, KEYS))


def mass_aligned(pair):
    return Q(1, 2) if pair[0] == pair[1] else Q(0)


def mass_crossed(pair):
    return Q(1, 2) if pair[0] != pair[1] else Q(0)


def unmarked_mass(law, key):
    return sum((law((key, action)) for action in KEYS), Q(0))


class MarkedCouplingM02(unittest.TestCase):
    def test_both_normalized_joint_laws(self):
        for law in (mass_aligned, mass_crossed):
            self.assertEqual(sum((law(pair) for pair in MARKS), Q(0)), Q(1))
            self.assertTrue(all(law(pair) >= 0 for pair in MARKS))

    def test_unmarked_key_laws_identical(self):
        for key in KEYS:
            self.assertEqual(unmarked_mass(mass_aligned, key), Q(1, 2))
            self.assertEqual(unmarked_mass(mass_crossed, key), Q(1, 2))

    def test_marked_diagonal_is_maximally_separating(self):
        diagonal = [p for p in MARKS if p[0] == p[1]]
        a = sum((mass_aligned(p) for p in diagonal), Q(0))
        b = sum((mass_crossed(p) for p in diagonal), Q(0))
        self.assertEqual((a, b, abs(a-b)), (Q(1), Q(0), Q(1)))

    def test_full_marked_event_tv_exactly_one(self):
        variation = Q(1, 2) * sum(
            (abs(mass_aligned(p)-mass_crossed(p)) for p in MARKS), Q(0)
        )
        self.assertEqual(variation, Q(1))


if __name__ == "__main__":
    unittest.main()
