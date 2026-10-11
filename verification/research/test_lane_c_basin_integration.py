"""Independent exact-fraction C2 basin/descriptor negative controls.

These finite checks are not an ergodic theorem or a verification of Lean proofs.
"""
from fractions import Fraction as F
from unittest import TestCase, main

K = (
    (F(0), F(1), F(0), F(0), F(0), F(0)),
    (F(0), F(1, 2), F(1, 6), F(0), F(1, 3), F(0)),
    (F(0), F(0), F(0), F(1), F(0), F(0)),
    (F(0), F(0), F(1), F(0), F(0), F(0)),
    (F(0), F(0), F(0), F(0), F(1, 2), F(1, 2)),
    (F(0), F(0), F(0), F(0), F(1, 4), F(3, 4)),
)
C = {'A': frozenset((2, 3)), 'B': frozenset((4, 5))}
REGION = frozenset((1, 2, 3, 4, 5))
WEIGHT_A = (F(1, 3), F(1, 3), F(1), F(1), F(0), F(0))
WEIGHT_B = tuple(F(1) - v for v in WEIGHT_A)


def reachable(start):
    seen = {start}
    stack = [start]
    while stack:
        state = stack.pop()
        for dest, prob in enumerate(K[state]):
            if prob > 0 and dest not in seen:
                seen.add(dest)
                stack.append(dest)
    return frozenset(seen)


def basin_family(basin):
    if not basin:
        raise ValueError('a frozen basin must be nonempty')
    if not set(basin) <= REGION:
        raise ValueError('basin not contained in the proper region')
    return frozenset(name for name, cls in C.items()
                     if any(reachable(s) & cls for s in basin))


class FrozenBasinIntegration(TestCase):
    def test_rows_are_exact_probabilities(self):
        self.assertTrue(all(sum(row) == 1 and all(x >= 0 for x in row) for row in K))

    def test_proper_region_genuinely_closed(self):
        self.assertNotIn(0, REGION)
        self.assertIn(1, REGION)
        self.assertTrue(all(K[i][j] == 0 for i in REGION
                            for j in range(len(K)) if j not in REGION))

    def test_family_includes_only_reachable_classes(self):
        self.assertEqual(basin_family({2, 3}), frozenset({'A'}))
        self.assertEqual(basin_family({4, 5}), frozenset({'B'}))
        self.assertEqual(basin_family({1, 2}), frozenset({'A', 'B'}))
        self.assertEqual(basin_family(REGION), frozenset({'A', 'B'}))

    def test_reject_vacuous_empty_and_outside_basin(self):
        with self.assertRaises(ValueError):
            basin_family(set())
        with self.assertRaises(ValueError):
            basin_family({0})

    def test_class_selection_harmonic_exact(self):
        self.assertTrue(all(WEIGHT_A[i] == sum(K[i][j] * WEIGHT_A[j]
                             for j in range(6)) for i in range(6)))
        self.assertTrue(all(WEIGHT_A[i] + WEIGHT_B[i] == 1 for i in range(6)))
        self.assertEqual((WEIGHT_A[1], WEIGHT_B[1]), (F(1, 3), F(2, 3)))

    def test_descriptor_collapse_does_not_erase_physical_classes(self):
        desc = lambda i: i >= 2
        self.assertNotEqual(C['A'], C['B'])
        self.assertTrue(all(desc(i) for cls in C.values() for i in cls))
        self.assertFalse(desc(1))
        self.assertEqual({desc(i) for i in REGION}, {False, True})

    def test_periodic_class_cannot_use_marginal_convergence(self):
        self.assertEqual(K[2][3], 1)
        self.assertEqual(K[3][2], 1)
        self.assertNotEqual(K[2], K[3])
        path = [2, 3] * 30
        self.assertEqual(path.count(2), 30)
        self.assertEqual(path.count(3), 30)


if __name__ == '__main__':
    main()
