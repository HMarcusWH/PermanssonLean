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

    def test_finite_horizon_class_destination_distributions(self):
        # Starting at u, class probabilities are exact rational and converge
        # to 1/3 and 2/3. The remaining mass is transient (1/2)^T.
        for T in range(1, 50):
            a_hit = F(1, 3) * (1 - F(1, 2) ** T)
            b_hit = F(2, 3) * (1 - F(1, 2) ** T)
            residual = F(1, 2) ** T
            self.assertEqual(a_hit + b_hit + residual, 1)
            self.assertEqual(a_hit / b_hit, F(1, 2))
            self.assertLess(F(1, 3) - a_hit, residual)
            self.assertLess(F(2, 3) - b_hit, residual)

    def test_empirical_limit_not_time_marginal(self):
        # Point-start A alternates forever. Its time marginals never converge
        # but the pathwise time averages approach the stationary half/half.
        for T in (100, 102, 200):
            sample = [2 if k % 2 == 0 else 3 for k in range(T)]
            self.assertEqual(
                (F(sample.count(2), T), F(sample.count(3), T)),
                (F(1, 2), F(1, 2))
            )
            self.assertNotEqual(K[sample[-1]], K[sample[-2]])

    def test_observed_law_collapses_class_weights_not_physical_modes(self):
        # Different physical limits are mapped to the same observed atom.
        pi_a = (F(0), F(0), F(1, 2), F(1, 2), F(0), F(0))
        pi_b = (F(0), F(0), F(0), F(0), F(1, 3), F(2, 3))
        physical_mean = tuple(F(1, 3) * pi_a[i] + F(2, 3) * pi_b[i]
                              for i in range(6))
        self.assertNotEqual(pi_a, pi_b)
        self.assertNotEqual(physical_mean, pi_a)
        self.assertNotEqual(physical_mean, pi_b)
        h = lambda i: i >= 2
        self.assertEqual(sum(physical_mean[i] for i in range(6) if h(i)), 1)
        self.assertEqual(sum(pi_a[i] for i in range(6) if h(i)), 1)
        self.assertEqual(sum(pi_b[i] for i in range(6) if h(i)), 1)

    def test_periodic_class_cannot_use_marginal_convergence(self):
        self.assertEqual(K[2][3], 1)
        self.assertEqual(K[3][2], 1)
        self.assertNotEqual(K[2], K[3])
        path = [2, 3] * 30
        self.assertEqual(path.count(2), 30)
        self.assertEqual(path.count(3), 30)


if __name__ == '__main__':
    main()
