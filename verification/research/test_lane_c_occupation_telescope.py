"""Independent exact-rational adversarial rechecker of C2 pathwise telescoping.

The equation is deterministic and holds for arbitrary paths and transition
arrays. It is *not* a probabilistic strong law or proof of a martingale.
No simulation, numerical approximations or stochastic assumptions.
"""
from fractions import Fraction as Q
import unittest

P = (
    (Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(1, 2), Q(1, 3), Q(1, 6)),
    (Q(0), Q(0), Q(0), Q(1)),
    (Q(0), Q(0), Q(1), Q(0)),
)


def bit(state, target):
    return Q(int(state == target))


def drift(path, target, n):
    return sum(P[path[t]][target] - bit(path[t], target)
               for t in range(n))


def residual(path, target, n):
    return sum(bit(path[t + 1], target) - P[path[t]][target]
               for t in range(n))


class ExactPathwiseOccupation(unittest.TestCase):
    def test_all_targets_all_horizons(self):
        paths = (
            [0, 1, 1, 2, 3, 2, 3, 2, 3, 2] * 5,
            [2, 3] * 25,
            [3, 2] * 25,
            [1] * 50,
            [0] + [1] * 49,
            list(range(4)) * 13,
        )
        for path in paths:
            for n in (0, 1, 2, 3, 4, 7, 17, 37):
                for target in range(4):
                    self.assertEqual(
                        drift(path, target, n),
                        bit(path[n], target) - bit(path[0], target)
                        - residual(path, target, n),
                    )
                    self.assertTrue(
                        -1 <= bit(path[n], target) - bit(path[0], target) <= 1
                    )
                    if n:
                        self.assertLessEqual(
                            abs((drift(path, target, n) +
                                 residual(path, target, n)) / Q(n)),
                            Q(1, n),
                        )

    def test_drift_is_not_identically_zero(self):
        path = [0, 1, 1, 1]
        self.assertNotEqual(drift(path, 1, 2), 0)
        self.assertNotEqual(residual(path, 1, 2), 0)

    def test_zero_horizon_both_sums_zero(self):
        path = [0, 3]
        for z in range(4):
            self.assertEqual(drift(path, z, 0), 0)
            self.assertEqual(residual(path, z, 0), 0)


if __name__ == "__main__":
    unittest.main()
