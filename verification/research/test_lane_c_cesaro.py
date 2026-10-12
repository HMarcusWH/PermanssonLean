"""Exact independent regression for finite Cesaro stationary residuals.

Pure Fraction arithmetic. No simulations, floating-point tolerances,
or claims of proving infinite-horizon a.s. ergodicity by finite testing.
"""
from fractions import Fraction as Q
import unittest

THREE_CYCLE = (
    (Q(0), Q(1), Q(0)),
    (Q(0), Q(0), Q(1)),
    (Q(1), Q(0), Q(0)),
)

SIX_STATE = (
    (Q(0), Q(1), Q(0), Q(0), Q(0), Q(0)),
    (Q(0), Q(1, 2), Q(1, 6), Q(0), Q(1, 3), Q(0)),
    (Q(0), Q(0), Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(0), Q(1), Q(0), Q(0), Q(0)),
    (Q(0), Q(0), Q(0), Q(0), Q(1, 2), Q(1, 2)),
    (Q(0), Q(0), Q(0), Q(0), Q(1, 4), Q(3, 4)),
)


def push(v, K):
    n = len(v)
    assert len(K) == n and all(len(r) == n for r in K)
    assert all(sum(row) == 1 and all(x >= 0 for x in row) for row in K)
    return tuple(sum(v[i] * K[i][j] for i in range(n)) for j in range(n))


def time_vectors(v, K, count):
    history = [v]
    for _ in range(count):
        history.append(push(history[-1], K))
    return history


def average(rows):
    n = len(rows)
    return tuple(sum(row[j] for row in rows) / n for j in range(len(rows[0])))


class ExactCesaroDefect(unittest.TestCase):
    def test_telescope_every_horizon_and_every_start(self):
        for P in (THREE_CYCLE, SIX_STATE):
            for start in range(len(P)):
                v = tuple(Q(i == start) for i in range(len(P)))
                for n in (0, 1, 2, 3, 4, 7, 23):
                    history = time_vectors(v, P, n + 1)
                    a = average(history[:n + 1])
                    residual = tuple(x - y for x, y in zip(push(a, P), a))
                    endpoint = tuple((history[n + 1][i] - v[i]) / (n + 1)
                                     for i in range(len(P)))
                    self.assertEqual(residual, endpoint)
                    self.assertEqual(sum(a), 1)
                    self.assertTrue(all(0 <= x <= 1 for x in a))
                    self.assertTrue(all(abs(x) <= Q(1, n + 1)
                                        for x in residual))

    def test_periodic_marginals_need_not_converge(self):
        P = THREE_CYCLE
        v = (Q(1), Q(0), Q(0))
        history = time_vectors(v, P, 302)
        self.assertEqual(history[300], v)
        self.assertEqual(history[301], (0, 1, 0))
        self.assertEqual(average(history[:300]), (Q(1, 3),) * 3)

    def test_cesaro_residual_does_not_prove_pathwise_limit(self):
        P = SIX_STATE
        v = (Q(1), Q(0), Q(0), Q(0), Q(0), Q(0))
        history = time_vectors(v, P, 51)
        barycenter = average(history[:50])
        # Expected Cesaro limit is a barycenter over recurrent classes,
        # whereas a sample-path occupation limit is one class law.
        self.assertNotEqual(barycenter, (0, 0, Q(1, 2), Q(1, 2), 0, 0))
        self.assertNotEqual(barycenter, (0, 0, 0, 0, Q(1, 3), Q(2, 3)))


if __name__ == "__main__":
    unittest.main()
