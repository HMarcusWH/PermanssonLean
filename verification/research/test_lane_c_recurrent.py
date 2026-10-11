"""Independent exact-rational C2 finite-chain adversarial checks.

Computational regressions, not Lean certification of almost-sure path laws.
Uses Fraction-based linear algebra and graph discovery independently of the
Lean theorem proofs. No floating point or Monte Carlo is used.
"""
from fractions import Fraction as Q
from collections import deque
import unittest

N = 6
P = (
    (Q(0), Q(1), Q(0), Q(0), Q(0), Q(0)),
    (Q(0), Q(1, 2), Q(1, 6), Q(0), Q(1, 3), Q(0)),
    (Q(0), Q(0), Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(0), Q(1), Q(0), Q(0), Q(0)),
    (Q(0), Q(0), Q(0), Q(0), Q(1, 2), Q(1, 2)),
    (Q(0), Q(0), Q(0), Q(0), Q(1, 4), Q(3, 4)),
)
A, B = frozenset((2, 3)), frozenset((4, 5))
PI_A = (Q(0), Q(0), Q(1, 2), Q(1, 2), Q(0), Q(0))
PI_B = (Q(0), Q(0), Q(0), Q(0), Q(1, 3), Q(2, 3))

def reachable(start):
    reached, todo = {start}, [start]
    while todo:
        v = todo.pop()
        for j, p in enumerate(P[v]):
            if p > 0 and j not in reached:
                reached.add(j)
                todo.append(j)
    return reached

def recurrent_classes():
    remaining, comps = set(range(N)), []
    while remaining:
        i = min(remaining)
        comp = frozenset(j for j in remaining
                         if j in reachable(i) and i in reachable(j))
        remaining.difference_update(comp)
        comps.append(comp)
    closed = [c for c in comps
              if all(p == 0 for i in c for j, p in enumerate(P[i]) if j not in c)]
    return frozenset(closed), frozenset(comps)

def solve(A, rhs):
    """Exact Gaussian elimination; rejects singular systems."""
    n = len(rhs)
    aug = [[Q(x) for x in row] + [Q(y)] for row, y in zip(A, rhs)]
    assert all(len(row) == n + 1 for row in aug)
    for k in range(n):
        pivot = next((i for i in range(k, n) if aug[i][k]), None)
        if pivot is None:
            raise ValueError("singular exact system")
        aug[k], aug[pivot] = aug[pivot], aug[k]
        fac = aug[k][k]
        aug[k] = [x / fac for x in aug[k]]
        for i in range(n):
            if i != k:
                fac = aug[i][k]
                aug[i] = [x - fac * y for x, y in zip(aug[i], aug[k])]
    return tuple(row[-1] for row in aug)

def class_invariant(states):
    """Stationarity + normalization, independently solved over the class."""
    states = tuple(sorted(states))
    n = len(states)
    rows = [[P[states[i]][states[j]] - Q(i == j)
             for i in range(n)] for j in range(n - 1)]
    rows.append([Q(1)] * n)
    v = solve(rows, [Q(0)] * (n - 1) + [Q(1)])
    out = [Q(0)] * N
    for i, z in zip(states, v):
        out[i] = z
    return tuple(out)

def hitting_probabilities(target):
    """Boundary 1 on target class, 0 on other closed classes."""
    closed, _ = recurrent_classes()
    boundary = set().union(*closed)
    unknown = sorted(set(range(N)) - boundary)
    vec = [Q(int(i in target)) if i in boundary else None for i in range(N)]
    rows = [[Q(i == j) - P[i][j] for j in unknown] for i in unknown]
    rhs = [sum(P[i][j] * vec[j] for j in boundary) for i in unknown]
    for i, z in zip(unknown, solve(rows, rhs)):
        vec[i] = z
    return tuple(vec)

def matvec(v):
    return tuple(sum(v[i] * P[i][j] for i in range(N)) for j in range(N))

def empirical(path):
    return tuple(Q(path.count(j), len(path)) for j in range(N))

class ExactRecurrentChain(unittest.TestCase):
    def test_stochastic_and_positive_support(self):
        self.assertTrue(all(p >= 0 for row in P for p in row))
        self.assertEqual(tuple(sum(row) for row in P), (Q(1),) * N)
        self.assertNotIn(3, reachable(1))

    def test_components_and_closed_classes(self):
        closed, all_comps = recurrent_classes()
        self.assertEqual(closed, frozenset((A, B)))
        self.assertEqual(all_comps, frozenset((frozenset((0,)), frozenset((1,)), A, B)))

    def test_stationary_from_fresh_linear_solve(self):
        self.assertEqual(class_invariant(A), PI_A)
        self.assertEqual(class_invariant(B), PI_B)
        for pi in (PI_A, PI_B):
            self.assertEqual(sum(pi), 1)
            self.assertEqual(matvec(pi), pi)

    def test_exact_class_entry_harmonic_equations(self):
        pa = hitting_probabilities(A)
        pb = hitting_probabilities(B)
        self.assertEqual(pa, (Q(1, 3), Q(1, 3), 1, 1, 0, 0))
        self.assertEqual(pb, (Q(2, 3), Q(2, 3), 0, 0, 1, 1))
        self.assertEqual(tuple(x + y for x, y in zip(pa, pb)), (Q(1),) * N)
        self.assertEqual(tuple(sum(P[i][j] * pa[j] for j in range(N))
                               for i in range(N)), pa)

    def test_periodic_marginals_vs_cesaro_occupation(self):
        path = [2 if t % 2 == 0 else 3 for t in range(200)]
        self.assertEqual(empirical(path), PI_A)
        self.assertNotEqual(P[2], P[3])
        self.assertNotEqual(P[2], PI_A)
        self.assertEqual(matvec(PI_A), PI_A)

    def test_two_limit_law_is_not_barycenter(self):
        pa, pb = hitting_probabilities(A), hitting_probabilities(B)
        self.assertEqual((pa[0], pb[0]), (Q(1, 3), Q(2, 3)))
        barycenter = tuple(Q(1, 3) * PI_A[i] + Q(2, 3) * PI_B[i] for i in range(N))
        self.assertEqual(barycenter, (0, 0, Q(1, 6), Q(1, 6), Q(2, 9), Q(4, 9)))
        self.assertNotEqual(barycenter, PI_A)
        self.assertNotEqual(barycenter, PI_B)
        self.assertNotEqual(PI_A, PI_B)

    def test_descriptor_collapse_is_not_physical_equality(self):
        h = lambda j: j >= 2
        self.assertEqual({h(i) for i in A}, {True})
        self.assertEqual({h(i) for i in B}, {True})
        self.assertNotEqual(A, B)
        self.assertNotEqual(PI_A, PI_B)

    def test_zero_support_edges_are_not_reachability(self):
        self.assertNotIn(4, reachable(2))
        self.assertNotIn(2, reachable(4))
        self.assertNotIn(0, reachable(1))

if __name__ == "__main__":
    unittest.main()
