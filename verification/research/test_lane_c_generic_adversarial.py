"""Lane C2 generic finite-chain adversarial rechecker.

Pure exact Fraction graph and linear-algebra calculations, independent of
Lean terms and independent of the six-state proof module. These are
regressions and counterexamples, NOT substitutes for a.s. Lean theorems.

No float arithmetic, RNG, simulation, or hidden aperiodicity assumption.
"""
from fractions import Fraction as Q
import unittest


def check_kernel(P):
    n = len(P)
    if n < 1 or any(len(row) != n for row in P):
        raise ValueError("must be a nonempty square kernel")
    if any(x < 0 for row in P for x in row):
        raise ValueError("negative transition mass")
    if any(sum(row) != 1 for row in P):
        raise ValueError("row not normalized")
    return n


def reachable(P, start):
    seen = {start}
    stack = [start]
    while stack:
        i = stack.pop()
        for j, mass in enumerate(P[i]):
            if mass > 0 and j not in seen:
                stack.append(j)
                seen.add(j)
    return frozenset(seen)


def classes(P):
    n = check_kernel(P)
    unseen = set(range(n))
    sccs = []
    while unseen:
        i = min(unseen)
        ri = reachable(P, i)
        c = frozenset(j for j in unseen if j in ri and i in reachable(P, j))
        sccs.append(c)
        unseen -= c
    closed = frozenset(c for c in sccs if all(
        P[i][j] == 0 for i in c for j in range(n) if j not in c))
    return frozenset(sccs), closed


def product(A, B):
    n = check_kernel(A)
    assert len(B) == n
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n))
                       for j in range(n)) for i in range(n))


def powers(P, n):
    N = check_kernel(P)
    q = tuple(tuple(Q(i == j) for j in range(N)) for i in range(N))
    for _ in range(n):
        q = product(q, P)
    return q


def uniform_class_entry_bound(P, horizon):
    """For closed union C, endpoint mass in C = hit-by-horizon probability."""
    _, closed = classes(P)
    target = set().union(*closed)
    T = powers(P, horizon)
    p = tuple(sum(T[i][j] for j in target) for i in range(len(P)))
    return min(p), p


def rational_system(A, b):
    n = len(b)
    R = [[Q(x) for x in A[i]] + [Q(b[i])] for i in range(n)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if R[i][k] != 0), None)
        if pivot is None:
            raise ValueError("singular")
        R[k], R[pivot] = R[pivot], R[k]
        scale = R[k][k]
        R[k] = [x / scale for x in R[k]]
        for i in range(n):
            if i != k:
                fac = R[i][k]
                R[i] = [R[i][j] - fac * R[k][j] for j in range(n + 1)]
    return tuple(row[-1] for row in R)


def class_invariant(P, C):
    c = sorted(C)
    n = len(c)
    A = [[P[c[i]][c[j]] - Q(i == j) for i in range(n)]
         for j in range(n - 1)]
    A.append([Q(1)] * n)
    pi = rational_system(A, [Q(0)] * (n - 1) + [Q(1)])
    assert all(x >= 0 for x in pi) and sum(pi) == 1
    return dict(zip(c, pi))


def one_state():
    return ((Q(1),),)


def three_cycle():
    return ((Q(0), Q(1), Q(0)),
            (Q(0), Q(0), Q(1)),
            (Q(1), Q(0), Q(0)))


def unreachable_basins():
    # Two absorbing classes 0 and 1, a transient state 2 goes only to 0.
    return ((Q(1), Q(0), Q(0)),
            (Q(0), Q(1), Q(0)),
            (Q(1), Q(0), Q(0)))


def slow_absorber(p):
    return ((Q(1), Q(0)),
            (p, Q(1) - p))


def six_state():
    return ((Q(0), Q(1), Q(0), Q(0), Q(0), Q(0)),
            (Q(0), Q(1, 2), Q(1, 6), Q(0), Q(1, 3), Q(0)),
            (Q(0), Q(0), Q(0), Q(1), Q(0), Q(0)),
            (Q(0), Q(0), Q(1), Q(0), Q(0), Q(0)),
            (Q(0), Q(0), Q(0), Q(0), Q(1, 2), Q(1, 2)),
            (Q(0), Q(0), Q(0), Q(0), Q(1, 4), Q(3, 4)))


class GenericFiniteChainAdversaries(unittest.TestCase):
    def test_singleton_chain_ergodic_but_not_regime_nondegeneracy(self):
        P = one_state()
        self.assertEqual(classes(P)[1], frozenset({frozenset({0})}))
        self.assertEqual(uniform_class_entry_bound(P, 1)[0], 1)
        self.assertEqual(class_invariant(P, {0}), {0: 1})
        self.assertFalse(len({False}) >= 2)  # frozen descriptor has 1 value

    def test_period_three_has_periodic_marginals_but_uniform_occupation(self):
        P = three_cycle()
        self.assertEqual(classes(P)[1], frozenset({frozenset({0, 1, 2})}))
        self.assertEqual(class_invariant(P, {0, 1, 2}),
                         {0: Q(1, 3), 1: Q(1, 3), 2: Q(1, 3)})
        self.assertEqual(powers(P, 3)[0], (1, 0, 0))
        self.assertEqual(powers(P, 4)[0], (0, 1, 0))
        self.assertNotEqual(powers(P, 3)[0], powers(P, 4)[0])
        path = [i % 3 for i in range(300)]
        self.assertEqual(tuple(Q(path.count(i), len(path)) for i in range(3)),
                         (Q(1, 3),) * 3)

    def test_unreachable_absorber_does_not_block_common_basin_limit(self):
        P = unreachable_basins()
        self.assertEqual(classes(P)[1], frozenset({
            frozenset({0}), frozenset({1})}))
        self.assertNotIn(1, reachable(P, 2))
        self.assertEqual(powers(P, 1)[2], (1, 0, 0))
        basin = {0, 2}
        h = (False, True, True)
        self.assertEqual(len({h[i] for i in basin}), 2)
        self.assertTrue(all(P[i][j] == 0 for i in basin
                            for j in range(3) if j not in basin))
        # Every basin starting point eventually yields observed False,
        # despite unreachable class 1 having observed True.
        self.assertTrue(all(powers(P, 1)[i][0] == 1 for i in basin))

    def test_no_kernel_independent_geometric_entry_rate(self):
        slow = slow_absorber(Q(1, 1000000))
        fast = slow_absorber(Q(1, 2))
        _, ps = uniform_class_entry_bound(slow, 1)
        _, pf = uniform_class_entry_bound(fast, 1)
        self.assertEqual(ps[1], Q(1, 1000000))
        self.assertEqual(pf[1], Q(1, 2))
        self.assertLess(min(ps), min(pf))
        self.assertGreater(min(ps), 0)
        self.assertEqual(classes(slow)[1], frozenset({frozenset({0})}))

    def test_six_state_exact_uniform_two_step_bound(self):
        P = six_state()
        _, cl = classes(P)
        self.assertEqual(cl, frozenset({
            frozenset({2, 3}), frozenset({4, 5})}))
        q, p = uniform_class_entry_bound(P, 2)
        self.assertEqual(q, Q(1, 2))
        self.assertEqual(p, (Q(1, 2), Q(3, 4), 1, 1, 1, 1))
        self.assertEqual(class_invariant(P, {2, 3}),
                         {2: Q(1, 2), 3: Q(1, 2)})
        self.assertEqual(class_invariant(P, {4, 5}),
                         {4: Q(1, 3), 5: Q(2, 3)})

    def test_certainly_absorbing_is_not_every_path_absorbing(self):
        P = slow_absorber(Q(1, 2))
        self.assertEqual(classes(P)[1], frozenset({frozenset({0})}))
        # Infinite all-1 trajectories are possible as functions, though
        # their probability under the canonical Markov process is zero.
        path = lambda t: 1
        self.assertTrue(all(path(t) == 1 for t in range(100)))
        self.assertEqual(powers(P, 10)[1][1], Q(1, 1024))

    def test_positive_edge_required_not_zero_weight_syntax(self):
        P = unreachable_basins()
        self.assertNotIn(1, reachable(P, 0))
        self.assertNotIn(0, reachable(P, 1))
        self.assertIn(0, reachable(P, 2))


if __name__ == "__main__":
    unittest.main()
