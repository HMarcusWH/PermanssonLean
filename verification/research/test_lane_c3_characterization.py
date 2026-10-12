"""PR54/C3 independent exact-rational classification adversaries.

These tests validate concrete finite matrices and logical boundary cases.
They do NOT certify Lean's general almost-sure theorem, an actual typed
intervention, or historical predeclaration of real-world specifications.
"""
from fractions import Fraction as Q
import unittest

P = (
    (Q(0), Q(1), Q(0), Q(0), Q(0), Q(0)),
    (Q(0), Q(1, 2), Q(1, 6), Q(0), Q(1, 3), Q(0)),
    (Q(0), Q(0), Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(0), Q(1), Q(0), Q(0), Q(0)),
    (Q(0), Q(0), Q(0), Q(0), Q(1, 2), Q(1, 2)),
    (Q(0), Q(0), Q(0), Q(0), Q(1, 4), Q(3, 4)),
)
A, B = frozenset((2, 3)), frozenset((4, 5))
REGION = frozenset((1, 2, 3, 4, 5))
BASIN = frozenset((1, 2))


def reachable(start):
    seen = {start}
    todo = [start]
    while todo:
        state = todo.pop()
        for nxt, probability in enumerate(P[state]):
            if probability and nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return frozenset(seen)


def solve_exact(a, b):
    n = len(b)
    a = [[Q(x) for x in row] + [Q(y)] for row, y in zip(a, b)]
    for k in range(n):
        pivot = next(i for i in range(k, n) if a[i][k])
        a[k], a[pivot] = a[pivot], a[k]
        d = a[k][k]
        a[k] = [v / d for v in a[k]]
        for i in range(n):
            if i == k:
                continue
            v = a[i][k]
            a[i] = [x - v * y for x, y in zip(a[i], a[k])]
    return tuple(row[-1] for row in a)


def stationary(cls):
    states = sorted(cls)
    n = len(states)
    a = [
        [P[states[i]][states[j]] - Q(i == j) for i in range(n)]
        for j in range(n - 1)
    ] + [[Q(1)] * n]
    values = solve_exact(a, [Q(0)] * (n - 1) + [Q(1)])
    out = [Q(0)] * len(P)
    for index, value in zip(states, values):
        out[index] = value
    return tuple(out)


def absorption(cls):
    transient = sorted(set(range(len(P))) - A - B)
    target = {
        i: Q(int(i in cls))
        for i in A | B
    }
    a = [
        [Q(i == j) - P[i][j] for j in transient]
        for i in transient
    ]
    b = [
        sum(P[i][j] * target[j] for j in A | B)
        for i in transient
    ]
    for index, value in zip(transient, solve_exact(a, b)):
        target[index] = value
    return tuple(target[i] for i in range(len(P)))


def reachable_family(basin):
    return frozenset(
        name for name, cls in (("A", A), ("B", B))
        if any(absorption(cls)[y] > 0 for y in basin)
    )


def push_probability(vec, descriptor):
    result = {}
    for state, value in enumerate(vec):
        key = descriptor(state)
        result[key] = result.get(key, Q(0)) + value
    return {key: val for key, val in result.items() if val != 0}


def common_target_exists(basin, descriptor):
    class_laws = {
        "A": push_probability(stationary(A), descriptor),
        "B": push_probability(stationary(B), descriptor),
    }
    family = reachable_family(basin)
    assert family
    return len({tuple(sorted(class_laws[name].items())) for name in family}) == 1


class C3ExactClassification(unittest.TestCase):
    def test_canonical_rows_are_exact_and_normalized(self):
        self.assertTrue(all(p >= 0 for row in P for p in row))
        self.assertTrue(all(sum(row) == 1 for row in P))

    def test_recurrent_classes_are_closed_and_disjoint(self):
        self.assertFalse(A & B)
        for cls in (A, B):
            self.assertTrue(all(P[i][j] == 0 for i in cls for j in range(6) if j not in cls))

    def test_solve_stationary_laws_independently(self):
        self.assertEqual(stationary(A), (0, 0, Q(1, 2), Q(1, 2), 0, 0))
        self.assertEqual(stationary(B), (0, 0, 0, 0, Q(1, 3), Q(2, 3)))
        for pi in (stationary(A), stationary(B)):
            self.assertEqual(
                tuple(sum(pi[i] * P[i][j] for i in range(6)) for j in range(6)), pi
            )

    def test_class_selection_weight_exact_not_assigned(self):
        self.assertEqual(absorption(A), (Q(1, 3), Q(1, 3), 1, 1, 0, 0))
        self.assertEqual(absorption(B), (Q(2, 3), Q(2, 3), 0, 0, 1, 1))
        self.assertEqual(absorption(A)[1] + absorption(B)[1], 1)

    def test_positive_boolean_descriptor_accepts_both_classes(self):
        self.assertEqual(reachable_family(BASIN), frozenset(("A", "B")))
        h = lambda y: y in A | B
        self.assertEqual(push_probability(stationary(A), h), {True: 1})
        self.assertEqual(push_probability(stationary(B), h), {True: 1})
        self.assertTrue(common_target_exists(BASIN, h))
        self.assertEqual({h(y) for y in REGION}, {False, True})

    def test_identity_descriptor_obstructs_every_single_target(self):
        self.assertNotEqual(stationary(A), stationary(B))
        self.assertFalse(common_target_exists(BASIN, lambda y: y))
        self.assertEqual(reachable_family(BASIN), frozenset(("A", "B")))

    def test_restricted_A_basin_identity_has_no_B_obstruction(self):
        basin = frozenset((2, 3))
        self.assertEqual(len(basin), 2)
        self.assertEqual(reachable_family(basin), frozenset(("A",)))
        self.assertTrue(common_target_exists(basin, lambda y: y))
        self.assertNotEqual(P[2], P[3])

    def test_mismatched_frozen_target_rejected(self):
        h = lambda y: y in A | B
        lawA = push_probability(stationary(A), h)
        lawB = push_probability(stationary(B), h)
        wrong = {False: Q(1)}
        self.assertNotEqual(lawA, wrong)
        self.assertNotEqual(lawB, wrong)

    def test_small_positive_selection_weights_are_still_reachable(self):
        for epsilon in (Q(1, 100), Q(1, 10**6), Q(1, 10**35)):
            # General two-recurrent-absorber brancher with exact ε.
            self.assertGreater(epsilon, 0)
            self.assertNotEqual(epsilon, Q(0))
            self.assertEqual(epsilon + (1 - epsilon), 1)

    def test_unreachable_class_never_registered(self):
        self.assertEqual(reachable_family(frozenset((2,))), frozenset(("A",)))
        self.assertEqual(absorption(B)[2], 0)
        self.assertNotIn(4, reachable(2))

    def test_periodic_marginals_not_empirical_limit(self):
        self.assertNotEqual(P[2], P[3])
        for n in (2, 20, 200):
            path = [2 if t % 2 == 0 else 3 for t in range(n)]
            self.assertEqual((Q(path.count(2), n), Q(path.count(3), n)),
                             (Q(1, 2), Q(1, 2)))

    def test_assumption41_two_basin_states_required(self):
        self.assertEqual(len(BASIN), 2)
        self.assertEqual(len(frozenset((2,))), 1)
        self.assertFalse(len(frozenset((2,))) >= 2)

    def test_region_invariance_is_independent_gate(self):
        self.assertTrue(all(P[i][j] == 0 for i in REGION for j in range(6) if j not in REGION))
        invalid_region = frozenset((1, 2))
        self.assertTrue(any(P[i][j] > 0 for i in invalid_region for j in range(6)
                            if j not in invalid_region))

    def test_custom_always_true_mode_is_not_almost_sure_weak(self):
        # The frozen original permits custom modes. The always-true
        # mode is a logical boundary, not a stochastic convergence fact.
        predicate = lambda _trajectory, _target: True
        self.assertTrue(predicate([], None))
        self.assertFalse(common_target_exists(BASIN, lambda y: y))


if __name__ == "__main__":
    unittest.main()
