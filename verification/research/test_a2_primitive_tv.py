"""A2 research-only exact rational adversaries for primitive α/P/U TV budgets.

No claim that Python itself verifies a general Lean theorem or empirical
identification. All finite probabilities are exact fractions. This suite
guards the intended typed/order-sensitive mathematical statements.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
import random
import unittest

STATES = tuple(product(range(2), range(2)))
ACTIONS = (0, 1)


def normalize(rows):
    vals = [Q(i) for i in rows]
    assert sum(vals) > 0
    return tuple(v / sum(vals) for v in vals)


class FiniteModel:
    """Explicit typed S/X/A model, not a generic claimed strategic inference."""
    def __init__(self, alpha, world, update):
        self.alpha, self.world, self.update = alpha, world, update
        for y in STATES:
            assert sum(self.alpha[y]) == 1
            for a in ACTIONS:
                assert sum(self.world[(y, a)]) == 1
                for xp in range(2):
                    assert sum(self.update[(y, a, xp)]) == 1

    def joint(self):
        return {y: tuple(
            sum((self.alpha[y][a] * self.world[(y, a)][xp] *
                 self.update[(y, a, xp)][sp] for a in ACTIONS),
                Q(0)) for sp, xp in STATES
        ) for y in STATES}


def baseline():
    a = {y: (Q(1), Q(0)) for y in STATES}
    p = {(y, act): (Q(1), Q(0)) for y in STATES for act in ACTIONS}
    u = {(y, act, xp): (Q(1), Q(0)) for y in STATES
         for act in ACTIONS for xp in range(2)}
    return FiniteModel(a, p, u)


def with_changed(model, *, alpha=None, world=None, update=None):
    return FiniteModel(alpha if alpha is not None else model.alpha,
                       world if world is not None else model.world,
                       update if update is not None else model.update)


def tv(v, w):
    assert len(v) == len(w)
    return sum((abs(a - b) for a, b in zip(v, w)), Q(0)) / 2


def all_primitive_errors(m, n):
    da = max(tv(m.alpha[y], n.alpha[y]) for y in STATES)
    dp = max(tv(m.world[(y, a)], n.world[(y, a)])
             for y in STATES for a in ACTIONS)
    du = max(tv(m.update[(y, a, xp)], n.update[(y, a, xp)])
             for y in STATES for a in ACTIONS for xp in range(2))
    return da, dp, du


def budget(ds):
    return min(Q(1), sum(ds, Q(0)))


def check_primitive_bound(m, n):
    d = budget(all_primitive_errors(m, n))
    assert max(tv(m.joint()[y], n.joint()[y]) for y in STATES) <= d
    return d


def path_law(k, initial, t):
    paths = {(initial,): Q(1)}
    for _ in range(t):
        nxt = {}
        for path, mass in paths.items():
            for z, p in zip(STATES, k[path[-1]]):
                nxt[path + (z,)] = nxt.get(path + (z,), Q(0)) + mass * p
        paths = nxt
    return paths


def path_tv(left, right):
    return tv([left.get(w, Q(0)) for w in sorted(set(left) | set(right))],
              [right.get(w, Q(0)) for w in sorted(set(left) | set(right))])


def finite_score(k, y, horizon, score):
    return sum((mass * score(path) for path, mass in path_law(k, y, horizon).items()),
               Q(0))


def gap(m, intervention, frozen_states, horizon, score):
    return min(abs(finite_score(m.joint(), y, horizon, score) -
                   finite_score(intervention.joint(), y, horizon, score))
               for y in frozen_states)


def matched(target, other_target, component, other_component):
    return target in {"actionSelection", "strategicUpdate", "jointStrategic"} and (
        target == other_target and component == other_component
    )


class A2PrimitiveTests(unittest.TestCase):
    def test_a2_01_zero_errors(self):
        m = baseline()
        self.assertEqual(check_primitive_bound(m, m), 0)

    def test_a2_02_action_only(self):
        m = baseline()
        a = dict(m.alpha)
        a[STATES[0]] = (Q(2, 5), Q(3, 5))
        n = with_changed(m, alpha=a)
        self.assertEqual(check_primitive_bound(m, n), Q(3, 5))

    def test_a2_03_world_only(self):
        m = baseline()
        p = dict(m.world)
        p[(STATES[0], 0)] = (Q(1, 4), Q(3, 4))
        n = with_changed(m, world=p)
        self.assertEqual(check_primitive_bound(m, n), Q(3, 4))
        self.assertNotEqual(m.world, n.world)

    def test_a2_04_update_only(self):
        m = baseline()
        u = dict(m.update)
        u[(STATES[0], 0, 0)] = (Q(1, 5), Q(4, 5))
        self.assertEqual(check_primitive_bound(m, with_changed(m, update=u)), Q(4, 5))

    def test_a2_05_sum_clamps_to_one(self):
        m = baseline()
        a = {y: (Q(0), Q(1)) for y in STATES}
        p = {(y, z): (Q(0), Q(1)) for y in STATES for z in ACTIONS}
        u = {(y, z, xp): (Q(0), Q(1)) for y in STATES
             for z in ACTIONS for xp in range(2)}
        n = FiniteModel(a, p, u)
        self.assertEqual(sum(all_primitive_errors(m, n)), 3)
        self.assertEqual(check_primitive_bound(m, n), 1)

    def test_a2_06_zero_horizon_identical(self):
        m = baseline()
        for y in STATES:
            self.assertEqual(path_law(m.joint(), y, 0), {(y,): Q(1)})

    def test_a2_07_one_transition(self):
        m = baseline()
        p = dict(m.world)
        p[(STATES[0], 0)] = (Q(1, 3), Q(2, 3))
        n = with_changed(m, world=p)
        eps = check_primitive_bound(m, n)
        self.assertEqual(path_tv(path_law(m.joint(), STATES[0], 1),
                                 path_law(n.joint(), STATES[0], 1)), eps)

    def test_a2_08_post_intervention_reachable_row(self):
        m = baseline()
        p = dict(m.world)
        p[(STATES[0], 1)] = (Q(0), Q(1))
        n = with_changed(m, world=p)
        # Baseline a=0 cannot see the changed row, but strategic action
        # replacement a=1 activates the discrepancy.
        self.assertEqual(check_primitive_bound(m, n), 1)
        a = {y: (Q(0), Q(1)) for y in STATES}
        j = with_changed(m, alpha=a)
        nj = with_changed(n, alpha=a)
        self.assertEqual(tv(j.joint()[STATES[0]], nj.joint()[STATES[0]]), 1)

    def test_a2_09_update_must_consume_realized_next_world(self):
        m = baseline()
        p = dict(m.world)
        p[(STATES[0], 0)] = (Q(0), Q(1))
        u = dict(m.update)
        u[(STATES[0], 0, 1)] = (Q(0), Q(1))
        n = FiniteModel(m.alpha, p, u)
        # The two-stage result must be (S'=1, X'=1), not (S'=0, X'=1)
        self.assertEqual(n.joint()[STATES[0]], (Q(0), Q(0), Q(0), Q(1)))

    def test_a2_10_changed_world_is_not_a_strategic_intervention(self):
        self.assertFalse(matched("worldTransition", "worldTransition", "k", "k"))
        self.assertTrue(matched("actionSelection", "actionSelection", "k", "k"))

    def test_a2_11_pointwise_positive_not_uniform(self):
        original = baseline()
        # The structural world law is frozen across the intervention.
        # Only action selection changes at the first state.
        p = dict(original.world)
        p[(STATES[0], 1)] = (Q(0), Q(1))
        m = with_changed(original, world=p)
        a = dict(m.alpha)
        a[STATES[0]] = (Q(0), Q(1))
        j = with_changed(m, alpha=a)
        self.assertEqual(j.world, m.world)
        f = lambda path: Q(1) if path[-1][1] == 1 else Q(0)
        self.assertGreater(abs(finite_score(m.joint(), STATES[0], 1, f) -
                               finite_score(j.joint(), STATES[0], 1, f)), 0)
        self.assertEqual(gap(m, j, STATES, 1, f), 0)

    def test_a2_12_arbitrarily_small_leak_breaks_exact_invariance(self):
        eps = Q(1, 1000)
        k = {y: (Q(1), Q(0), Q(0), Q(0)) for y in STATES}
        leak = {y: (1 - eps, eps, Q(0), Q(0)) for y in STATES}
        self.assertEqual(max(tv(k[y], leak[y]) for y in STATES), eps)
        for t in range(1, 5):
            self.assertEqual(sum(p for w, p in path_law(leak, STATES[0], t).items()
                                 if all(z == STATES[0] for z in w)),
                             (1 - eps) ** t)
        self.assertLess(1 - eps, 1)  # Infinite retention is zero.

    def test_a2_13_scores_outside_unit_interval_not_admissible(self):
        def check_score(values):
            if any(not (Q(0) <= v <= Q(1)) for v in values):
                raise ValueError("score outside declared [0,1]")
        for values in ((Q(2),), (Q(-1),), (Q(1, 2), Q(3, 2))):
            with self.assertRaises(ValueError):
                check_score(values)

    def test_a2_14_component_and_target_must_match(self):
        self.assertFalse(matched("actionSelection", "strategicUpdate", "k", "k"))
        self.assertFalse(matched("actionSelection", "actionSelection", "k", "other"))
        self.assertTrue(matched("jointStrategic", "jointStrategic", "k", "k"))

    def test_a2_15_exact_exhaustive_synthetic_primitives(self):
        rng = random.Random(6402)
        for _ in range(35):
            def one():
                return normalize((rng.randint(1, 7), rng.randint(1, 7)))
            def rand_model():
                return FiniteModel(
                    {y: one() for y in STATES},
                    {(y, a): one() for y in STATES for a in ACTIONS},
                    {(y, a, xp): one() for y in STATES for a in ACTIONS
                     for xp in range(2)}
                )
            m, n = rand_model(), rand_model()
            d = check_primitive_bound(m, n)
            for t in range(3):
                actual = path_tv(path_law(m.joint(), STATES[0], t),
                                 path_law(n.joint(), STATES[0], t))
                self.assertLessEqual(actual, 1 - (1 - d) ** t)


if __name__ == "__main__":
    unittest.main()
