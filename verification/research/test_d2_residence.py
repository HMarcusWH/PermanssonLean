"""D2 independent exact-rational path, residence-clock and policy adversaries.

These finite cross-checks do not prove the general Lean statements. Literal
window enumeration, a forward residence clock, a backwards controller, and
complete policy enumeration are implemented independently and compared.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import unittest

ZERO, ONE = F(0), F(1)


def matrix(rows):
    assert all(sum(row.values(), ZERO) == ONE and all(p >= 0 for p in row.values())
               for row in rows.values())
    return rows


def literal_event(word, target, m, entry_deadline=None):
    """m transitions AFTER entry require m+1 target observations."""
    latest = len(word) - m - 1
    if entry_deadline is not None:
        latest = min(latest, entry_deadline)
    return any(all(word[e + j] in target for j in range(m + 1))
               for e in range(latest + 1))


def clock_event(word, target, m, mutation=None):
    count = int(word[0] in target) if mutation != "missing_initial" else 0
    required = m + 1 if mutation != "observations_not_transitions" else m
    done = count >= required
    for z in word[1:]:
        if done and mutation != "forget_completion":
            continue
        if z in target:
            count = count + 1 if count > 0 or mutation != "cannot_enter" else 0
        elif mutation != "no_reset":
            count = 0
        done = count >= required
    return done


def paths(system, policy, start, horizon):
    cur = {(start,): ONE}
    for _ in range(horizon):
        nxt = {}
        for word, mass in cur.items():
            row = system[policy(word)][word[-1]]
            for z, p in row.items():
                nxt[word + (z,)] = nxt.get(word + (z,), ZERO) + mass * p
        cur = nxt
    assert sum(cur.values(), ZERO) == ONE
    return cur


def event_probability(system, policy, start, horizon, target, m, deadline=None):
    return sum((p for word, p in paths(system, policy, start, horizon).items()
                if literal_event(word, target, m, deadline)), ZERO)


def history_value(system, policy, target, m, word, remaining):
    if remaining == 0:
        return F(literal_event(word, target, m))
    return sum((p * history_value(system, policy, target, m, word + (z,), remaining - 1)
                for z, p in system[policy(word)][word[-1]].items()), ZERO)


def history_bellman(system, target, m, start, horizon):
    @lru_cache(None)
    def value(word, remaining):
        if remaining == 0:
            return F(literal_event(word, target, m))
        return max(sum((p * value(word + (z,), remaining - 1)
                        for z, p in K[word[-1]].items()), ZERO)
                   for K in system.values())
    return value((start,), horizon)


def clock_bellman(system, target, m, start, horizon):
    """Independent small product-state calculation; Lean compression is OPEN."""
    @lru_cache(None)
    def value(y, count, remaining):
        if count == m + 1:
            return ONE
        if remaining == 0:
            return ZERO
        return max(sum((p * value(z, count + 1 if z in target else 0, remaining - 1)
                        for z, p in K[y].items()), ZERO)
                   for K in system.values())
    return value(start, int(start in target), horizon)


class ResidenceSemanticsTests(unittest.TestCase):
    def test_clock_matches_literal_windows_exhaustively(self):
        for length in range(1, 8):
            for word in product((0, 1), repeat=length):
                for m in range(4):
                    self.assertEqual(clock_event(word, {1}, m),
                                     literal_event(word, {1}, m), (word, m))

    def test_start_in_target_counts_time_zero(self):
        self.assertTrue(literal_event((1,), {1}, 0))
        self.assertFalse(literal_event((1,), {1}, 1))
        self.assertTrue(literal_event((1, 1), {1}, 1))

    def test_first_entry_starts_counter_from_zero(self):
        self.assertTrue(clock_event((0, 1, 1), {1}, 1))
        self.assertFalse(clock_event((0, 1, 0), {1}, 1))

    def test_retry_is_distinct_from_first_ever_entry(self):
        word = (0, 1, 0, 1, 1)
        self.assertTrue(literal_event(word, {1}, 1))
        first = word.index(1)
        self.assertFalse(all(word[first + j] == 1 for j in range(2)))

    def test_completed_success_survives_later_exit(self):
        self.assertTrue(clock_event((0, 1, 1, 0), {1}, 1))

    def test_entry_deadline_and_completion_deadline_differ(self):
        word, T, m = (0, 1, 1), 1, 1
        self.assertTrue(literal_event(word, {1}, m, T))
        self.assertFalse(literal_event(word[:T + 1], {1}, m))

    def test_horizon_T_plus_m_is_exact_entry_bound(self):
        for T in range(4):
            for m in range(3):
                for word in product((0, 1), repeat=T + m + 1):
                    self.assertEqual(literal_event(word, {1}, m, T),
                                     literal_event(word, {1}, m))

    def test_hit_does_not_imply_stay(self):
        K = matrix({0: {1: ONE}, 1: {0: ONE}})
        system = {0: K}
        hit = event_probability(system, lambda _: 0, 0, 2, {1}, 0)
        stay = event_probability(system, lambda _: 0, 0, 2, {1}, 1)
        self.assertEqual((hit, stay), (ONE, ZERO))

    def test_empty_and_universal_targets(self):
        for m in range(4):
            self.assertFalse(literal_event((0, 1, 0, 1), set(), m))
            self.assertTrue(literal_event((0, 1, 0, 1), {0, 1}, m))

    def test_mutations_are_detected(self):
        adversaries = {
            "missing_initial": ((1, 1), 1),
            "cannot_enter": ((0, 1, 1), 1),
            "observations_not_transitions": ((0, 1, 0), 1),
            "no_reset": ((1, 0, 1), 1),
            "forget_completion": ((1, 1, 0), 1),
        }
        for mutation, (word, m) in adversaries.items():
            with self.subTest(mutation=mutation):
                self.assertNotEqual(clock_event(word, {1}, m, mutation),
                                    literal_event(word, {1}, m))


class CanonicalPathAndControlTests(unittest.TestCase):
    def test_recursion_matches_independent_path_enumeration(self):
        for p, q in product((ZERO, F(1, 4), F(1, 2), F(3, 4), ONE), repeat=2):
            K = matrix({0: {0: 1-p, 1: p}, 1: {0: 1-q, 1: q}})
            system = {0: K}
            for x, D, m in product((0, 1), range(5), range(3)):
                actual = event_probability(system, lambda _: 0, x, D, {1}, m)
                value = history_value(system, lambda _: 0, {1}, m, (x,), D)
                self.assertEqual(actual, value)

    def test_history_sensitive_policy_no_future_information(self):
        K0 = matrix({0: {0: F(1, 2), 1: F(1, 2)}, 1: {0: F(1, 3), 1: F(2, 3)}})
        K1 = matrix({0: {1: ONE}, 1: {0: ONE}})
        system = {0: K0, 1: K1}
        policy = lambda word: sum(word) % 2
        for D in range(5):
            self.assertEqual(event_probability(system, policy, 0, D, {1}, 1),
                             history_value(system, policy, {1}, 1, (0,), D))

    def test_bellman_equals_enumerated_deterministic_policies(self):
        system = {
            0: matrix({0: {0: F(1, 2), 1: F(1, 2)}, 1: {0: ZERO, 1: ONE}}),
            1: matrix({0: {1: ONE}, 1: {0: ONE}}),
        }
        D, x, m = 3, 0, 1
        histories = [(x,) + tail for length in range(D)
                     for tail in product((0, 1), repeat=length)]
        values = []
        for choices in product((0, 1), repeat=len(histories)):
            policy_map = dict(zip(histories, choices))
            values.append(event_probability(system, policy_map.__getitem__, x, D, {1}, m))
        optimum = history_bellman(system, {1}, m, x, D)
        self.assertEqual(optimum, max(values))
        self.assertEqual(optimum, ONE)
        self.assertLess(min(values), optimum)

    def test_product_clock_and_history_values_agree(self):
        system = {
            0: matrix({0: {0: F(1, 4), 1: F(3, 4)}, 1: {0: F(1, 2), 1: F(1, 2)}}),
            1: matrix({0: {0: F(1, 2), 1: F(1, 2)}, 1: {0: F(1, 4), 1: F(3, 4)}}),
        }
        for x, D, m in product((0, 1), range(6), range(3)):
            self.assertEqual(history_bellman(system, {1}, m, x, D),
                             clock_bellman(system, {1}, m, x, D))


class RobustAndRiskTests(unittest.TestCase):
    def test_committed_randomization_vs_model_revealed_first(self):
        committed = [min(p, 1-p) for p in (F(k, 20) for k in range(21))]
        self.assertEqual(max(committed), F(1, 2))
        revealed = min(max(p if model else 1-p for p in (ZERO, ONE))
                       for model in (False, True))
        self.assertEqual(revealed, ONE)
        self.assertLess(max(committed), revealed)

    def test_deterministic_robust_value_zero(self):
        self.assertEqual(max(min(p, 1-p) for p in (ZERO, ONE)), ZERO)

    def test_risk_budget_changes_optimum(self):
        success = lambda p: F(4, 5) + p/10
        risk = lambda p: p/10
        grid = [F(k, 100) for k in range(101)]
        unconstrained = max(grid, key=success)
        feasible = [p for p in grid if risk(p) <= F(1, 20)]
        constrained = max(feasible, key=success)
        self.assertEqual((unconstrained, constrained), (ONE, F(1, 2)))
        self.assertEqual(success(constrained), F(17, 20))
        self.assertGreater(risk(unconstrained), F(1, 20))


if __name__ == "__main__":
    unittest.main()
