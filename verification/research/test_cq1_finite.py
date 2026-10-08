"""Executable CQ-1 boundary regressions; independent of historical release tests.

These are exact rational finite-state calculations, not Lean proofs or empirical
identification. Models are supplied as finite row-stochastic transition tables.
"""
import itertools
import unittest
from fractions import Fraction as Q


def prefixes(kernel, initial, horizon):
    assert horizon >= 0
    result = {(initial,): Q(1)}
    for _ in range(horizon):
        next_result = {}
        for path, mass in result.items():
            for dest, p in enumerate(kernel[path[-1]]):
                nxt = path + (dest,)
                next_result[nxt] = next_result.get(nxt, Q(0)) + mass * p
        result = next_result
    return result


def expectation(law, score):
    values = [score(path) for path in law]
    assert all(Q(0) <= value <= Q(1) for value in values)
    return sum((p * score(path) for path, p in law.items()), Q(0))


def survival(law, region):
    return sum((p for path, p in law.items()
                if all(state in region for state in path)), Q(0))


def row_tv(kernel, other):
    assert len(kernel) == len(other)
    assert all(len(row) == len(kernel) for row in kernel + other)
    for row in kernel + other:
        assert sum(row, Q(0)) == 1 and all(Q(0) <= x <= Q(1) for x in row)
    return max(sum((abs(a - b) for a, b in zip(row, other_row)), Q(0)) / 2
               for row, other_row in zip(kernel, other))


def envelope(delta, horizon):
    assert 0 <= delta <= 1 and horizon >= 0
    return 1 - (1 - delta) ** horizon


IDENTITY = ((Q(1), Q(0)), (Q(0), Q(1)))
EXIT = ((Q(0), Q(1)), (Q(0), Q(1)))
LEAKY = ((Q(3, 4), Q(1, 4)), (Q(0), Q(1)))


class CQ1FiniteTests(unittest.TestCase):
    def test_zero_horizon_same_initial(self):
        for kernel in (IDENTITY, EXIT, LEAKY):
            self.assertEqual(prefixes(kernel, 0, 0), {(0,): Q(1)})
            self.assertEqual(survival(prefixes(kernel, 0, 0), {0}), 1)
            self.assertEqual(survival(prefixes(kernel, 1, 0), {0}), 0)

    def test_exit_at_horizon_counts_as_failure(self):
        self.assertEqual(survival(prefixes(EXIT, 0, 0), {0}), 1)
        self.assertEqual(survival(prefixes(EXIT, 0, 1), {0}), 0)
        self.assertEqual(survival(prefixes(EXIT, 0, 2), {0}), 0)

    def test_sharp_geometric_survival_discrepancy(self):
        delta = row_tv(IDENTITY, LEAKY)
        self.assertEqual(delta, Q(1, 4))
        for horizon in range(7):
            baseline = survival(prefixes(IDENTITY, 0, horizon), {0})
            approximate = survival(prefixes(LEAKY, 0, horizon), {0})
            self.assertEqual(baseline, 1)
            self.assertEqual(approximate, (1 - delta) ** horizon)
            self.assertEqual(abs(baseline - approximate), envelope(delta, horizon))

    def test_indicator_expectation_is_survival(self):
        for kernel, init, horizon in itertools.product(
                (IDENTITY, EXIT, LEAKY), (0, 1), range(5)):
            law = prefixes(kernel, init, horizon)
            indicator = lambda path: Q(all(y == 0 for y in path))
            self.assertEqual(expectation(law, indicator), survival(law, {0}))

    def test_intervention_has_uniform_nonzero_one_step_effect(self):
        score = lambda path: Q(all(y == 0 for y in path))
        self.assertEqual(expectation(prefixes(IDENTITY, 0, 1), score), 1)
        self.assertEqual(expectation(prefixes(EXIT, 0, 1), score), 0)
        self.assertEqual(abs(expectation(prefixes(IDENTITY, 0, 1), score) -
                             expectation(prefixes(EXIT, 0, 1), score)), 1)

    def test_zero_kernel_errors_and_numerical_budgets(self):
        self.assertEqual(row_tv(IDENTITY, IDENTITY), 0)
        self.assertEqual(envelope(Q(0), 12), 0)
        true_baseline, true_intervened = Q(1), Q(0)
        approx_baseline, approx_intervened = Q(9, 10), Q(1, 10)
        b0 = abs(true_baseline - approx_baseline)
        bj = abs(true_intervened - approx_intervened)
        self.assertEqual(abs(approx_baseline - approx_intervened), Q(4, 5))
        self.assertEqual(abs(approx_baseline - approx_intervened),
                         1 - b0 - bj)

    def test_maximal_one_step_error_uninformative(self):
        self.assertEqual(row_tv(IDENTITY, EXIT), 1)
        for horizon in range(1, 6):
            self.assertEqual(envelope(Q(1), horizon), 1)

    def test_zero_effect_cannot_certify_positive_margin(self):
        law = prefixes(IDENTITY, 0, 2)
        self.assertEqual(abs(expectation(law, lambda path: Q(path[-1] == 0)) -
                             expectation(law, lambda path: Q(path[-1] == 0))), 0)

    def test_positive_pointwise_not_uniform_on_infinite_domain_diagnostic(self):
        # Diagnostic only; not an infinite-state Lean counterexample.
        effects = [Q(1, n) for n in range(1, 2001)]
        self.assertTrue(all(effect > 0 for effect in effects))
        self.assertLess(min(effects), Q(1, 1000))
        # For all ε>0, choose n>1/ε so 1/n<ε: hence infimum is zero.


if __name__ == "__main__":
    unittest.main()
