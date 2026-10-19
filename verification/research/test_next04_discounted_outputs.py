"""Exact-fraction adversaries for actual-law discounted output budgets.

These arithmetic checks supplement, and never replace, the pinned Lean
compiler, actual source marginal identities and the transitive axiom audit.
"""
import unittest
from fractions import Fraction as F


def retained(eta, n):
    product = F(1)
    for t in range(n):
        defect = eta(t)
        if not F(0) <= defect <= F(1):
            raise ValueError("defect not normalized")
        product *= 1 - defect
    return product


def envelope(eps, eta, n):
    if not F(0) <= eps <= F(1):
        raise ValueError("initial error not normalized")
    return F(1) - (F(1)-eps) * retained(eta, n)


def discounted_prefix(eps, eta, beta, n):
    if not F(0) <= beta < F(1) or n < 0:
        raise ValueError("discount not normalized")
    return sum(((F(1)-beta)*beta**t*envelope(eps, eta, t)
                for t in range(n)), F(0))


class DiscountedProjectedOutputFixtures(unittest.TestCase):
    def test_nonzero_initial_error_at_zero_transitions(self):
        eta = lambda _: F(0)
        eps = F(1, 7)
        for n in range(8):
            self.assertEqual(envelope(eps, eta, n), eps)
        self.assertEqual(discounted_prefix(eps, eta, F(0), 1), eps)

    def test_nonstationary_defects_not_replaced_by_last_row(self):
        seq = (F(1, 10), F(1, 5), F(1, 4))
        eta = lambda n: seq[n] if n < len(seq) else F(0)
        eps = F(1, 7)
        self.assertEqual(retained(eta, 3), F(27, 50))
        self.assertEqual(envelope(eps, eta, 3), F(94, 175))
        self.assertEqual(envelope(eps, eta, 0), eps)
        # All 0..T emissions are evaluated chronologically, not at final T.
        self.assertNotEqual(discounted_prefix(eps, eta, F(1, 2), 4),
                            (F(1)-F(1, 2)**4)*envelope(eps, eta, 3))

    def test_unit_defect_saturates_after_first_transition(self):
        eta = lambda t: F(1) if t == 0 else F(0)
        self.assertEqual(envelope(F(0), eta, 0), F(0))
        for n in range(1, 8):
            self.assertEqual(envelope(F(0), eta, n), F(1))

    def test_closed_form_uniform_defect(self):
        beta, eps, defect = F(1, 3), F(1, 5), F(1, 4)
        rhs = 1 - (1-eps)*(1-beta)/(1-beta*(1-defect))
        eta = lambda _: defect
        for n in (2, 5, 10, 25):
            partial = discounted_prefix(eps, eta, beta, n)
            self.assertLessEqual(partial, rhs)
            self.assertLessEqual(rhs-partial, beta**n)
        self.assertEqual(rhs, F(13, 45))

    def test_discounted_total_cannot_create_exact_survival(self):
        eta = lambda _: F(1, 1000)
        beta = F(1, 2)
        eps = F(0)
        self.assertEqual(envelope(eps, eta, 0), F(0))
        self.assertGreater(discounted_prefix(eps, eta, beta, 10), F(0))


if __name__ == "__main__":
    unittest.main()
