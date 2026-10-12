"""Exact finite negative controls for C2; not a substitute for Lean proofs.

All ratios, geometric tails and Cesaro frequencies use Fraction arithmetic.
The corresponding universal statements still require Lean quantifier proofs.
"""
from fractions import Fraction as Q
from unittest import TestCase


def cycle3(t):
    return t % 3


def cycle3_occupation(n):
    assert n > 0
    return tuple(Q(sum(cycle3(t) == j for t in range(n)), n)
                 for j in range(3))


def survival_u(n):
    return Q(1, 2) ** n


def a_weight_u_by_n(n):
    return Q(1, 3) * (1 - survival_u(n))


def b_weight_u_by_n(n):
    return Q(2, 3) * (1 - survival_u(n))


def delayed_escape_survival(escape_probability, n):
    assert 0 < escape_probability <= 1
    return (1 - escape_probability) ** n


class CounterexampleChecks(TestCase):
    def test_period_three_nonconstant_marginal_sequence(self):
        self.assertEqual([cycle3(n) for n in range(9)], [0, 1, 2]*3)
        self.assertNotEqual((Q(1), Q(0), Q(0)), (Q(0), Q(1), Q(0)))

    def test_period_three_exact_occupation(self):
        for n in range(1, 150):
            out = cycle3_occupation(n)
            self.assertEqual(sum(out), 1)
            self.assertLessEqual(max(abs(x-Q(1,3)) for x in out), Q(1,n))
        self.assertEqual(cycle3_occupation(300), (Q(1,3),)*3)

    def test_transient_survival_positive_at_every_finite_time(self):
        self.assertTrue(all(survival_u(n)>0 for n in range(40)))
        self.assertLess(survival_u(30), Q(1,1_000_000))

    def test_class_hitting_weight_limit_exact(self):
        for n in range(30):
            self.assertEqual(a_weight_u_by_n(n)+b_weight_u_by_n(n),
                             1-survival_u(n))
            self.assertLessEqual(a_weight_u_by_n(n), Q(1,3))
            self.assertLessEqual(b_weight_u_by_n(n), Q(2,3))
        self.assertLess(Q(1,3)-a_weight_u_by_n(30), Q(1,1_000_000))

    def test_no_kernel_independent_positive_entry_bound(self):
        for horizon in (1,2,3,10,20,100):
            for desired_lower_bound in (Q(1,10), Q(1,2), Q(9,10)):
                eps = desired_lower_bound / (2*horizon)
                actual_entry = 1-delayed_escape_survival(eps, horizon)
                self.assertLess(actual_entry, desired_lower_bound)
                self.assertGreater(eps,0)

    def test_physical_barycenter_not_a_realized_class_law(self):
        a=(Q(0),Q(0),Q(1,2),Q(1,2),Q(0),Q(0))
        b=(Q(0),Q(0),Q(0),Q(0),Q(1,3),Q(2,3))
        avg=tuple(Q(1,3)*a[i]+Q(2,3)*b[i] for i in range(6))
        self.assertNotEqual(a,b)
        self.assertNotEqual(avg,a)
        self.assertNotEqual(avg,b)
        self.assertEqual(sum(avg),1)

    def test_nonconstant_descriptor_collapses_distinct_classes(self):
        a={2:Q(1,2),3:Q(1,2)}
        b={4:Q(1,3),5:Q(2,3)}
        h=lambda i:i>=2
        def push(mu):
            return sum(p for i,p in mu.items() if h(i))
        self.assertEqual(push(a),1)
        self.assertEqual(push(b),1)
        self.assertNotEqual(a,b)
        self.assertFalse(h(1))

    def test_singleton_cannot_pass_descriptor_two_values(self):
        for f in (lambda x:False, lambda x:True, lambda x:x):
            self.assertEqual(len({f(x) for x in (0,)}),1)
