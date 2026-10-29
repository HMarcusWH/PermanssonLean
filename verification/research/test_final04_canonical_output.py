"""Independent exact Fraction tests for discounted common-mass envelopes."""
from fractions import Fraction as F
from math import prod
import unittest

def retained(eta,n):
    return prod((1-F(e) for e in eta[:n]),start=F(1))

def finite_error(beta,eta,epsilon,horizon):
    return sum(((1-beta)*beta**n*(1-(1-epsilon)*retained(eta,n))
               for n in range(horizon)),start=F(0))

class CanonicalEnvelope(unittest.TestCase):
    def test_frozen_geometric_exact_thirteen_fortyfive(self):
        b,e,a=F(1,3),F(1,5),F(1,4)
        analytic=1-(1-e)*(1-b)/(1-b*(1-a))
        self.assertEqual(analytic,F(13,45))
    def test_zero_row_error_keeps_initial_mismatch(self):
        self.assertEqual(1-(1-F(2,7))*(1-F(1,3))/
                         (1-F(1,3)),F(2,7))
    def test_chronological_defects_not_last_row(self):
        e=F(1,7)
        ds=[F(1,10),F(1,5),F(1,4)]
        self.assertEqual(retained(ds,3),F(27,50))
        self.assertEqual(finite_error(F(1,3),ds,e,4),
                         sum((F(2,3)*F(1,3)**n*
                              (1-F(6,7)*retained(ds,n))
                              for n in range(4)),F(0)))
    def test_intervention_only_reachable_row_charged(self):
        self.assertGreater(finite_error(F(1,2),[F(0),F(1,2)],F(0),3),0)
    def test_positive_leakage_cannot_certify_exact_retention(self):
        survival=(1-F(1,100))**500
        self.assertLess(survival,F(1,10))
if __name__=="__main__":unittest.main()
