"""Exact rational NEXT-04 source-bridge accounting, not a Lean certificate."""
from fractions import Fraction as F
import unittest


def retained(defects, n):
    factor=F(1)
    for eta in defects[:n]:
        factor *= 1-eta
    return factor


def bound(beta, eps, defects, n):
    return (1-beta)*beta**n*(1-(1-eps)*retained(defects,n))


class CanonicalDiscountedBounds(unittest.TestCase):
    def test_point_start_is_identical_at_time_zero(self):
        for beta in (F(0),F(1,3),F(9,10)):
            self.assertEqual(bound(beta,F(0),[F(1,4)],0),F(0))
        self.assertEqual(bound(F(0),F(1,5),[F(1,4)],0),F(1,5))

    def test_nonzero_initial_error_is_retained(self):
        beta,eps,eta=F(1,3),F(1,5),F(1,4)
        closed=1-(1-eps)*(1-beta)/(1-beta*(1-eta))
        self.assertEqual(closed,F(13,45))
        self.assertNotEqual(closed,1-(1-beta)/(1-beta*(1-eta)))

    def test_chronological_defects(self):
        ds=[F(1,10),F(1,5),F(1,4)]
        self.assertEqual(retained(ds,0),F(1))
        self.assertEqual(retained(ds,1),F(9,10))
        self.assertEqual(retained(ds,2),F(18,25))
        self.assertEqual(retained(ds,3),F(27,50))
        self.assertEqual(1-retained(ds,3),F(23,50))

    def test_intervention_reachable_only_row_is_charged(self):
        baseline=[F(0),F(0),F(0)]
        intervention=[F(0),F(1,2),F(0)]
        self.assertEqual(1-retained(baseline,3),F(0))
        self.assertEqual(1-retained(intervention,3),F(1,2))
        self.assertNotEqual(retained(baseline,3),retained(intervention,3))

    def test_unit_defect_saturates_after_transition(self):
        defects=[F(0),F(1)]
        self.assertEqual(retained(defects,1),F(1))
        self.assertEqual(retained(defects,2),F(0))


if __name__=="__main__":
    unittest.main()
