"""Independent exact Fraction checks of NEXT-04 2-sided discounted bound."""
from fractions import Fraction as Q
import unittest
def bound(beta,eta,eps): return 1-(1-eps)*(1-beta)/(1-beta*(1-eta))
class Tests(unittest.TestCase):
    def test_declared_exact_13_over_45(self):
        self.assertEqual(bound(Q(1,3),Q(1,4),Q(1,5)),Q(13,45))
    def test_beta_zero_only_initial(self):
        self.assertEqual(bound(Q(0),Q(1,4),Q(1,5)),Q(1,5))
        self.assertEqual(bound(Q(0),Q(1,4),Q(0)),Q(0))
    def test_no_row_defect_keeps_initial_error(self):
        self.assertEqual(bound(Q(1,2),Q(0),Q(1,5)),Q(1,5))
    def test_chronological_dependent_product(self):
        defects=[Q(1,10),Q(1,5),Q(1,4)]
        retained=Q(1)
        for d in defects: retained*=1-d
        self.assertEqual(retained,Q(27,50)*Q(3,4))
        self.assertNotEqual(retained,(1-defects[-1])**3)
    def test_original_full_set_minimum(self):
        effects={0:Q(1,8),1:Q(3,8),2:Q(1,2)}
        full=min(effects.values())
        omitted=min(v for k,v in effects.items() if k!=0)
        self.assertNotEqual(full,omitted)
    def test_both_error_sides(self):
        e0,eJ=Q(1,10),Q(1,5)
        self.assertEqual(e0+eJ,Q(3,10))
        reported=Q(1,4)
        self.assertLessEqual(abs(reported-Q(1,5)),Q(1,10))
if __name__=="__main__":unittest.main()
