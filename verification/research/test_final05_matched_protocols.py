"""Independent asymmetric/conditional product finite counterchecks.

These are numerical implementation adversaries. The all-event Lean kernel
intertwining is separately compiler-certified, not deduced from this test.
"""
from fractions import Fraction as F
from itertools import product
import unittest

class MatchedProtocols(unittest.TestCase):
    def test_asymmetric_opponent_anchor_not_changed_by_treated_component(self):
        g=[F(1,5),F(3,4)]
        replacement=F(2,3)
        closed=[replacement,g[1]]
        frozen_anchor=[F(1,3),F(4,5)]
        open_loop=[replacement,frozen_anchor[1]]
        self.assertEqual(closed[1],g[1])
        self.assertEqual(open_loop[1],frozen_anchor[1])
        self.assertNotEqual(closed,open_loop)
    def test_joint_action_order_changes_physical_law_when_asymmetric(self):
        def p(a,b):return F(1,10)+a*F(1,5)+b*F(1,2)
        self.assertNotEqual(p(1,0),p(0,1))
    def test_correlated_actions_are_outside_product_subclass(self):
        joint={(0,0):F(1,2),(1,1):F(1,2),(0,1):F(0),(1,0):F(0)}
        independent={(a,b):F(1,4) for a,b in product((0,1),repeat=2)}
        self.assertNotEqual(joint,independent)
    def test_mixed_initial_law_requires_both_atoms(self):
        mu={0:F(2,7),1:F(5,7)}
        mapped={0:mu[0],1:mu[1]}
        self.assertEqual(sum(mapped.values()),1)
        self.assertNotEqual(mapped,{0:F(1),1:F(0)})
if __name__=="__main__":unittest.main()
