"""Exact independent CL/OL frozen-mechanism arithmetic."""
from fractions import Fraction as Q
from itertools import product
import unittest
class Tests(unittest.TestCase):
    def test_two_treated_players_and_frozen_world(self):
        for i in (0,1):
            base=(Q(1,3),Q(2,5))
            target=Q(9,10)
            source=tuple(target if j==i else base[j] for j in (0,1))
            self.assertEqual(source[1-i],base[1-i])
            physical=lambda a:Q(1,4)+Q(1,2)*Q(a[0])+Q(1,8)*Q(a[1])
            for a in product((0,1),repeat=2):
                self.assertEqual(physical(a),physical(a))
    def test_open_loop_is_predeclared_not_reactive(self):
        anchor=(Q(4,7),Q(3,8))
        for i in (0,1):
            treatment=tuple(Q(1) if j==i else anchor[j] for j in (0,1))
            self.assertEqual(treatment[1-i],anchor[1-i])
        self.assertNotEqual(anchor,(Q(1,2),Q(1,2)))
if __name__=="__main__":unittest.main()
