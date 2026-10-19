"""NEXT-03 / F-05: independent rational model numbers for the Lean SCM fixture."""
from fractions import Fraction as Q
import itertools
import unittest


def mediator(t, u):
    return (not u) if t else u


def outcome(t, m):
    return (4 if m else 2) if t else (3 if m else 1)


def law(t, tp):
    return sum((w * outcome(t, mediator(tp, u))
                for u, w in ((False, Q(1, 3)), (True, Q(2, 3)))), Q(0))


class PositiveMediationArithmetic(unittest.TestCase):
    def test_all_conditionals_have_strict_positive_denominators(self):
        for t, m in itertools.product([False, True], repeat=2):
            pm = sum((p for u, p in ((False,Q(1,3)),(True,Q(2,3)))
                      if mediator(t,u)==m), Q(0))
            self.assertGreater(Q(1,2)*pm, 0)

    def test_exact_four_nested_values(self):
        self.assertEqual([law(False,False),law(False,True),law(True,False),law(True,True)],
                         [Q(7,3),Q(5,3),Q(10,3),Q(8,3)])

    def test_mediator_matters_not_only_direct_treatment(self):
        self.assertNotEqual(law(True,False),law(True,True))
        self.assertEqual(law(True,False)-law(True,True),Q(2,3))

    def test_positive_observational_formula(self):
        for t,tp in itertools.product([False,True], repeat=2):
            # Conditional outcome is the exact deterministic response; conditional
            # mediator is treatment-specific and available at every cell.
            observed = sum((outcome(t,m)*sum((p for u,p in
                            ((False,Q(1,3)),(True,Q(2,3)))
                            if mediator(tp,u)==m),Q(0)) for m in [False,True]),Q(0))
            self.assertEqual(observed,law(t,tp))

if __name__ == '__main__':
    unittest.main()
