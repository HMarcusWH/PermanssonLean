"""Independent exact rational enumeration for D-05's actual two-stage laws.

Does not claim Lean compilation or identification of any empirical process.
"""
from fractions import Fraction as F
import unittest


def stage_row(model: bool, second: bool) -> F:
    return F(1, 10) if model == second else F(9, 10)


def path_law(model0: bool, model1: bool) -> dict[tuple[bool, bool], F]:
    out = {}
    for first in (False, True):
        for second in (False, True):
            p0 = stage_row(model0, False)
            p1 = stage_row(model1, True)
            out[(first, second)] = (p0 if first else 1 - p0) * (p1 if second else 1 - p1)
    return out


class CommittedVsRectangular(unittest.TestCase):
    def test_all_four_chronological_atoms_are_normalized(self):
        for m0 in (False, True):
            for m1 in (False, True):
                with self.subTest(models=(m0, m1)):
                    law = path_law(m0, m1)
                    self.assertEqual(len(law), 4)
                    self.assertTrue(all(0 <= v <= 1 for v in law.values()))
                    self.assertEqual(sum(law.values(), F()), F(1))

    def test_committed_model_identity_persists_between_stages(self):
        def event(m0, m1):
            return path_law(m0, m1)[(True, True)]
        self.assertEqual(event(False, False), F(9, 100))
        self.assertEqual(event(True, True), F(9, 100))
        self.assertEqual(min(event(False, False), event(True, True)), F(9, 100))

    def test_rectangular_reselection_is_a_different_path_law(self):
        committed = path_law(False, False)
        switched = path_law(False, True)
        self.assertNotEqual(committed, switched)
        self.assertEqual(switched[(True, True)], F(1, 100))
        self.assertEqual(switched[(True, True)] * 9, F(9, 100))

    def test_not_a_false_universal_independence_claim(self):
        # These are declared independent conditionally on the selected stage
        # rows, not a theorem about arbitrary history-dependent or hidden laws.
        self.assertEqual(path_law(False, True)[(False, False)], F(81, 100))
        self.assertEqual(path_law(False, False)[(False, False)], F(9, 100))


if __name__ == '__main__':
    unittest.main()
