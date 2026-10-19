"""Independent exact one-prior two-reachable-history Bayesian calculation."""
from fractions import Fraction as F
import unittest

PRIOR = {False: F(1), True: F(0)}
POLICY = {False: F(1, 2), True: F(1, 2)}


def transition(flag, action, next_flag):
    del flag
    return F(int(action == next_flag))


def observation(next_flag, action, readout):
    del next_flag, action
    return F(int(readout == ()))


def actual_word_mass(action):
    return POLICY[action] * sum((PRIOR[z] * transition(z, action, y) *
        observation(y, action, ()) for z in PRIOR for y in PRIOR), F())


def posterior_true(action):
    numerator = sum((PRIOR[z] * transition(z, action, True) *
        observation(True, action, ()) for z in PRIOR), F())
    likelihood = sum((PRIOR[z] * transition(z, action, y) *
        observation(y, action, ()) for z in PRIOR for y in PRIOR), F())
    return numerator / likelihood


class ReachableCompletionBelief(unittest.TestCase):
    def test_single_initial_law_is_normalized(self):
        self.assertEqual(sum(PRIOR.values(), F()), F(1))
        self.assertEqual(sum(POLICY.values(), F()), F(1))

    def test_both_histories_have_mass_under_the_same_law(self):
        self.assertEqual(actual_word_mass(False), F(1, 2))
        self.assertEqual(actual_word_mass(True), F(1, 2))
        self.assertEqual(actual_word_mass(False) + actual_word_mass(True), F(1))

    def test_same_physical_readout_does_not_identify_completion(self):
        self.assertEqual(posterior_true(False), F(0))
        self.assertEqual(posterior_true(True), F(1))
        self.assertEqual(observation(False, False, ()), observation(True, True, ()))

    def test_no_false_zero_denominator(self):
        for a in POLICY:
            self.assertNotEqual(actual_word_mass(a), F(0))
            self.assertTrue(0 <= posterior_true(a) <= 1)


if __name__ == '__main__':
    unittest.main()
