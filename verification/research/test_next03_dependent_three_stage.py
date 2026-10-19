"""Independent exhaustive finite-event TV for dependent three-stage histories."""
from fractions import Fraction as F
from itertools import product, combinations
import unittest

HISTORY = tuple(product((False, True), repeat=3))


def follow(previous: bool, current: bool, defect: F) -> F:
    if not previous:
        return F(0) if current else F(1)
    return F(1) - defect if current else defect


def law(w):
    a, b, c = w
    return (F(9, 10) if a else F(1, 10)) * follow(a, b, F(1, 5)) * follow(b, c, F(1, 4))


def perfect(w):
    return F(1) if w == (True, True, True) else F(0)


class DependentThreeStage(unittest.TestCase):
    def test_complete_eight_history_law_is_normalized(self):
        self.assertEqual(len(HISTORY), 8)
        self.assertEqual(sum((law(w) for w in HISTORY), F()), F(1))
        self.assertEqual(sum((perfect(w) for w in HISTORY), F()), F(1))
        self.assertTrue(all(0 <= law(w) <= 1 for w in HISTORY))

    def test_true_conditional_history_dependence(self):
        self.assertEqual(follow(False, True, F(1, 5)), F(0))
        self.assertEqual(follow(True, True, F(1, 5)), F(4, 5))
        self.assertEqual(follow(False, True, F(1, 4)), F(0))
        self.assertEqual(follow(True, True, F(1, 4)), F(3, 4))

    def test_realized_good_history_and_retained_product(self):
        self.assertEqual(law((True, True, True)), F(27, 50))
        self.assertEqual(F(9, 10) * F(4, 5) * F(3, 4), F(27, 50))
        self.assertEqual(sum((law(w) for w in HISTORY if w != (True, True, True)), F()), F(23, 50))

    def test_all_256_events_and_half_l1_equal_exact_tv(self):
        # Exhaustively enumerate every subset, not just a selected event.
        max_event = F(0)
        for mask in range(1 << len(HISTORY)):
            event = (w for i, w in enumerate(HISTORY) if mask & (1 << i))
            difference = abs(sum((law(w) - perfect(w) for w in event), F()))
            max_event = max(max_event, difference)
        half_l1 = sum((abs(law(w) - perfect(w)) for w in HISTORY), F()) / 2
        self.assertEqual(max_event, F(23, 50))
        self.assertEqual(half_l1, F(23, 50))


if __name__ == '__main__':
    unittest.main()
