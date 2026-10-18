"""Independent finite-word boundary checks, separate from Lean proof evidence."""
from fractions import Fraction as Q
from itertools import product
import unittest


def retry_scan(word, m):
    streak, success = 0, False
    for target, _ in word:
        streak = min(m + 1, streak + 1) if target else 0
        success |= streak == m + 1
    return success


def first_scan(word, T, m):
    phase, count = "waiting", 0
    for t, (target, _) in enumerate(word):
        if phase in {"failed", "succeeded"}:
            continue
        if phase == "waiting":
            if t > T:
                phase = "failed"
            elif target:
                count = 1
                phase = "succeeded" if m == 0 else "active"
        elif not target:
            phase = "failed"
        else:
            count += 1
            if count == m + 1:
                phase = "succeeded"
    return phase == "succeeded"


def avoid_scan(word, m):
    streak, success, failed = 0, False, False
    for target, danger in word:
        if success or failed:
            continue
        if danger:
            failed = True
        else:
            streak = min(m + 1, streak + 1) if target else 0
            success = streak == m + 1
    return success


class LiteralEventTests(unittest.TestCase):
    def test_all_short_physical_words(self):
        alphabet = list(product([False, True], repeat=2))
        checked = 0
        for T in range(3):
            for m in range(3):
                for word in product(alphabet, repeat=T + m + 1):
                    runs = [e for e in range(T + 1)
                            if all(word[e + j][0] for j in range(m + 1))]
                    first = next((t for t, z in enumerate(word) if z[0]), None)
                    literal_first = first is not None and first <= T and all(
                        word[first + j][0] for j in range(m + 1))
                    literal_avoid = any(all(not word[t][1] for t in range(e + m + 1))
                                        for e in runs)
                    self.assertEqual(retry_scan(word, m), bool(runs))
                    self.assertEqual(first_scan(word, T, m), literal_first)
                    self.assertEqual(avoid_scan(word, m), literal_avoid)
                    checked += 1
        self.assertEqual(checked, 1764)

    def test_retry_first_and_danger_boundaries(self):
        word = [(True, False), (False, False), (True, False), (True, False)]
        self.assertTrue(retry_scan(word, 1))
        self.assertFalse(first_scan(word, 2, 1))
        self.assertFalse(avoid_scan([(True, True)], 0))
        self.assertTrue(avoid_scan([(True, False), (False, True)], 0))

    def test_exact_stationary_reference_two_states(self):
        for epsilon in [Q(1), Q(1, 1000), Q(1, 10**9)]:
            P = [[1 - epsilon, epsilon], [epsilon, 1 - epsilon]]
            M = [[(1 if i == j else 0) - P[j][i] + 1 for j in range(2)]
                 for i in range(2)]
            determinant = M[0][0] * M[1][1] - M[0][1] * M[1][0]
            self.assertNotEqual(determinant, 0)
            weights = [(M[1][1] - M[0][1]) / determinant,
                       (M[0][0] - M[1][0]) / determinant]
            self.assertEqual(weights, [Q(1, 2), Q(1, 2)])
            self.assertEqual(sum(weights), 1)
            self.assertEqual([sum(weights[i] * P[i][j] for i in range(2))
                              for j in range(2)], weights)


if __name__ == "__main__":
    unittest.main()
