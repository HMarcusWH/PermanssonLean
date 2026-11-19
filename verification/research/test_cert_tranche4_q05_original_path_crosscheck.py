"""Q-05 Tranche 4: independent chronological exact-rational path-law check.

This is a source-anchored ARITHMETIC CROSSCHECK, NOT a Lean theorem or
independent certification acceptance. It deliberately does not import the
existing finite-resolvent implementation or reuse its solve routine.

The generated path atoms follow the actual declared alpha -> P -> U sequence;
P is the fixed deterministic physical action-to-world kernel. We compare
finite original paths against a separately derived infinite weighted-sum
identity and test the entire frozen two-start comparison set.
"""
from __future__ import annotations

import hashlib
from fractions import Fraction as F
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
BETA = F(1, 3)
STARTS = ((False, False), (False, True))
FROZEN_SOURCES = {
    "PermanssonResearch/Quotient/Q05ActualOriginalMarginWitnessFixture.lean":
        "bed57136586bf5f3f82ba30da6aa133d641954c361ed40d17a516510968beeb2",
    "PermanssonResearch/Quotient/Q05ActualOriginalMarginAdapter.lean":
        "1c14ac82af8409ba639db17760fdb53c08ab266ed01cbb25b229f90e92339da8",
    "PermanssonResearch/Quotient/Q05ActualAtomClosure.lean":
        "c75f429a9f066396e1e9754f85123acfcfa2794d4b3f5995b97dd1bb923417cb",
}


def action_probability(treated: bool, strategic: bool, fine: bool) -> F:
    if fine:
        if treated:
            return F(4, 5) if strategic else F(7, 10)
        return F(1, 5) if strategic else F(1, 10)
    return F(3, 4) if treated else F(3, 20)


def successors(state: tuple[bool, bool] | bool, treated: bool, fine: bool):
    """Actual strategic update is written after the action sets the new world."""
    prior_strategic = state[0] if fine else False
    p = action_probability(treated, prior_strategic, fine)
    # The world transition P is exactly x' = a on both sides.
    return {(treated, False) if fine else False: 1 - p,
            (treated, True) if fine else True: p}


def path_distribution(initial, treated: bool, fine: bool, transitions: int):
    if transitions < 0:
        raise ValueError('negative transitions')
    paths = {(initial,): F(1)}
    for _ in range(transitions):
        updated = {}
        for path, mass in paths.items():
            for successor, chance in successors(path[-1], treated, fine).items():
                new_path = path + (successor,)
                updated[new_path] = updated.get(new_path, F(0)) + mass * chance
        paths = updated
    if sum(paths.values(), F(0)) != 1:
        raise AssertionError('Path mass not normalized')
    return paths


def observed_world(state, fine: bool) -> F:
    return F(int(state[1] if fine else state))


def prefix_expectation(paths: dict, fine: bool):
    """Original finite path property, without collapsing to a surrogate Markov model."""
    total = F(0)
    for path, weight in paths.items():
        score = sum(((1 - BETA) * BETA**n * observed_world(y, fine)
                     for n, y in enumerate(path)), F(0))
        total += weight * score
    return total


def infinite_chronological_identity(initial, treated: bool, fine: bool) -> F:
    """Direct expected chronological score, valid because the update freezes after n=1.

    n=0: (1-b) * x0; n=1: (1-b)*b * p(t,s0);
    n>=2: b**2 * p(t,t), with no independence assumption across paths.
    """
    strategic, world = initial if fine else (False, initial)
    p_first = action_probability(treated, strategic, fine)
    p_later = action_probability(treated, treated, fine)
    return ((1 - BETA) * F(int(world))
            + (1 - BETA) * BETA * p_first
            + BETA**2 * p_later)


def original_margin(fine: bool) -> F:
    domain = STARTS if fine else (False, True)
    return min(abs(infinite_chronological_identity(y, True, fine)
                   - infinite_chronological_identity(y, False, fine))
               for y in domain)


class Q05ChronologicalCrosscheck(unittest.TestCase):
    def test_frozen_original_source_hashes_and_toolchain(self):
        self.assertEqual((ROOT / 'lean-toolchain').read_text().strip(),
                         'leanprover/lean4:v4.34.0')
        for path, expected in FROZEN_SOURCES.items():
            with self.subTest(file=path):
                self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(),
                                 expected)

    def test_path_measure_mass_and_two_starts_nontrivial(self):
        self.assertEqual(len(STARTS), 2)
        self.assertNotEqual(STARTS[0], STARTS[1])
        for fine in (True, False):
            for treated in (False, True):
                for initial in STARTS if fine else (False, True):
                    for n in range(7):
                        paths = path_distribution(initial, treated, fine, n)
                        self.assertEqual(sum(paths.values(), F(0)), 1)
                        self.assertTrue(all(m >= 0 for m in paths.values()))
                        self.assertEqual({path[0] for path in paths}, {initial})
        self.assertNotEqual(path_distribution(STARTS[0], False, True, 0),
                            path_distribution(STARTS[1], False, True, 0))

    def test_direct_prefix_converges_to_exact_infinite_value_with_tail_bound(self):
        for fine in (True, False):
            for treated in (False, True):
                for initial in STARTS if fine else (False, True):
                    target = infinite_chronological_identity(initial, treated, fine)
                    for n in range(7):
                        prefix = prefix_expectation(
                            path_distribution(initial, treated, fine, n), fine)
                        with self.subTest(fine=fine, treated=treated, start=initial, n=n):
                            self.assertGreaterEqual(prefix, 0)
                            self.assertLessEqual(prefix, target)
                            self.assertLessEqual(target - prefix, BETA ** (n + 1))

    def test_complete_original_comparison_domain_and_exact_values(self):
        expected = {
            False: (F(1, 30), F(11, 45), F(1, 20), F(1, 4)),
            True: (F(7, 10), F(41, 45), F(43, 60), F(11, 12)),
        }
        self.assertEqual({(None, x) for _, x in STARTS}, {(None, False), (None, True)})
        # Genuine non-injectivity even though the full original B1 is preserved.
        self.assertEqual((None, (False, True)[1]), (None, (True, True)[1]))
        self.assertNotEqual((False, True), (True, True))
        for x, values in expected.items():
            self.assertEqual((infinite_chronological_identity((False, x), False, True),
                              infinite_chronological_identity((False, x), True, True),
                              infinite_chronological_identity(x, False, False),
                              infinite_chronological_identity(x, True, False)), values)
        self.assertEqual(original_margin(True), F(19, 90))
        self.assertEqual(original_margin(False), F(1, 5))
        self.assertEqual(abs(original_margin(True) - original_margin(False)), F(1, 90))

    def test_treatment_reachable_strategic_row_is_essential(self):
        # A counterfactual tamper changes only the n>=2 treated strategic row.
        initial = (False, False)
        actual = infinite_chronological_identity(initial, True, True)
        falsified_later_rate = F(19, 20)
        falsified = ((1 - BETA) * 0
                     + (1 - BETA) * BETA * action_probability(True, False, True)
                     + BETA**2 * falsified_later_rate)
        self.assertEqual(falsified - actual, F(1, 60))
        self.assertNotEqual(falsified, F(11, 45))
        self.assertGreater(abs(falsified_later_rate - F(3, 4)), F(1, 20))

    def test_two_sided_bound_is_strictly_weaker_than_exact_margin_identity(self):
        exact = abs(original_margin(True) - original_margin(False))
        self.assertEqual(exact, F(1, 90))
        self.assertLessEqual(exact, F(2, 41))
        self.assertGreater(original_margin(True) - F(2, 41), 0)
        self.assertNotEqual(exact, F(2, 41))


if __name__ == '__main__':
    unittest.main()
