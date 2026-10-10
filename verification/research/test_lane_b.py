"""Independent exact finite-state regressions for Lane B partition grammars.

These calculate deterministic Markov transition matrices independently from
the Lean implementation.  They do not constitute proof of Lean theorem types.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations
import unittest

STATES = tuple((s, x) for s in (False, True) for x in (False, True))
BASIN = {(True, True), (True, False)}
REGION = {(True, True), (True, False), (False, True)}
FINE = {"action": frozenset({"a"}), "update": frozenset({"u"})}
COARSE = {"combined": frozenset({"a", "u"})}


def all_blocks(components):
    keys = tuple(components)
    return tuple(frozenset(x) for n in range(len(keys) + 1)
                 for x in combinations(keys, n))


def expand(grammar, block):
    return frozenset().union(*(grammar[k] for k in block))


def transition(state, selected):
    """World copies action; update writes memory. P is unchanged by patches."""
    action = "a" not in selected
    updated = "u" not in selected
    return (updated, action)


def kernel(selected):
    return {state: {dst: Fraction(int(dst == transition(state, selected)))
                    for dst in STATES} for state in STATES}


def next_value(selected, predicate, state):
    return sum((prob for next_state, prob in kernel(selected)[state].items()
                if predicate(next_state)), Fraction(0))


def forever_in_region(selected, start):
    if start not in REGION:
        return Fraction(0)
    after = transition(start, selected)
    # Every future state equals 'after' because the deterministic patches
    # cover all rows, hence first-transition survival = forever survival.
    return Fraction(int(after in REGION))


def effect(selected, predicate):
    baseline = next_value(frozenset(), predicate, (True, True))
    actual = next_value(selected, predicate, (True, True))
    return abs(actual - baseline)


def minimal_blocks(grammar, predicate):
    blocks = all_blocks(grammar)
    effective = {b for b in blocks if effect(expand(grammar, b), predicate) > 0}
    return {b for b in effective if not any(e < b for e in effective)}


class LaneBExactRegressions(unittest.TestCase):
    def test_all_rows_normalized_as_exact_fractions(self):
        for selected in (frozenset(), frozenset({"a"}), frozenset({"u"}),
                         frozenset({"a", "u"})):
            for row in kernel(selected).values():
                self.assertEqual(sum(row.values()), Fraction(1))
                self.assertTrue(all(p >= 0 for p in row.values()))

    def test_or_joint_only(self):
        predicate = lambda y: y[0] or y[1]
        result = {b: effect(expand(FINE, b), predicate) for b in all_blocks(FINE)}
        self.assertEqual(result[frozenset()], 0)
        self.assertEqual(result[frozenset({"action"})], 0)
        self.assertEqual(result[frozenset({"update"})], 0)
        self.assertEqual(result[frozenset({"action", "update"})], 1)
        self.assertEqual(minimal_blocks(FINE, predicate),
                         {frozenset({"action", "update"})})

    def test_and_incomparable_minima(self):
        predicate = lambda y: y[0] and y[1]
        self.assertEqual(minimal_blocks(FINE, predicate),
                         {frozenset({"action"}), frozenset({"update"})})
        self.assertEqual(minimal_blocks(COARSE, predicate),
                         {frozenset({"combined"})})

    def test_xor_nonmonotone(self):
        predicate = lambda y: y[0] != y[1]
        self.assertEqual(effect(frozenset({"a"}), predicate), 1)
        self.assertEqual(effect(frozenset({"u"}), predicate), 1)
        self.assertEqual(effect(frozenset({"a", "u"}), predicate), 0)

    def test_nonbijective_coarsening_transports_actual_kernels(self):
        coarse_block = frozenset({"combined"})
        fine_lift = frozenset({"action", "update"})
        self.assertEqual(expand(COARSE, coarse_block),
                         expand(FINE, fine_lift))
        self.assertEqual(kernel(expand(COARSE, coarse_block)),
                         kernel(expand(FINE, fine_lift)))
        self.assertEqual(len(fine_lift), 2)
        self.assertEqual(len(coarse_block), 1)

    def test_forever_persistence_effect(self):
        for start in BASIN:
            self.assertEqual(forever_in_region(frozenset(), start), 1)
            self.assertEqual(forever_in_region(frozenset({"a"}), start), 1)
            self.assertEqual(forever_in_region(frozenset({"u"}), start), 1)
            self.assertEqual(forever_in_region(frozenset({"a", "u"}), start), 0)

    def test_baseline_absorbing_occupation_analytic_formula(self):
        dest = (True, True)
        for start in BASIN:
            for n in range(1, 51):
                visited = [start] + [dest] * (n - 1)
                for point in STATES:
                    actual = Fraction(visited.count(point), n)
                    formula = ((Fraction(1, n) if point == start else 0)
                               + (Fraction(n - 1, n) if point == dest else 0))
                    self.assertEqual(actual, formula)

    def test_baseline_cannot_identify_atom_bank(self):
        alternate = lambda state: (True, False)
        self.assertNotEqual(transition((True, True), frozenset({"a", "u"})),
                            alternate((True, True)))
        self.assertEqual(transition((True, True), frozenset()),
                         (True, True))

    def test_effect_preserving_label_bijection_can_fail_minimality(self):
        pred = lambda y: y[0] and y[1]
        singleton = frozenset({"action"})
        compound = frozenset({"action", "update"})
        self.assertEqual(effect(expand(FINE, singleton), pred),
                         effect(expand(FINE, compound), pred))
        self.assertIn(singleton, minimal_blocks(FINE, pred))
        self.assertNotIn(compound, minimal_blocks(FINE, pred))

    def test_two_disjoint_action_row_masks(self):
        masks = {"left": {(False, False)}, "right": {(True, True)}}
        self.assertFalse(masks["left"] & masks["right"])
        selected = {"left"}
        def action_after_patches(state):
            if state in masks["left"] and "left" in selected:
                return False
            if state in masks["right"] and "right" in selected:
                return False
            return True
        self.assertFalse(action_after_patches((False, False)))
        self.assertTrue(action_after_patches((True, True)))
        self.assertTrue(action_after_patches((False, True)))


if __name__ == "__main__":
    unittest.main()
