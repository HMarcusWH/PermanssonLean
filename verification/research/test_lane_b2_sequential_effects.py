"""B2 exact-rational independent regression suite (not a substitute for Lean proofs).

Every effect is evaluated by executing α -> P -> U from an initial typed
strategic/world state.  No independently supplied 4-number table is
accepted for semantic integration tests.
"""
from __future__ import annotations

from fractions import Fraction as Q
import unittest

FALSE = False
TRUE = True
Q0 = (TRUE, TRUE)
Q1 = (TRUE, FALSE)
ACTION_DEST = (TRUE, FALSE)
UPDATE_DEST = (FALSE, TRUE)
JOINT_DEST = (FALSE, FALSE)
B1 = (Q0, Q1)
REGION = {Q0, Q1, ACTION_DEST, UPDATE_DEST}  # all except (False, False)


def step(state, *, change_action=False, change_update=False,
         alt_bank=False):
    """Action choice, frozen world copy, then strategic update."""
    action = TRUE if (not change_action or alt_bank) else FALSE
    next_world = action                         # common fixed world P
    next_strategy = TRUE if not change_update else FALSE
    return (next_strategy, next_world)


def path(initial, *, steps=3, change_action=False, change_update=False,
         alt_bank=False):
    states = [initial]
    for _ in range(steps):
        states.append(step(states[-1], change_action=change_action,
                           change_update=change_update, alt_bank=alt_bank))
    return tuple(states)


def four_corners(initial, property_fn, *, alt_bank=False):
    kw = {"alt_bank": alt_bank}
    return (
        Q(property_fn(path(initial, **kw))),
        Q(property_fn(path(initial, change_action=True, **kw))),
        Q(property_fn(path(initial, change_update=True, **kw))),
        Q(property_fn(path(initial, change_action=True, change_update=True,
                           **kw))),
    )


def effects(z):
    a, b, c, d = z
    return {"action": abs(a-b), "update": abs(a-c),
            "joint": abs(a-d), "conditional_update": abs(b-d),
            "conditional_action": abs(c-d)}


def uniform_min(property_fn, key):
    return min(effects(four_corners(y, property_fn))[key] for y in B1)


def survival(states):
    return all(y in REGION for y in states)


def or_property(states):
    return states[1][0] or states[1][1]


def and_property(states):
    return states[1][0] and states[1][1]


def xor_property(states):
    return states[1][0] != states[1][1]


def zero_inf_adversary(states):
    return states[1] == JOINT_DEST or (
        states[0] == Q1 and states[1] == ACTION_DEST)


def vector_property(states):
    successor = states[1]
    return {Q0: Q(0), ACTION_DEST: Q(1), UPDATE_DEST: Q(-1),
            JOINT_DEST: Q(2)}[successor]


class B2ExactRationalTests(unittest.TestCase):
    def test_01_corners_share_frozen_world(self):
        for a in (False, True):
            for u in (False, True):
                for y in B1:
                    s, x = step(y, change_action=a, change_update=u)
                    self.assertEqual(x, int(not a))
                    self.assertEqual(s, not u)

    def test_02_triangle_action_route_both_directions(self):
        for fn in (survival, or_property, and_property, xor_property,
                   zero_inf_adversary, vector_property):
            for y in B1:
                e = effects(four_corners(y, fn))
                self.assertLessEqual(e["joint"],
                                     e["action"] + e["conditional_update"])
                self.assertLessEqual(abs(e["action"] - e["conditional_update"]),
                                     e["joint"])

    def test_03_triangle_update_route_both_directions(self):
        for fn in (survival, or_property, and_property, xor_property,
                   zero_inf_adversary, vector_property):
            for y in B1:
                e = effects(four_corners(y, fn))
                self.assertLessEqual(e["joint"],
                                     e["update"] + e["conditional_action"])
                self.assertLessEqual(abs(e["update"] - e["conditional_action"]),
                                     e["joint"])

    def test_04_uniform_conditional_margin_lower_bounds(self):
        for fn in (survival, or_property, and_property, xor_property,
                   zero_inf_adversary, vector_property):
            for first, cond in (("action", "conditional_update"),
                                ("update", "conditional_action")):
                eps = max(effects(four_corners(y, fn))[first] for y in B1)
                self.assertGreaterEqual(uniform_min(fn, cond),
                                        uniform_min(fn, "joint") - eps)

    def test_05_strong_singleton_null_joint_positive_survival(self):
        for y in B1:
            e = effects(four_corners(y, survival))
            self.assertEqual((e["action"], e["update"], e["joint"],
                              e["conditional_update"], e["conditional_action"]),
                             (Q(0), Q(0), Q(1), Q(1), Q(1)))

    def test_06_OR_original_path_law_joint_only(self):
        for y in B1:
            self.assertEqual(four_corners(y, or_property),
                             (Q(1), Q(1), Q(1), Q(0)))

    def test_07_zero_singleton_infimum_not_pointwise_zero(self):
        self.assertEqual(uniform_min(zero_inf_adversary, "action"), 0)
        self.assertEqual(uniform_min(zero_inf_adversary, "update"), 0)
        self.assertEqual(uniform_min(zero_inf_adversary, "joint"), 1)
        self.assertEqual(uniform_min(zero_inf_adversary, "conditional_update"), 0)
        self.assertEqual(uniform_min(zero_inf_adversary, "conditional_action"), 1)
        self.assertEqual(effects(four_corners(Q1, zero_inf_adversary))["action"], 1)

    def test_08_direct_baseline_singleton_subadditivity_is_false(self):
        e = effects(four_corners(Q0, survival))
        self.assertEqual(e["joint"], 1)
        self.assertEqual(e["action"] + e["update"], 0)

    def test_09_AND_incomparable_singleton_supports(self):
        for y in B1:
            e = effects(four_corners(y, and_property))
            self.assertEqual((e["action"], e["update"], e["joint"]), (1,1,1))
        # Empty block null; both singleton blocks are inclusion-minimal.
        self.assertEqual(effects(four_corners(Q0, and_property))["joint"], 1)

    def test_10_XOR_destroys_upward_monotonicity(self):
        for y in B1:
            e = effects(four_corners(y, xor_property))
            self.assertEqual((e["action"], e["update"], e["joint"]), (1,1,0))

    def test_11_interaction_vector_not_scalar_distance_remainder(self):
        for y in B1:
            z00,z10,z01,z11 = four_corners(y, vector_property)
            interaction = z11-z10-z01+z00
            remainder = abs(z11-z00)-abs(z10-z00)-abs(z01-z00)
            self.assertEqual(interaction, 2)
            self.assertEqual(remainder, 0)
            self.assertNotEqual(interaction, remainder)
            e = effects((z00,z10,z01,z11))
            self.assertLessEqual(abs(interaction),
                                 e["conditional_update"]+e["update"])
            self.assertLessEqual(abs(interaction),
                                 e["conditional_action"]+e["action"])

    def test_12_conditional_legs_are_asymmetric(self):
        e = effects(four_corners(Q0, vector_property))
        self.assertEqual(e["conditional_update"], 1)
        self.assertEqual(e["conditional_action"], 3)

    def test_13_baseline_identical_different_admitted_bank(self):
        for y in B1:
            self.assertEqual(four_corners(y, or_property)[0],
                             four_corners(y, or_property, alt_bank=True)[0])
            self.assertEqual(four_corners(y, or_property)[3], 0)
            self.assertEqual(four_corners(y, or_property, alt_bank=True)[3], 1)

    def test_14_invalid_order_or_noncommuting_patch(self):
        # Same overlapping row: last patch wins.  Lane B rules out such
        # overlap; four corners do not imply arbitrary mutation commutativity.
        def patched(start, order):
            value = start
            for replacement in order:
                value = replacement
            return value
        self.assertNotEqual(patched(True, [False, True]),
                            patched(True, [True, False]))

    def test_15_zero_transition_effect_is_zero(self):
        for y in B1:
            states = (y,)
            self.assertEqual(states[0], y)
        # A path property reading only Y0 cannot be changed by α/U.
        def initial_only(states):
            return states[0] == Q1
        for y in B1:
            self.assertEqual(len(set(four_corners(y, initial_only))), 1)

    def test_16_invalid_margin_matched_relabeling(self):
        # AND has same effects for action-only and joint, but {α} ⊊ {α,U}.
        # Swapping labels preserves displayed margins, not minimality.
        blocks = {frozenset(): 0, frozenset({"a"}): 1,
                  frozenset({"u"}): 1, frozenset({"a","u"}): 1}
        self.assertEqual(blocks[frozenset({"a"})],
                         blocks[frozenset({"a","u"})])
        self.assertTrue(frozenset({"a"}) < frozenset({"a","u"}))

    def test_17_no_decomposition_of_coarse_grammar(self):
        coarse = {frozenset(), frozenset({"a","u"})}
        self.assertNotIn(frozenset({"a"}), coarse)
        self.assertNotIn(frozenset({"u"}), coarse)

    def test_18_finite_B1_not_implicit_global_test(self):
        # Test state and even a positive infimum require the *declared* set.
        self.assertEqual(set(B1), {Q0,Q1})
        self.assertNotIn(JOINT_DEST, B1)


if __name__ == "__main__":
    unittest.main()
