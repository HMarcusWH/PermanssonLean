"""Exact Fraction oracle for the native two-player alpha->P->U transition.

Independent next-state-first and action-first constructions over 16 joint
states and four joint actions. This is finite regression evidence, not the
Lean proof for arbitrary measurable coordinates.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import unittest

BITS = (False, True)
STATES = tuple(product(BITS, repeat=4))
ACTIONS = tuple(product(BITS, repeat=2))

def bern(x, p):
    return p if x else Q(1) - p

def act0(y, a):
    return bern(a, Q(2, 3) if y[0] ^ y[1] else Q(1, 4))

def act1(y, a):
    return bern(a, Q(3, 5) if y[2] or y[3] else Q(1, 3))

def world(y, a, nxt):
    a0, a1 = a
    p = (Q(4, 5) if a0 and not a1 else Q(2, 7) if a1 and not a0
         else Q(3, 5) if y[3] else Q(1, 6))
    return bern(nxt, p)

def common(y, a, nxt, value):
    return bern(value, Q(5, 6) if a[0] ^ nxt else Q(1, 5))

def priv0(y, a, nxt, value):
    return bern(value, Q(3, 4) if a[1] ^ y[1] else Q(1, 4))

def priv1(y, a, nxt, value):
    return bern(value, Q(2, 3) if a[0] ^ a[1] ^ nxt else Q(1, 7))

def original(y):
    row = defaultdict(Q)
    for a in ACTIONS:
        action_mass = act0(y, a[0]) * act1(y, a[1])
        for nxt in BITS:
            world_mass = action_mass * world(y, a, nxt)
            for s0, s1, s2 in product(BITS, repeat=3):
                row[(s0, s1, s2, nxt)] += (
                    world_mass * common(y, a, nxt, s0) *
                    priv0(y, a, nxt, s1) * priv1(y, a, nxt, s2))
    return dict(row)

def binary(y, *, swapped_actions=False, missing_world=False, swapped_private=False):
    row = {}
    for s0, s1, s2, nxt in STATES:
        mass = Q(0)
        for a in ACTIONS:
            aworld = (a[1], a[0]) if swapped_actions else a
            mass += (act0(y, a[0]) * act1(y, a[1]) * world(y, aworld, nxt) *
                     common(y, a, False if missing_world else nxt, s0) *
                     priv0(y, a, nxt, s2 if swapped_private else s1) *
                     priv1(y, a, nxt, s1 if swapped_private else s2))
        row[(s0, s1, s2, nxt)] = mass
    return row

class ExactKernelFixture(unittest.TestCase):
    def test_all_256_transition_atoms_and_stochastic_rows(self):
        for y in STATES:
            a = original(y)
            self.assertEqual(a, binary(y))
            self.assertEqual(sum(a.values(), Q(0)), Q(1))
            self.assertEqual(len(a), 16)
            self.assertTrue(all(Q(0) < p < Q(1) for p in a.values()))

    def test_non_dirac_initial_law(self):
        nu = {STATES[0]: Q(1, 3), STATES[-1]: Q(2, 3)}
        for z in STATES:
            lhs = sum((w * original(y)[z] for y, w in nu.items()), Q(0))
            rhs = sum((w * binary(y)[z] for y, w in nu.items()), Q(0))
            self.assertEqual(lhs, rhs)

    def test_wrong_action_order_breaks_actual_world_row(self):
        self.assertTrue(any(original(y) != binary(y, swapped_actions=True) for y in STATES))

    def test_dropped_realized_next_world_breaks_common_update(self):
        self.assertTrue(any(original(y) != binary(y, missing_world=True) for y in STATES))

    def test_swapped_homogeneous_private_updates_are_semantically_wrong(self):
        self.assertTrue(any(original(y) != binary(y, swapped_private=True) for y in STATES))

    def test_hidden_joint_correlation_is_outside_product_subclass(self):
        y = STATES[0]
        joint = {a: act0(y, a[0]) * act1(y, a[1]) for a in ACTIONS}
        correlated = {(False, False): Q(1, 2), (True, True): Q(1, 2),
                      (False, True): Q(0), (True, False): Q(0)}
        self.assertNotEqual(joint, correlated)
        self.assertGreater(joint[(False, True)], Q(0))
        self.assertGreater(joint[(True, False)], Q(0))

if __name__ == "__main__":
    unittest.main()
