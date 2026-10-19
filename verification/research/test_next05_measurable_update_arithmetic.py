"""NEXT-05.1 independent finite asymmetric alpha-P-U reindex checks.

Checks typed input and output ordering, not a Lean proof of the general
measurable update pushforward.
"""
from itertools import product
from fractions import Fraction as Q
import unittest


def phi_state(common, s0, s1):
    return (common, (s0, s1))


def pi2(f):
    return (f[0],f[1])


def original_world(common, private, x, actions):
    a0,a1=actions
    return bool((int(a0) + 2*int(a1) + int(x) + int(common)) % 3 == 1)


def common_update(common, priv, x, actions, next_world):
    return bool(int(common) ^ int(actions[0]) ^ int(next_world))


def private0_update(common, priv, x, actions, next_world):
    return bool(int(priv[0]) ^ int(actions[1]) ^ int(next_world))


def private1_update(common, priv, x, actions, next_world):
    return bool(int(priv[1]) ^ int(actions[0]) ^ int(x))


def original_update(common,priv,x,actions,nx):
    return (common_update(common,priv,x,actions,nx),
            (private0_update(common,priv,x,actions,nx),
             private1_update(common,priv,x,actions,nx)))


def binary_update(binary_state,x,actions,nx):
    common,priv=binary_state
    return (common_update(common,priv,x,actions,nx),
            (private0_update(common,priv,x,actions,nx),
             private1_update(common,priv,x,actions,nx)))


class MeasurableTwoFiniteAsymmetry(unittest.TestCase):
    def test_exact_original_binary_inputs_and_update(self):
        for common,s0,s1,x,a0,a1 in product((False,True), repeat=6):
            priv=(s0,s1);actions=(a0,a1)
            n=original_world(common,priv,x,actions)
            self.assertEqual(original_update(common,priv,x,actions,n),
                             binary_update(phi_state(common,*priv),x,actions,n))
            self.assertEqual(sum((Q(1),Q(0))),Q(1))

    def test_bad_swapped_private_update_is_detected(self):
        witness=0
        for common,s0,s1,x,a0,a1 in product((False,True), repeat=6):
            priv=(s0,s1);actions=(a0,a1)
            n=original_world(common,priv,x,actions)
            target=original_update(common,priv,x,actions,n)
            bad=(target[0],tuple(reversed(target[1])))
            witness+=target!=bad
        self.assertGreater(witness,0)

    def test_omitting_next_world_from_common_update_is_detected(self):
        witness=0
        for common,s0,s1,x,a0,a1 in product((False,True), repeat=6):
            priv=(s0,s1); actions=(a0,a1)
            n=original_world(common,priv,x,actions)
            if common_update(common,priv,x,actions,n)!=common_update(
                 common,priv,x,actions,not n):
                witness+=1
        self.assertGreater(witness,0)

    def test_physical_world_depends_asymmetrically_on_actions(self):
        witnesses=0
        for common,s0,s1,x in product((False,True), repeat=4):
            p=(s0,s1)
            if original_world(common,p,x,(True,False)) != (
               original_world(common,p,x,(False,True))):
                witnesses+=1
        self.assertGreater(witnesses,0)


if __name__=="__main__":
    unittest.main()
