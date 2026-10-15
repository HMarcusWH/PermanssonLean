"""Independent exact-Fraction C-Exit regression suite (22 destructive cases).

The matrix is a complete frozen stochastic kernel; this is independent arithmetic
rather than a substitute for the actual typed Lean α→P→U proof obligations.
We refuse outside-region starts for an *inside-B* first-exit certification.
"""
from __future__ import annotations

from fractions import Fraction as F
from collections import defaultdict
from itertools import product
import unittest

ZERO, ONE = F(0), F(1)

class Kernel:
    def __init__(self, states, rows):
        self.states = tuple(states)
        self.rows = {x: {z: F(v) for z,v in rows[x].items()} for x in states}
        assert set(self.rows) == set(self.states)
        for x in states:
            assert set(self.rows[x]).issubset(set(states))
            assert all(v >= 0 for v in self.rows[x].values())
            assert sum(self.rows[x].values(), ZERO) == ONE

    def step(self, law):
        out = defaultdict(F)
        for x, mass in law.items():
            for z, prob in self.rows[x].items():
                out[z] += mass * prob
        return dict(out)

F1 = Kernel(("b", "a", "c"), {
    "b": {"b": F(1,2), "a": F(1,3), "c": F(1,6)},
    "a": {"a": ONE},
    "c": {"c": ONE},
})
F2 = Kernel(("d", "b", "a"), {
    "d": {"d": F(1,2), "b": F(1,4), "a": F(1,4)},
    "b": {"b": ONE},
    "a": {"a": ONE},
})
F4 = Kernel(("b", "d", "a", "c"), {
    "b": {"b": ONE},
    "d": {"a": ONE},
    "a": {"c": ONE},
    "c": {"c": ONE},
})
BF1 = frozenset(("b",))
BF2 = frozenset(("d", "b"))
BF4 = frozenset(("d", "b"))


def require_supported(law, B):
    if sum((v for x,v in law.items() if x not in B), ZERO) != ZERO:
        raise ValueError("initial law is not supported on regime B")


def killed_step(K, B, law):
    out = defaultdict(F)
    for x, mass in law.items():
        for z, p in K.rows[x].items():
            if z in B:
                out[z] += mass*p
    return dict(out)


def exit_step(K, B, law, destination):
    return sum((mass*p for x,mass in law.items()
                for z,p in K.rows[x].items()
                if z not in B and z in destination), ZERO)


def route(K, B, initial, destination, L):
    require_supported(initial, B)
    law = dict(initial)
    result = ZERO
    for _ in range(L):
        result += exit_step(K, B, law, destination)
        law = killed_step(K, B, law)
    return result, sum(law.values(), ZERO)


def route_infinite_known(K, B, initial, dest):
    # This is a separate exact absorbing-equations check for THESE frozen
    # fixtures. Never substitute large-L Monte Carlo for infinite proof.
    require_supported(initial, B)
    if K is F1:
        return initial.get("b",ZERO) * (F(2,3) if "a" in dest else ZERO) + (
            initial.get("b",ZERO)*F(1,3) if "c" in dest else ZERO)
    if K is F2:
        return initial.get("d",ZERO) * (F(1,2) if "a" in dest else ZERO)
    if K is F4:
        return initial.get("d",ZERO) * (ONE if "a" in dest else ZERO)
    raise ValueError("unregistered analytic formula")


def survival_infinite_known(K, initial):
    if K is F1:
        return ZERO
    if K is F2:
        return initial.get("b",ZERO) + initial.get("d",ZERO)*F(1,2)
    if K is F4:
        return initial.get("b",ZERO)
    raise ValueError("unregistered analytic formula")


def path_first_exit_index(path, B):
    for t,x in enumerate(path):
        if x not in B:
            return t
    return None


def qsd_eigenvalue(K, B, mu):
    require_supported(mu, B)
    killed = killed_step(K, B, mu)
    candidates = {killed.get(x,ZERO)/v for x,v in mu.items() if v}
    if len(candidates)!=1:
        raise ValueError("QSD eigenmass not proportional to mu")
    theta=candidates.pop()
    if not ZERO<theta<=ONE:
        raise ValueError("theta outside 0<theta<=1")
    if any(killed.get(x,ZERO) != theta*mu.get(x,ZERO) for x in K.states):
        raise ValueError("eigenmeasure relation failed")
    return theta


def qsd_destination_formula(K, B, mu, dest):
    theta = qsd_eigenvalue(K,B,mu)
    if theta == ONE:
        raise ZeroDivisionError("theta=1: no QSD destination ratio")
    q = exit_step(K,B,mu,dest)
    return q/(ONE-theta)


class ExactExitRouting22(unittest.TestCase):
    def test_ER01_horizon_zero(self):
        self.assertEqual(route(F1,BF1,{"b":ONE},{"a"},0),(ZERO,ONE))

    def test_ER02_horizon_one(self):
        self.assertEqual(route(F1,BF1,{"b":ONE},{"a"},1),(F(1,3),F(1,2)))
        self.assertEqual(route(F1,BF1,{"b":ONE},{"c"},1)[0],F(1,6))

    def test_ER03_horizon_two(self):
        self.assertEqual(route(F1,BF1,{"b":ONE},{"a"},2),(F(1,2),F(1,4)))
        self.assertEqual(route(F1,BF1,{"b":ONE},{"c"},2)[0],F(1,4))

    def test_ER04_general_horizon_formula(self):
        for L in range(3,19):
            self.assertEqual(route(F1,BF1,{"b":ONE},{"a"},L)[0],
                             F(2,3)*(ONE-F(1,2)**L))

    def test_ER05_destination_overlaps_regime(self):
        for L in (0,1,2,7):
            self.assertEqual(route(F1,BF1,{"b":ONE},{"b","a"},L)[0],
                             route(F1,BF1,{"b":ONE},{"a"},L)[0])

    def test_ER06_inside_only_destination_is_zero(self):
        for L in range(9):
            self.assertEqual(route(F1,BF1,{"b":ONE},{"b"},L)[0],ZERO)

    def test_ER07_destination_additivity(self):
        for L in range(8):
            a=route(F1,BF1,{"b":ONE},{"a"},L)[0]
            c=route(F1,BF1,{"b":ONE},{"c"},L)[0]
            self.assertEqual(a+c,route(F1,BF1,{"b":ONE},{"a","c"},L)[0])

    def test_ER08_partial_destinations_leave_exit_mass(self):
        a=route(F1,BF1,{"b":ONE},{"a"},3)[0]
        full=route(F1,BF1,{"b":ONE},{"a","c"},3)[0]
        self.assertLess(a,full)

    def test_ER09_finite_mass_conservation(self):
        for K,B,law in ((F1,BF1,{"b":ONE}),(F2,BF2,{"d":ONE}),
                         (F4,BF4,{"d":ONE})):
            for L in range(9):
                escaped,survival=route(K,B,law,set(K.states)-set(B),L)
                self.assertEqual(escaped+survival,ONE)

    def test_ER10_exit_by_L_not_before_L(self):
        paths=[("b","a"),("b","b","a"),("b","b","b")]
        self.assertEqual([path_first_exit_index(p,BF1) for p in paths],[1,2,None])
        self.assertFalse(path_first_exit_index(paths[0],BF1)<1)
        self.assertTrue(path_first_exit_index(paths[0],BF1)<=1)

    def test_ER11_competing_infinite_destinations(self):
        self.assertEqual(route_infinite_known(F1,BF1,{"b":ONE},{"a"}),F(2,3))
        self.assertEqual(route_infinite_known(F1,BF1,{"b":ONE},{"c"}),F(1,3))

    def test_ER12_F1_never_exit_zero(self):
        self.assertEqual(survival_infinite_known(F1,{"b":ONE}),ZERO)

    def test_ER13_F2_positive_never_exit(self):
        self.assertEqual(survival_infinite_known(F2,{"d":ONE}),F(1,2))

    def test_ER14_F2_missing_mass_conservation(self):
        self.assertEqual(route_infinite_known(F2,BF2,{"d":ONE},{"a"})+
                         survival_infinite_known(F2,{"d":ONE}),ONE)

    def test_ER15_outside_start_gate(self):
        with self.assertRaises(ValueError):
            route(F1,BF1,{"a":ONE},{"a"},0)

    def test_ER16_never_exit_does_not_index_infinity(self):
        never_exit_path=("b",)*12
        self.assertIsNone(path_first_exit_index(never_exit_path,BF4))
        self.assertNotIn("infinity",never_exit_path)

    def test_ER17_proper_QSD_destination_fraction(self):
        self.assertEqual(qsd_eigenvalue(F1,BF1,{"b":ONE}),F(1,2))
        self.assertEqual(qsd_destination_formula(F1,BF1,{"b":ONE},{"a"}),F(2,3))

    def test_ER18_theta_one_excluded_from_fraction(self):
        self.assertEqual(qsd_eigenvalue(F2,BF2,{"b":ONE}),ONE)
        with self.assertRaises(ZeroDivisionError):
            qsd_destination_formula(F2,BF2,{"b":ONE},{"a"})
        self.assertEqual(exit_step(F2,BF2,{"b":ONE},{"a"}),ZERO)

    def test_ER19_theta_zero_invalid_QSD(self):
        with self.assertRaises(ValueError):
            qsd_eigenvalue(F4,BF4,{"d":ONE})

    def test_ER20_theta_one_does_not_imply_all_state_survival(self):
        self.assertEqual(qsd_eigenvalue(F4,BF4,{"b":ONE}),ONE)
        exited,survival=route(F4,BF4,{"d":ONE},{"a"},1)
        self.assertEqual((exited,survival),(ONE,ZERO))

    def test_ER21_arrival_to_noninvariant_destination(self):
        self.assertEqual(route(F4,BF4,{"d":ONE},{"a"},1)[0],ONE)
        self.assertEqual(F4.rows["a"].get("a",ZERO),ZERO)
        self.assertEqual(F4.rows["a"]["c"],ONE)

    def test_ER22_F2_nondirac_law_and_linear_mixture(self):
        mu={"d":F(1,3),"b":F(2,3)}
        for L in (0,1,2,4,9):
            r,s=route(F2,BF2,mu,{"a"},L)
            rd,sd=route(F2,BF2,{"d":ONE},{"a"},L)
            rb,sb=route(F2,BF2,{"b":ONE},{"a"},L)
            self.assertEqual(r,F(1,6)*(ONE-F(1,2)**L))
            self.assertEqual(r,F(1,3)*rd+F(2,3)*rb)
            self.assertEqual(s,F(1,3)*sd+F(2,3)*sb)
        self.assertEqual(route_infinite_known(F2,BF2,mu,{"a"}),F(1,6))
        self.assertEqual(survival_infinite_known(F2,mu),F(5,6))


if __name__ == "__main__":
    unittest.main()
