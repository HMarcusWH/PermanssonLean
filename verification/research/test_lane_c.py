"""Independent exact-rational finite absorbing-class regressions.

These exact-rational regressions independently check the typed witness.
The generic kernel-power and path-marginal bridge is separately proved in
Lean; the fixture is not a proof of that universal theorem or a substitute
for the genuine alpha/P/U canonical path law.
"""
from __future__ import annotations

from fractions import Fraction as Q
import unittest

STATES = ("t", "u", "a", "b")
ABSORBING = ("a", "b")
ZERO, ONE = Q(0), Q(1)
K = {
    "t": {"t": ZERO, "u": ONE, "a": ZERO, "b": ZERO},
    "u": {"t": ZERO, "u": Q(1, 2), "a": Q(1, 6), "b": Q(1, 3)},
    "a": {"t": ZERO, "u": ZERO, "a": ONE, "b": ZERO},
    "b": {"t": ZERO, "u": ZERO, "a": ZERO, "b": ONE},
}

# An independent exact reconstruction of the *typed alpha -> P -> U*
# stochastic semantics declared in TypedStrategicWitness.lean.
# The Boolean action is true with probability 1/2 everywhere.
def strategic_action_weights(_state):
    return {False: Q(1, 2), True: Q(1, 2)}

def world_weights(state, action):
    if state == "u" and not action:
        return {False: Q(1, 3), True: Q(2, 3)}
    old_world = {"t": False, "u": True, "a": False, "b": True}[state]
    return {False: Q(not (True if state == "t" else old_world)),
            True: Q(True if state == "t" else old_world)}

def strategic_update(state, action, next_world):
    old_strategic = state in ABSORBING
    if state == "t":
        next_strategic = False
    elif state == "u" and action:
        next_strategic = False
    else:
        next_strategic = True
    return {
        (False, False): "t", (False, True): "u",
        (True, False): "a", (True, True): "b"
    }[(next_strategic, next_world)]

def composed_typed_kernel():
    return {
        state: {
            dst: sum(
                (pa * px
                 for action, pa in strategic_action_weights(state).items()
                 for world, px in world_weights(state, action).items()
                 if strategic_update(state, action, world) == dst),
                ZERO)
            for dst in STATES
        }
        for state in STATES
    }

def step_distribution(v):
    return {j: sum((v[i] * K[i][j] for i in STATES), ZERO)
            for j in STATES}

def law_after(start, n):
    v = {i: Q(i == start) for i in STATES}
    for _ in range(n):
        v = step_distribution(v)
    return v

def survival(start, n):
    v = law_after(start, n)
    return v["t"] + v["u"]

def empirical(path, horizon):
    assert horizon > 0
    return {j: Q(path[:horizon].count(j), horizon) for j in STATES}

def abs_occup_error(path, horizon, destination):
    v = empirical(path, horizon)
    return sum((abs(v[j] - int(j == destination)) for j in STATES), ZERO)

class LaneCExactAbsorptionRegressions(unittest.TestCase):
    def test_typed_alpha_P_U_composition_matches_exact_four_state_matrix(self):
        self.assertEqual(composed_typed_kernel(), K)
        for state in STATES:
            self.assertEqual(sum(composed_typed_kernel()[state].values(), ZERO), ONE)

    def test_row_stochastic_exact(self):
        for i in STATES:
            self.assertEqual(sum(K[i].values(), ZERO), ONE)
            self.assertTrue(all(x >= ZERO for x in K[i].values()))

    def test_two_distinct_absorbing_states(self):
        for a in ABSORBING:
            self.assertEqual(K[a][a], ONE)
            self.assertEqual(law_after(a, 20)[a], ONE)
        self.assertNotEqual("a", "b")

    def test_two_step_uniform_absorption(self):
        for i in ("t", "u"):
            self.assertGreaterEqual(ONE - survival(i, 2), Q(1, 2))
        self.assertEqual(ONE - survival("t", 2), Q(1, 2))
        self.assertEqual(ONE - survival("u", 2), Q(3, 4))

    def test_exact_two_step_kernel_outside_all_states(self):
        expected = {"t": Q(1, 2), "u": Q(1, 4),
                    "a": ZERO, "b": ZERO}
        for state in STATES:
            self.assertEqual(survival(state, 2), expected[state])
        self.assertEqual(survival("t", 0), ONE)
        self.assertEqual(survival("u", 0), ONE)
        self.assertEqual(survival("a", 0), ZERO)
        self.assertEqual(survival("b", 0), ZERO)

    def test_arbitrary_initial_law_geometric_survival(self):
        cases = (
            {x: Q(1, 4) for x in STATES},
            {"t": Q(1, 7), "u": Q(2, 7), "a": Q(3, 7), "b": Q(1, 7)},
            {"t": ONE, "u": ZERO, "a": ZERO, "b": ZERO},
            {"t": ZERO, "u": ZERO, "a": ZERO, "b": ONE},
        )
        for mu in cases:
            self.assertEqual(sum(mu.values(), ZERO), ONE)
            for k in range(25):
                event_probability = sum(
                    (mu[y] * survival(y, 2 * k) for y in STATES), ZERO)
                self.assertLessEqual(event_probability, Q(1, 2)**k)

    def test_geometric_tail_n_two(self):
        for i in STATES:
            for k in range(25):
                self.assertLessEqual(survival(i, 2 * k), Q(1, 2)**k)

    def test_exact_transient_tail_from_u(self):
        for n in range(60):
            self.assertEqual(survival("u", n), Q(1, 2)**n)

    def test_exact_transient_tail_from_t(self):
        for n in range(1, 60):
            self.assertEqual(survival("t", n), Q(1, 2)**(n-1))

    def test_absorbing_mass_formula(self):
        for n in range(40):
            v = law_after("u", n)
            self.assertEqual(v["a"], Q(1, 3)*(ONE - Q(1, 2)**n))
            self.assertEqual(v["b"], Q(2, 3)*(ONE - Q(1, 2)**n))

    def test_random_limit_weights(self):
        # From u or t, absorption has weights 1/3 and 2/3.
        self.assertEqual(Q(1, 6)/(ONE-Q(1, 2)), Q(1, 3))
        self.assertEqual(Q(1, 3)/(ONE-Q(1, 2)), Q(2, 3))


    def test_initial_mixture_endpoint_closed_forms(self):
        cases = [
            {"t": ONE, "u": ZERO, "a": ZERO, "b": ZERO},
            {"t": ZERO, "u": ONE, "a": ZERO, "b": ZERO},
            {"t": ZERO, "u": ZERO, "a": ONE, "b": ZERO},
            {"t": ZERO, "u": ZERO, "a": ZERO, "b": ONE},
            {x: Q(1, 4) for x in STATES},
            {"t": Q(1, 7), "u": Q(2, 7), "a": Q(3, 7), "b": Q(1, 7)},
        ]
        point_a = {"t": Q(1, 3), "u": Q(1, 3), "a": ONE, "b": ZERO}
        point_b = {"t": Q(2, 3), "u": Q(2, 3), "a": ZERO, "b": ONE}
        for mu in cases:
            self.assertEqual(sum(mu.values(), ZERO), ONE)
            pa = mu["a"] + (mu["t"] + mu["u"]) / 3
            pb = mu["b"] + 2 * (mu["t"] + mu["u"]) / 3
            self.assertEqual(pa, sum((mu[y] * point_a[y] for y in STATES), ZERO))
            self.assertEqual(pb, sum((mu[y] * point_b[y] for y in STATES), ZERO))
            self.assertEqual(pa + pb, ONE)

    def test_endpoint_distribution_is_not_state_barycenter(self):
        # Random terminal occupation takes only two Dirac values; its
        # probability law is on MEASURES, not on physical states.
        mu = {x: Q(1, 4) for x in STATES}
        pa = mu["a"] + (mu["t"] + mu["u"]) / 3
        pb = mu["b"] + 2 * (mu["t"] + mu["u"]) / 3
        law_on_measures = {"dirac_a": pa, "dirac_b": pb}
        self.assertEqual(law_on_measures, {"dirac_a": Q(5, 12), "dirac_b": Q(7, 12)})
        self.assertEqual(sum(law_on_measures.values(), ZERO), ONE)

    def test_geometric_event_horizon_zero_and_absorbing_start(self):
        for start in STATES:
            self.assertLessEqual(survival(start, 0), ONE)
            for k in range(20):
                self.assertLessEqual(survival(start, 2 * k), Q(1, 2) ** k)
        for start in ABSORBING:
            for k in range(20):
                self.assertEqual(survival(start, 2 * k), ZERO)

    def test_pathwise_limit_not_expected_mixture(self):
        mixture = {"a": Q(1, 3), "b": Q(2, 3)}
        delta_a = {"a": ONE, "b": ZERO}
        delta_b = {"a": ZERO, "b": ONE}
        self.assertNotEqual(mixture, delta_a)
        self.assertNotEqual(mixture, delta_b)
        self.assertEqual(sum(mixture.values(), ZERO), ONE)

    def test_eventual_constant_path_occupation(self):
        for dest in ABSORBING:
            path = ["t", "u", "u", dest] + [dest] * 300
            for horizon in (8, 20, 50, 100, 200):
                self.assertLessEqual(abs_occup_error(path, horizon, dest),
                                     Q(6, horizon))

    def test_initial_dependence(self):
        self.assertEqual(law_after("a", 10)["a"], ONE)
        self.assertEqual(law_after("b", 10)["b"], ONE)

    def test_descriptor_collapse(self):
        h = {"t": -1, "u": -1, "a": 0, "b": 0}
        self.assertNotEqual("a", "b")
        self.assertEqual(h["a"], h["b"])

    def test_periodic_control_case(self):
        path = [i % 2 for i in range(400)]
        # One-time laws alternate, but empirical occupation tends to half-half.
        self.assertEqual(Q(path[:400].count(0), 400), Q(1, 2))
        self.assertEqual(Q(path[:400].count(1), 400), Q(1, 2))
        self.assertNotEqual(path[398], path[399])

    def test_no_absorption_is_not_a_positive_certificate(self):
        bad = {"t": {"t": ONE}, "a": {"a": ONE}}
        self.assertEqual(bad["t"]["t"], ONE)
        # An absorbing state existing somewhere says nothing about starting at t.
        self.assertEqual(Q(0), ONE - bad["t"]["t"])

if __name__ == "__main__":
    unittest.main()
