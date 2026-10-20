"""Independent exact native S=Fin3, X=A=Bool policy-class boundary tests.

This Python oracle is NOT a Lean/measure-theoretic certification of the
actual infinite path occupation law. The latter is a separate open P-06.2
obligation. This fixture computes finite recurrent classes and exact
stationary weights on the ORIGINAL shared alpha -> P -> U model.
"""
from fractions import Fraction as Q
from itertools import product
import unittest

PHASES = tuple(range(3))
WORLD = (False, True)
STATES = tuple(product(PHASES, WORLD))
START = (0, False)


def native_next(state, action):
    phase, world = state
    return ((phase + 1) % 3, bool(action))


def phase_aware(state):
    return state[0] != 2


def phase_blind(profile):
    return lambda state: profile[int(state[1])]


def exact_orbit_cycle(policy):
    seen = {}
    states = []
    state = START
    while state not in seen:
        seen[state] = len(states)
        states.append(state)
        state = native_next(state, policy(state))
    j = seen[state]
    return states[:j], states[j:]


def actual_score_of_cycle(cycle):
    true_mass = Q(sum(s[1] for s in cycle), len(cycle))
    return Q(1) - abs(true_mass - Q(2, 3))


def native_kernel_row(state, policy):
    nxt = native_next(state, policy(state))
    return {z: Q(int(z == nxt)) for z in STATES}


def randomized_kernel_row(state):
    return {z: (
        Q(2, 3) if z == ((state[0] + 1) % 3, True)
        else Q(1, 3) if z == ((state[0] + 1) % 3, False)
        else Q(0)) for z in STATES}


class NativePolicyBoundary(unittest.TestCase):
    def test_phase_aware_native_cycle_is_correct(self):
        transient, cycle = exact_orbit_cycle(phase_aware)
        self.assertEqual(transient, [])
        self.assertEqual(cycle, [(0, False), (1, True), (2, True)])
        self.assertEqual(actual_score_of_cycle(cycle), Q(1))
        self.assertEqual(sum(s[1] for s in cycle), 2)

    def test_all_36_native_atoms_for_each_deterministic_policy(self):
        for profile in product(WORLD, repeat=2):
            pi = phase_blind(profile)
            for y in STATES:
                row = native_kernel_row(y, pi)
                self.assertEqual(set(row), set(STATES))
                self.assertEqual(sum(row.values()), Q(1))
                self.assertEqual(sum(1 for v in row.values() if v == 1), 1)

    def test_all_four_phase_blind_actual_cycles(self):
        outcomes = {}
        for profile in product(WORLD, repeat=2):
            pre, cycle = exact_orbit_cycle(phase_blind(profile))
            outcomes[profile] = actual_score_of_cycle(cycle)
            self.assertGreaterEqual(len(cycle), 1)
            self.assertLessEqual(len(pre) + len(cycle), 6)
        self.assertEqual(outcomes, {
            (False, False): Q(1, 3),
            (False, True): Q(1, 3),
            (True, False): Q(5, 6),
            (True, True): Q(2, 3),
        })
        self.assertEqual(max(outcomes.values()), Q(5, 6))
        self.assertEqual(actual_score_of_cycle(exact_orbit_cycle(phase_aware)[1]), Q(1))

    def test_shared_world_and_update_primitives(self):
        # All policies differ only in action selection: the native world
        # state is the realized action and phase always advances by one.
        for y in STATES:
            for action in WORLD:
                expected = ((y[0] + 1) % 3, action)
                self.assertEqual(native_next(y, action), expected)
                self.assertEqual(native_next(y, action)[1], action)

    def test_randomized_stationary_policy_destroys_universal_claim(self):
        # The same model admits phase-blind iid Bernoulli(2/3) actions.
        # Finite exact verification of its stationary mass; almost-sure
        # convergence of its occupation is a separate probability theorem,
        # not certified by a finite-sample Python simulation.
        weights = { (p, x): Q(1, 3) * (Q(2, 3) if x else Q(1, 3))
                    for p, x in STATES}
        self.assertEqual(sum(weights.values()), Q(1))
        for z in STATES:
            pushed = sum((weights[y] * randomized_kernel_row(y)[z]
                          for y in STATES), Q(0))
            self.assertEqual(pushed, weights[z])
        true_mass = sum((p for (phase, x), p in weights.items() if x), Q(0))
        self.assertEqual(true_mass, Q(2, 3))
        self.assertEqual(Q(1) - abs(true_mass - Q(2, 3)), Q(1))

    def test_relabeling_strategic_phase_as_world_is_invalid(self):
        # The physical world has exactly two values; the joint state has six.
        # This mismatch cannot be a surjective physical-world map Bool -> Fin6.
        self.assertEqual(len(WORLD), 2)
        self.assertEqual(len(STATES), 6)
        self.assertNotEqual(len(WORLD), len(STATES))


if __name__ == "__main__":
    unittest.main()
