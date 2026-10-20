"""NEXT-06.1: independent exact native six-state alpha-P-U arithmetic.

This test checks finite transition rows and policy classes; it is NOT a
certificate of an infinite canonical occupation law.
"""
from fractions import Fraction as Q
import itertools
import unittest


STATES = tuple(itertools.product(range(3), (False, True)))
START = (0, False)


def next_state(state, choice):
    phase, _ = state
    return ((phase + 1) % 3, bool(choice))


def phase_aware(state):
    return state[0] != 2


def phase_blind(pair, state):
    return pair[int(state[1])]


def physical_world(_state, action):
    return bool(action)


def memory_update(state, _action, _next_world):
    return (state[0] + 1) % 3


def alpha_p_u(state, choice):
    action = bool(choice)
    return (memory_update(state, action, physical_world(state, action)),
            physical_world(state, action))


def row(state, choice):
    return {dest: Q(int(dest == next_state(state, choice)))
            for dest in STATES}


class NativePhaseModel(unittest.TestCase):
    def test_all_36_entries_for_five_controllers(self):
        controllers = [phase_aware]
        for pair in itertools.product((False, True), repeat=2):
            controllers.append(lambda y, pair=pair: phase_blind(pair, y))
        for ctrl in controllers:
            for state in STATES:
                actual = alpha_p_u(state, ctrl(state))
                exact = row(state, ctrl(state))
                self.assertEqual(sum(exact.values(), Q()), Q(1))
                for dest in STATES:
                    self.assertEqual(exact[dest], Q(int(dest == actual)))

    def test_exact_phase_aware_cycle(self):
        state = START
        observed = [state]
        for _ in range(30):
            state = alpha_p_u(state, phase_aware(state))
            observed.append(state)
        self.assertEqual(observed[:4],
                         [(0, False), (1, True), (2, True), (0, False)])
        self.assertEqual(observed[3:], observed[:-3])
        self.assertEqual(Q(sum(x for _, x in observed[1:31]), 30), Q(2, 3))

    def test_p_and_u_are_policy_independent(self):
        for state in STATES:
            for action in (False, True):
                for policy in itertools.product((False, True), repeat=2):
                    self.assertEqual(physical_world(state, action), action)
                    self.assertEqual(memory_update(state, action, True),
                                     memory_update(state, action, False))
                    self.assertEqual(next_state(state, action),
                                     alpha_p_u(state, action))

    def test_phase_policy_is_not_bool_feedback(self):
        for pair in itertools.product((False, True), repeat=2):
            self.assertNotEqual([phase_aware(y) for y in STATES],
                                [phase_blind(pair, y) for y in STATES])

    def test_mutated_phase_or_world_row_is_rejected(self):
        for state in STATES:
            original = row(state, phase_aware(state))
            wrong_dest = ((state[0] + 2) % 3, phase_aware(state))
            if wrong_dest != next_state(state, phase_aware(state)):
                self.assertNotEqual(original[wrong_dest], Q(1))
            wrong_world = not phase_aware(state)
            self.assertNotEqual(alpha_p_u(state, phase_aware(state))[1], wrong_world)


if __name__ == "__main__":
    unittest.main()
