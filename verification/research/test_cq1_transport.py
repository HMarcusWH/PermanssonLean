"""CQ-1 Part 3 exact rational transport regressions.

These checks exercise finite stationary *joint-state transition kernels*, not
the Lean proof that two strategic decompositions share the same P. The P
condition is certified separately by StrategicApproximationPair in Lean.
"""
import unittest
from fractions import Fraction as Q
from test_cq1_finite import prefixes, survival, row_tv, envelope, expectation


# State index is 2*strategic_memory + world_bit. World false: states 0 and 2.
# The shared world map is: action true preserves the world bit;
# action false sets world=true. Strategic memory is always preserved.
IDENTITY = (
    (Q(1), Q(0), Q(0), Q(0)),
    (Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(0), Q(1), Q(0)),
    (Q(0), Q(0), Q(0), Q(1)),
)
LEAKY = (
    (Q(3, 4), Q(1, 4), Q(0), Q(0)),
    (Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(0), Q(3, 4), Q(1, 4)),
    (Q(0), Q(0), Q(0), Q(1)),
)
EXIT = (
    (Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(1), Q(0), Q(0)),
    (Q(0), Q(0), Q(0), Q(1)),
    (Q(0), Q(0), Q(0), Q(1)),
)
REGION = {0, 2}
COMPARISON = (0, 2)


def score(path):
    return Q(all(state in REGION for state in path))


def clamp_eta(eta, error):
    return min(Q(1), eta + error)


class CQ1TransportTests(unittest.TestCase):
    def test_genuine_nonzero_kernel_error(self):
        self.assertEqual(row_tv(IDENTITY, LEAKY), Q(1, 4))
        self.assertEqual(row_tv(EXIT, EXIT), 0)

    def test_survival_and_margin_transport_is_tight(self):
        eta, kappa = Q(0), Q(1)
        d0, dj = row_tv(IDENTITY, LEAKY), row_tv(EXIT, EXIT)
        L = 1
        eta_star = clamp_eta(eta, envelope(d0, L))
        kappa_star = kappa - envelope(d0, L) - envelope(dj, L)
        self.assertEqual(eta_star, Q(1, 4))
        self.assertEqual(kappa_star, Q(3, 4))
        for y in REGION:
            p_orig = survival(prefixes(IDENTITY, y, L), REGION)
            p_approx = survival(prefixes(LEAKY, y, L), REGION)
            self.assertEqual(p_orig, 1)
            self.assertEqual(p_approx, Q(3, 4))
            self.assertGreaterEqual(p_approx, 1 - eta_star)
        for y in COMPARISON:
            b = expectation(prefixes(LEAKY, y, L), score)
            j = expectation(prefixes(EXIT, y, L), score)
            self.assertEqual(abs(b - j), kappa_star)

    def test_zero_horizon_always_no_constitutive_effect(self):
        for y in COMPARISON:
            self.assertEqual(
                expectation(prefixes(IDENTITY, y, 0), score),
                expectation(prefixes(EXIT, y, 0), score),
            )

    def test_oversized_error_budget_is_clamped(self):
        self.assertEqual(clamp_eta(Q(1, 2), Q(3, 4)), 1)
        self.assertEqual(clamp_eta(Q(0), Q(1)), 1)
        self.assertEqual(clamp_eta(Q(0), Q(0)), 0)

    def test_positive_margin_requires_strict_error_headroom(self):
        self.assertEqual(Q(1) - Q(1, 4) - Q(3, 4), 0)
        self.assertFalse(Q(1, 4) + Q(3, 4) < Q(1))

    def test_fixed_world_transition_generator_contract(self):
        # This is a standalone structural witness, not a proof that arbitrary
        # matrices share P. The shared map is declared before policy variation.
        def world_transition(current_world, action):
            return current_world if action else 1
        self.assertEqual(world_transition(0, True), 0)
        self.assertEqual(world_transition(0, False), 1)
        for s in (0, 1):
            self.assertEqual(EXIT[2*s][2*s+1], 1)
            self.assertEqual(IDENTITY[2*s][2*s], 1)
            self.assertEqual(LEAKY[2*s][2*s], Q(3, 4))
            self.assertEqual(LEAKY[2*s][2*s+1], Q(1, 4))


if __name__ == "__main__":
    unittest.main()
