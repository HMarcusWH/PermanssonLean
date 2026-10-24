"""Exact Q-05 candidate arithmetic for nonidentity strategic-state compression.

Independent finite rational implementation of the proposed witness targets in
the repository-anchored v2 build plan. This is NOT a Lean source theorem, an
original ConstitutiveComparisonSet certificate, or an Exact GR/PR claim.

Typed transition order: action-selection alpha -> physical world P (x' := a)
-> strategic update U (baseline s' := False, treatment s' := True).
The coarse system uses Unit strategic state and the SAME physical P.
"""
from __future__ import annotations

from fractions import Fraction as F
import unittest

BETA = F(1, 3)
SIDES = ("baseline", "treatment")
FINE_TRUE = {
    "baseline": {False: F(1, 10), True: F(1, 5)},
    "treatment": {False: F(7, 10), True: F(4, 5)},
}
COARSE_TRUE = {"baseline": F(3, 20), "treatment": F(3, 4)}
COMPARISON = ((False, False), (False, True))
ALL_FINE = tuple((s, x) for s in (False, True) for x in (False, True))
ALL_COARSE = (False, True)
ETA = F(1, 20)


def compression(y):
    """A genuinely non-injective type-respecting state compression."""
    strategic_state, world = y
    assert isinstance(strategic_state, bool) and isinstance(world, bool)
    return (None, world)


def physical_world_next(action):
    """Both fine/coarse models and both sides share the SAME physical kernel."""
    assert isinstance(action, bool)
    return action


def next_strategic_state(side):
    return side == "treatment"


def fine_transition(side, y):
    s, x = y
    assert side in SIDES and y in ALL_FINE
    p = FINE_TRUE[side][s]
    next_s = next_strategic_state(side)
    # The update uses the actual realized physical transition, not old x.
    return {
        (next_s, physical_world_next(False)): 1 - p,
        (next_s, physical_world_next(True)): p,
    }


def coarse_transition(side, x):
    assert side in SIDES and x in ALL_COARSE
    p = COARSE_TRUE[side]
    return {physical_world_next(False): 1 - p,
            physical_world_next(True): p}


def fraction_linear_solve(A, b):
    """Independent exact Gaussian elimination, no model-specific shortcuts."""
    n = len(b)
    rows = [[F(v) for v in A[i]] + [F(b[i])] for i in range(n)]
    for col in range(n):
        pivot = next((i for i in range(col, n) if rows[i][col]), None)
        if pivot is None:
            raise ValueError("singular finite discounted resolvent")
        rows[col], rows[pivot] = rows[pivot], rows[col]
        q = rows[col][col]
        rows[col] = [v / q for v in rows[col]]
        for j in range(n):
            if j == col:
                continue
            coeff = rows[j][col]
            rows[j] = [u - coeff * v for u, v in zip(rows[j], rows[col])]
    return [r[-1] for r in rows]


def discounted_values(side, fine):
    """Evaluate (1-beta) sum beta^t 1{x_t=True} on the canonical chain."""
    states = ALL_FINE if fine else ALL_COARSE
    step = fine_transition if fine else coarse_transition
    matrix = []
    b = []
    for y in states:
        dist = step(side, y)
        assert sum(dist.values(), F(0)) == 1
        matrix.append([F(int(y == nxt))
                       - BETA * dist.get(nxt, F(0))
                       for nxt in states])
        world = y[1] if fine else y
        b.append((1 - BETA) * int(world))
    ans = fraction_linear_solve(matrix, b)
    return dict(zip(states, ans))


def projected_overlap(side, s):
    p = FINE_TRUE[side][s]
    q = COARSE_TRUE[side]
    return min(p, q) + min(1 - p, 1 - q)


def margin(values0, valuesJ, states):
    return min(abs(valuesJ[y] - values0[y]) for y in states)


def common_mass_discounted_budget(beta=BETA, eta=ETA):
    """(1-beta)*sum beta^n [1-(1-eta)^n], exactly."""
    assert 0 <= beta < 1 and 0 <= eta <= 1
    return beta * eta / (1 - beta + beta * eta)


class ProposedNonidentitySourceFixture(unittest.TestCase):
    def test_type_respecting_q_nonidentity_and_original_two_starts(self):
        self.assertEqual(len(COMPARISON), 2)
        self.assertNotEqual(COMPARISON[0], COMPARISON[1])
        self.assertEqual(compression(COMPARISON[0]), (None, False))
        self.assertEqual(compression(COMPARISON[1]), (None, True))
        self.assertEqual(compression((False, True)), compression((True, True)))
        self.assertNotEqual((False, True), (True, True))

    def test_shared_physical_world_and_side_specific_update(self):
        for side in SIDES:
            for y in ALL_FINE:
                fine = fine_transition(side, y)
                self.assertEqual(sum(fine.values(), F(0)), 1)
                self.assertEqual({s for s, _ in fine}, {side == "treatment"})
                self.assertEqual({x for _, x in fine}, {False, True})
                self.assertTrue(all(0 <= prob <= 1 for prob in fine.values()))
            for x in ALL_COARSE:
                self.assertEqual(sum(coarse_transition(side, x).values(), F(0)), 1)
        self.assertFalse(next_strategic_state("baseline"))
        self.assertTrue(next_strategic_state("treatment"))

    def test_exact_canonical_discounted_values_for_both_original_starts(self):
        baseline = discounted_values("baseline", True)
        treated = discounted_values("treatment", True)
        coarse0 = discounted_values("baseline", False)
        coarseJ = discounted_values("treatment", False)
        expected = {
            False: (F(1, 30), F(11, 45), F(1, 20), F(1, 4)),
            True: (F(7, 10), F(41, 45), F(43, 60), F(11, 12)),
        }
        for x, values in expected.items():
            with self.subTest(world=x):
                self.assertEqual((baseline[False, x], treated[False, x],
                                  coarse0[x], coarseJ[x]), values)
        self.assertEqual(margin(baseline, treated, COMPARISON), F(19, 90))
        self.assertEqual(margin(coarse0, coarseJ, ALL_COARSE), F(1, 5))
        self.assertEqual(abs(F(19, 90)-F(1, 5)), F(1, 90))

    def test_actual_baseline_treatment_error_budgets_and_strict_margin(self):
        b0 = discounted_values("baseline", True)
        bJ = discounted_values("treatment", True)
        c0 = discounted_values("baseline", False)
        cJ = discounted_values("treatment", False)
        self.assertEqual({abs(b0[False, x]-c0[x]) for x in ALL_COARSE},
                         {F(1, 60)})
        self.assertEqual({abs(bJ[False, x]-cJ[x]) for x in ALL_COARSE},
                         {F(1, 180)})
        self.assertEqual(common_mass_discounted_budget(), F(1, 41))
        self.assertLessEqual(F(1, 90), F(2, 41))
        self.assertGreater(F(19, 90) - F(2, 41), 0)
        for side in SIDES:
            for s in (False, True):
                self.assertEqual(projected_overlap(side, s), F(19, 20))

    def test_baseline_only_witness_misses_treatment_reachable_state(self):
        from_starts_baseline = {
            next_s for start in COMPARISON
            for next_s, _ in fine_transition("baseline", start)
        }
        from_starts_treated = {
            next_s for start in COMPARISON
            for next_s, _ in fine_transition("treatment", start)
        }
        self.assertEqual(from_starts_baseline, {False})
        self.assertEqual(from_starts_treated, {True})
        self.assertNotEqual(from_starts_baseline, from_starts_treated)
        # A normalized but changed treated row violates the stated eta budget.
        altered_treated_p = F(19, 20)
        self.assertEqual(altered_treated_p + (1-altered_treated_p), 1)
        self.assertGreater(abs(altered_treated_p - COARSE_TRUE["treatment"]),
                           ETA)


if __name__ == "__main__":
    unittest.main()
