"""Independent exact countermodels for the new conditional closure boundaries."""
from fractions import Fraction as Q
import unittest


def quad(matrix, vector):
    return sum(vector[i] * matrix[i][j] * vector[j]
               for i in range(len(vector)) for j in range(len(vector)))


class ClosureBoundaryTests(unittest.TestCase):
    def test_seam_invisibility_can_have_rank_two(self):
        h = ((0, 1), (1, 2))
        self.assertTrue(all(h[i][j] - h[i][0] - h[0][j] + h[0][0] == 0
                            for i in range(2) for j in range(2)))
        self.assertEqual(h[0][0] * h[1][1] - h[0][1] * h[1][0], -1)

    def test_common_mode_is_not_identity_and_zero_sum_is_invisible(self):
        h = ((3, 3), (3, 3))
        self.assertEqual(quad(h, (1, -1)), 0)
        self.assertNotEqual(quad(((3, 0), (0, 3)), (1, -1)), 0)

    def test_singular_missing_preimage_produces_negative_vector(self):
        # H=0, b=1, c=7: the block form on (v,t)=(-4,1) is negative.
        self.assertEqual(2 * (-4) + 7, -1)
        self.assertFalse(any(0 * x == 1 for x in range(-20, 21)))

    def test_source_exceptional_branch_does_not_force_vanishing(self):
        gamma, source = Q(0), Q(1)
        self.assertEqual(gamma * source, 0)
        self.assertNotEqual(source, 0)

    def test_positive_component_can_mask_gram_negative_direction(self):
        a, p = ((1, 0), (0, -1)), ((0, 0), (0, 2))
        w = (0, 1)
        self.assertEqual(quad(a, w), -1)
        self.assertEqual(quad(p, w), 2)
        self.assertEqual(quad(a, w) + quad(p, w), 1)

    def test_nonempty_state_menus_can_have_empty_key_intersection(self):
        legal = ({0}, {1})
        self.assertTrue(all(legal))
        self.assertFalse(set.intersection(*legal))

    def test_discounted_budget_is_exact_limit_of_geometric_errors(self):
        beta, eta = Q(9, 10), Q(1, 7)
        closed = beta * eta / (1 - beta * (1 - eta))
        for horizon in (0, 1, 3, 15, 60):
            partial = sum((1 - beta) * beta**n * (1 - (1 - eta)**n)
                          for n in range(horizon))
            self.assertLessEqual(partial, closed)
            self.assertLessEqual(closed - partial, beta**horizon)

    def test_initial_law_error_does_not_disappear_at_zero_horizon(self):
        mu, nu = (Q(1), Q(0)), (Q(0), Q(1))
        self.assertEqual(max(abs(mu[i] - nu[i]) for i in range(2)), 1)

    def test_mediation_formula_uses_actual_positive_observational_cells(self):
        # Independent conditional noises, unequal covariate/assignment laws,
        # and a treatment-sensitive mediator and outcome.
        pc = (Q(1, 3), Q(2, 3))
        pt = ((Q(1, 4), Q(3, 4)), (Q(2, 5), Q(3, 5)))
        pu = ((Q(1, 3), Q(2, 3)), (Q(3, 7), Q(4, 7)))
        pv = ((Q(2, 7), Q(5, 7)), (Q(1, 6), Q(5, 6)))
        f = lambda t, c, u: (t + c + u) % 2
        g = lambda t, m, c, v: 2*t - 3*m + c + 5*v + t*m
        for t in range(2):
            for tp in range(2):
                direct, identified = Q(0), Q(0)
                for c in range(2):
                    direct += pc[c] * sum(pu[c][u] * pv[c][v] *
                        g(t, f(tp, c, u), c, v) for u in range(2) for v in range(2))
                    for m in range(2):
                        mass = sum(pc[c]*pt[c][t]*pu[c][u]*pv[c][v]
                            for u in range(2) for v in range(2) if f(t,c,u) == m)
                        numerator = sum(pc[c]*pt[c][t]*pu[c][u]*pv[c][v]*g(t,m,c,v)
                            for u in range(2) for v in range(2) if f(t,c,u) == m)
                        mediator = sum(pc[c]*pt[c][tp]*pu[c][u]*pv[c][v]
                            for u in range(2) for v in range(2) if f(tp,c,u) == m)
                        self.assertGreater(mass, 0)
                        identified += pc[c] * (numerator/mass) * (mediator/(pc[c]*pt[c][tp]))
                self.assertEqual(direct, identified)

    def test_observed_mediation_does_not_identify_joint_intervention(self):
        mediated = lambda t,m: m
        direct = lambda t,m: t
        observed_a = {(t,t,mediated(t,t)): Q(1,2) for t in range(2)}
        observed_b = {(t,t,direct(t,t)): Q(1,2) for t in range(2)}
        self.assertEqual(observed_a, observed_b)
        self.assertNotEqual(mediated(1,0), direct(1,0))
        self.assertNotIn((1,0,0), observed_a)  # missing positivity cell


if __name__ == '__main__':
    unittest.main()
