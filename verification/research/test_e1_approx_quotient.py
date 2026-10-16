"""Exact-Fraction adversaries for E1 (approximate type-respecting quotients).

Independent executable cross-checks of PermanssonResearch/Quotient/ApproxPrefix,
ApproxMargin and ApproxAdversaries. Finite chains only; these are NOT proofs of
the general measurable-space Lean theorems.
"""
from fractions import Fraction as F
from itertools import product
import unittest

ZERO, ONE, HALF = F(0), F(1), F(1, 2)


def check(K):
    for row in K.values():
        assert sum(row.values(), ZERO) == ONE and all(v >= 0 for v in row.values())
    return K


def prefix_law(K, y, T):
    """Exact law of (Y_0..Y_T) from Y_0 = y."""
    law = {(y,): ONE}
    for _ in range(T):
        nxt = {}
        for w, p in law.items():
            for z, q in K[w[-1]].items():
                nxt[w + (z,)] = nxt.get(w + (z,), ZERO) + p * q
        law = nxt
    return law


def push(law, f):
    out = {}
    for k, p in law.items():
        out[f(k)] = out.get(f(k), ZERO) + p
    return out


def tv(mu, nu):
    """Event-supremum TV on a finite space = sum of positive parts."""
    keys = set(mu) | set(nu)
    return sum((max(ZERO, mu.get(k, ZERO) - nu.get(k, ZERO)) for k in keys), ZERO)


def defect(K, Kbar, q):
    return max(tv(push(K[y], q), Kbar[q(y)]) for y in K)


def projected(K, q, y, T):
    return push(prefix_law(K, y, T), lambda w: tuple(q(z) for z in w))


def prefix_tv(K, Kbar, q, y, T):
    return tv(projected(K, q, y, T), prefix_law(Kbar, q(y), T))


# --- AQ2: non-Markov projection -------------------------------------------
QNM = {0: "a", 1: "b", 2: "b"}.__getitem__
KNM = check({0: {1: HALF, 2: HALF}, 1: {0: ONE}, 2: {2: ONE}})


def coarse_nm(p):
    return check({"a": {"b": ONE}, "b": {"a": p, "b": ONE - p}})


class NonMarkovProjectionTests(unittest.TestCase):

    def test_projection_is_not_markov(self):
        law = projected(KNM, QNM, 0, 2)
        law2 = projected(KNM, QNM, 2, 2)
        # P(q2=a | q0=a, q1=b) = 1/2 but P(q2=a | q0=b, q1=b) = 0
        self.assertEqual(law[("a", "b", "a")], HALF)
        self.assertEqual(law2.get(("b", "b", "a"), ZERO), ZERO)

    def test_linear_bound_holds_for_every_coarse_parameter(self):
        for p in [F(k, 8) for k in range(9)]:
            Kbar = coarse_nm(p)
            eta = defect(KNM, Kbar, QNM)
            for y in KNM:
                for T in range(0, 7):
                    with self.subTest(p=p, y=y, T=T):
                        self.assertLessEqual(prefix_tv(KNM, Kbar, QNM, y, T),
                                             min(ONE, T * eta))

    def test_defect_is_sup_over_all_fine_states(self):
        Kbar = coarse_nm(HALF)
        self.assertEqual(tv(push(KNM[0], QNM), Kbar["a"]), ZERO)
        self.assertEqual(defect(KNM, Kbar, QNM), HALF)

    def test_horizon_zero(self):
        for p in (ZERO, HALF, ONE):
            for y in KNM:
                self.assertEqual(prefix_tv(KNM, coarse_nm(p), QNM, y, 0), ZERO)


# --- AQ1: exact lumpability --------------------------------------------------
QL = {0: "a", 1: "a", 2: "b", 3: "b"}.__getitem__
KL = check({0: {0: F(1, 3), 1: F(1, 3), 2: F(1, 3)},
            1: {1: F(2, 3), 3: F(1, 3)},
            2: {0: F(1, 4), 2: F(3, 4)},
            3: {1: F(1, 4), 3: F(1, 2), 2: F(1, 4)}})
KLbar = check({"a": {"a": F(2, 3), "b": F(1, 3)}, "b": {"a": F(1, 4), "b": F(3, 4)}})


class ExactLumpabilityTests(unittest.TestCase):

    def test_zero_defect(self):
        self.assertEqual(defect(KL, KLbar, QL), ZERO)

    def test_zero_prefix_tv_every_horizon(self):
        for y in KL:
            for T in range(0, 6):
                self.assertEqual(prefix_tv(KL, KLbar, QL, y, T), ZERO)


# --- AQ3: leakage ------------------------------------------------------------
def leaky(eps):
    return check({0: {0: ONE - eps, 1: eps}, 1: {0: ONE - eps, 1: eps}})


KFIX = check({0: {0: ONE}, 1: {0: ONE}})


class LeakageTests(unittest.TestCase):

    def test_defect_equals_eps(self):
        for eps in (F(1, 100), F(1, 10), HALF, ONE):
            self.assertEqual(defect(KFIX, leaky(eps), lambda z: z), eps)

    def test_exact_prefix_tv_and_bounds(self):
        for eps in (F(1, 100), F(1, 10), HALF):
            for T in range(0, 8):
                d = prefix_tv(KFIX, leaky(eps), lambda z: z, 0, T)
                self.assertEqual(d, 1 - (1 - eps) ** T)
                self.assertLessEqual(d, min(ONE, T * eps))

    def test_invariance_not_transferred(self):
        eps = F(1, 1000)
        fine = prefix_law(KFIX, 0, 6)
        coarse = prefix_law(leaky(eps), 0, 6)
        stay_f = sum((p for w, p in fine.items() if set(w) == {0}), ZERO)
        stay_c = sum((p for w, p in coarse.items() if set(w) == {0}), ZERO)
        self.assertEqual(stay_f, ONE)
        self.assertEqual(stay_c, (1 - eps) ** 6)
        self.assertLess(stay_c, ONE)

    def test_geometric_bound_numeric_only(self):
        """E1.5 (geometric bound) is OPEN in Lean; here it is only observed
        numerically on finite examples, never asserted as proved."""
        for p in [F(k, 8) for k in range(9)]:
            Kbar = coarse_nm(p)
            eta = defect(KNM, Kbar, QNM)
            for T in range(0, 6):
                self.assertLessEqual(prefix_tv(KNM, Kbar, QNM, 0, T),
                                     1 - (1 - eta) ** T)


# --- V20.33-34: margins, factorization, labels --------------------------------
def final_in(target, T):
    """1-Lipschitz (event-TV) property of coarse T-prefix laws."""
    return lambda law: sum((p for w, p in law.items() if w[T] == target), ZERO)


def fine_effect(K0, KJ, q, prop, y, T):
    return abs(prop(projected(K0, q, y, T)) - prop(projected(KJ, q, y, T)))


def coarse_effect(K0b, KJb, prop, x, T):
    return abs(prop(prefix_law(K0b, x, T)) - prop(prefix_law(KJb, x, T)))


class MarginTests(unittest.TestCase):

    def setUp(self):
        self.K0, self.q = KNM, QNM
        self.KJ = check({0: {0: ONE}, 1: {2: ONE}, 2: {0: HALF, 2: HALF}})
        self.K0b = coarse_nm(F(1, 4))
        self.KJb = check({"a": {"a": ONE}, "b": {"a": F(1, 4), "b": F(3, 4)}})

    def test_margin_budget(self):
        eta0 = defect(self.K0, self.K0b, self.q)
        etaJ = defect(self.KJ, self.KJb, self.q)
        B1 = (0, 1, 2)
        for T in range(1, 6):
            prop = final_in("a", T)
            kappa = min(fine_effect(self.K0, self.KJ, self.q, prop, y, T) for y in B1)
            kbar = min(coarse_effect(self.K0b, self.KJb, prop, x, T)
                       for x in {self.q(y) for y in B1})
            budget = min(ONE, T * eta0) + min(ONE, T * etaJ)
            for y in B1:
                with self.subTest(T=T, y=y):
                    self.assertLessEqual(
                        abs(fine_effect(self.K0, self.KJ, self.q, prop, y, T)
                            - coarse_effect(self.K0b, self.KJb, prop, self.q(y), T)),
                        budget)
            self.assertLessEqual(abs(kappa - kbar), budget)

    def test_property_must_factor_through_quotient(self):
        """With EXACT lumpability (η=0) a property reading the hidden fine
        state (not q-measurable) still distinguishes models the quotient
        identifies: factorization is a hypothesis, not a consequence."""
        # same class-level rows as KL (lumps exactly to KLbar), different
        # within-class split from state 0: never visits hidden state 1 at t=1
        KJ = check({0: {0: F(2, 3), 2: F(1, 3)},
                    1: {1: F(2, 3), 3: F(1, 3)},
                    2: {0: F(1, 4), 2: F(3, 4)},
                    3: {1: F(1, 4), 3: F(1, 2), 2: F(1, 4)}})
        KJb = KLbar
        self.assertEqual(defect(KL, KLbar, QL), ZERO)
        self.assertEqual(defect(KJ, KJb, QL), ZERO)
        hidden = lambda law: sum((p for w, p in law.items() if w[1] == 1), ZERO)
        fine_hidden = abs(hidden(prefix_law(KL, 0, 1)) - hidden(prefix_law(KJ, 0, 1)))
        coarse = coarse_effect(KLbar, KJb, final_in("a", 1), "a", 1)
        self.assertEqual(coarse, ZERO)
        self.assertGreater(fine_hidden, ZERO)

    def test_label_matching_is_load_bearing(self):
        """Pairing a fine intervention with the WRONG coarse label: the budget
        computed from the correct label's defect does not cover the gap."""
        KJ_wrong = check({"a": {"a": ZERO, "b": ONE}, "b": {"a": ONE, "b": ZERO}})
        T = 2
        prop = final_in("a", T)
        eta0 = defect(KL, KLbar, QL)
        etaJ_correct = defect(KL, KLbar, QL)  # fine J := baseline, exact match
        budget = min(ONE, T * eta0) + min(ONE, T * etaJ_correct)
        self.assertEqual(budget, ZERO)
        fine = fine_effect(KL, KL, QL, prop, 0, T)
        mismatched = coarse_effect(KLbar, KJ_wrong, prop, "a", T)
        self.assertGreater(abs(fine - mismatched), budget)
        self.assertGreater(defect(KL, KJ_wrong, QL), ZERO)

    def test_positive_quotient_margin_not_exact_gr(self):
        """Positive coarse margin ABOVE the V20.34 budget (so the fine margin
        is positive too), while the coarse region {0} is not invariant:
        margin transfer is not an Exact-GR certificate.
        Identity quotient on {0,1}; baseline fine K0 = δ0 (fine {0} invariant),
        coarse K̄0 = leaky(ε); intervention fine KJ = coarse K̄J = δ1."""
        eps, T = F(1, 50), 3
        ident = lambda z: z
        K0, K0b = KFIX, leaky(eps)
        KJ = check({0: {1: ONE}, 1: {1: ONE}})
        KJb = KJ
        eta0, etaJ = defect(K0, K0b, ident), defect(KJ, KJb, ident)
        self.assertEqual((eta0, etaJ), (eps, ZERO))
        prop = lambda law: sum((p for w, p in law.items() if w[T] == 1), ZERO)
        B1 = (0,)
        fine_margin = min(abs(prop(prefix_law(K0, y, T)) - prop(prefix_law(KJ, y, T)))
                          for y in B1)
        coarse_margin = min(abs(prop(prefix_law(K0b, x, T)) - prop(prefix_law(KJb, x, T)))
                            for x in B1)
        budget = min(ONE, T * eta0) + min(ONE, T * etaJ)
        self.assertEqual(coarse_margin, 1 - eps)          # P̄_0(Y_T = 1) = ε
        self.assertGreater(coarse_margin, budget)         # transfer hypothesis
        self.assertLessEqual(abs(fine_margin - coarse_margin), budget)
        self.assertGreater(fine_margin, ZERO)             # transferred positivity
        self.assertGreater(K0b[0][1], ZERO)               # coarse {0} leaks
        self.assertEqual(K0[0].get(1, ZERO), ZERO)        # fine {0} invariant

if __name__ == "__main__":
    unittest.main()
