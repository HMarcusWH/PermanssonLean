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


def mixed_prefix_law(K, mu, T):
    """Exact prefix law from an initial LAW `mu` (dict state -> mass)."""
    out = {}
    for y, m in mu.items():
        for w, p in prefix_law(K, y, T).items():
            out[w] = out.get(w, ZERO) + m * p
    return out


def conditional(law, hist, nxt):
    """P(W_n = nxt | W_0..W_{n-1} = hist) under a joint law of tuples."""
    n = len(hist)
    den = sum((p for w, p in law.items() if w[:n] == hist), ZERO)
    num = sum((p for w, p in law.items() if w[:n] == hist and w[n] == nxt), ZERO)
    return num / den


def projected(K, q, y, T):
    return push(prefix_law(K, y, T), lambda w: tuple(q(z) for z in w))


def prefix_tv(K, Kbar, q, y, T):
    return tv(projected(K, q, y, T), prefix_law(Kbar, q(y), T))


# --- AQ2: non-Markov projection -------------------------------------------
QNM = {0: "a", 1: "b", 2: "b"}.__getitem__
KNM = check({0: {1: HALF, 2: HALF}, 1: {0: ONE}, 2: {2: ONE}})


def coarse_nm(p):
    return check({"a": {"b": ONE}, "b": {"a": p, "b": ONE - p}})


def near_lumpable(d):
    """Fibre b = {1, 2} split asymmetrically by `d`: defect exactly `d`
    against KNLBAR, projection history dependent for d > 0."""
    return check({0: {1: HALF, 2: HALF},
                  1: {0: HALF + d, 1: HALF - d},
                  2: {0: HALF - d, 2: HALF + d}})


KNLBAR = check({"a": {"b": ONE}, "b": {"a": HALF, "b": HALF}})


class NonMarkovProjectionTests(unittest.TestCase):

    def test_projection_is_not_markov_from_one_start(self):
        """Same fine start 0, same current coarse value b, different coarse
        histories give different next-step laws (conditionals computed as
        ratios of the projected joint law)."""
        law = projected(KNM, QNM, 0, 4)
        self.assertEqual(conditional(law, ("a", "b", "a", "b"), "a"), HALF)
        self.assertEqual(conditional(law, ("a", "b", "b", "b"), "a"), ZERO)
        law = projected(near_lumpable(F(1, 10)), QNM, 0, 3)
        self.assertEqual(conditional(law, ("a", "b"), "a"), HALF)
        self.assertEqual(conditional(law, ("a", "b", "b"), "a"), F(12, 25))

    def test_linear_bound_nonvacuous(self):
        """V20.31 on a non-Markov projection with the bound BELOW 1 at every
        checked horizon (vacuous horizons are rejected), and the TV positive."""
        for d in (F(1, 20), F(1, 10), F(1, 8)):
            K = near_lumpable(d)
            eta = defect(K, KNLBAR, QNM)
            self.assertEqual(eta, d)
            positive = False
            for y in K:
                for T in range(0, 8):
                    with self.subTest(d=d, y=y, T=T):
                        self.assertLess(T * eta, ONE)
                        tv_T = prefix_tv(K, KNLBAR, QNM, y, T)
                        self.assertLessEqual(tv_T, T * eta)
                        positive = positive or tv_T > 0
            self.assertTrue(positive)
        self.assertEqual(prefix_tv(near_lumpable(F(1, 10)), KNLBAR, QNM, 2, 2),
                         F(11, 100))

    def test_capped_bound_degenerate_family(self):
        """The cap `min(1, T η)` on the fully non-lumpable KNM family
        (η = max(p, 1-p) ≥ 1/2): only a sanity check, not evidence."""
        for p in [F(k, 8) for k in range(9)]:
            Kbar = coarse_nm(p)
            eta = defect(KNM, Kbar, QNM)
            for y in KNM:
                for T in range(0, 7):
                    self.assertLessEqual(prefix_tv(KNM, Kbar, QNM, y, T),
                                         min(ONE, T * eta))

    def test_defect_is_sup_over_all_fine_states(self):
        """State 3 (class b) is unreachable from 0 but carries the largest
        one-step TV; the defect is that state's TV, strictly above the sup
        over reachable states, a class representative, and a fibre mean."""
        K = dict(near_lumpable(F(1, 10)))
        K[3] = {0: ONE}
        K = check(K)
        q = {0: "a", 1: "b", 2: "b", 3: "b"}.__getitem__
        row_tv = {y: tv(push(K[y], q), KNLBAR[q(y)]) for y in K}
        self.assertEqual(row_tv, {0: ZERO, 1: F(1, 10), 2: F(1, 10), 3: HALF})
        reachable = {z for w in prefix_law(K, 0, 6) for z in w}
        self.assertNotIn(3, reachable)
        self.assertEqual(defect(K, KNLBAR, q), HALF)
        self.assertGreater(defect(K, KNLBAR, q), max(row_tv[y] for y in reachable))
        self.assertGreater(defect(K, KNLBAR, q), row_tv[1])                 # representative
        self.assertGreater(defect(K, KNLBAR, q), (row_tv[1] + row_tv[2] + row_tv[3]) / 3)

    def test_horizon_zero(self):
        for p in (ZERO, HALF, ONE):
            for y in KNM:
                self.assertEqual(prefix_tv(KNM, coarse_nm(p), QNM, y, 0), ZERO)

    def test_initial_law_lift_is_needed(self):
        """η = 0 (exact lumpability) but the coarse start is not the image of
        the fine initial law: the prefix bound `T η` already fails at T = 0."""
        mu = {0: HALF, 2: HALF}                  # q_# mu = (a + b) / 2
        fine = push(mixed_prefix_law(KL, mu, 0), lambda w: tuple(QL(z) for z in w))
        coarse = prefix_law(KLbar, "a", 0)
        self.assertEqual(defect(KL, KLbar, QL), ZERO)
        self.assertEqual(tv(fine, coarse), HALF)
        self.assertEqual(tv(projected(KL, QL, 0, 3), prefix_law(KLbar, "b", 3)), ONE)


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
        for eps in (F(1, 100), F(1, 10), HALF, ONE):
            for T in range(0, 8):
                d = prefix_tv(KFIX, leaky(eps), lambda z: z, 0, T)
                self.assertEqual(d, 1 - (1 - eps) ** T)
                self.assertLessEqual(d, min(ONE, T * eps))
                if eps == ONE and T >= 1:
                    self.assertEqual(d, ONE)             # cap attained

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
        for d in (F(1, 20), F(1, 10), F(1, 8)):
            K = near_lumpable(d)
            eta = defect(K, KNLBAR, QNM)
            for y in K:
                for T in range(0, 8):
                    self.assertLess(1 - (1 - eta) ** T, ONE)
                    self.assertLessEqual(prefix_tv(K, KNLBAR, QNM, y, T),
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

    def test_margin_budget_nonvacuous(self):
        """V20.33 pointwise and V20.34 margin bounds with two POSITIVE defects
        and the budget strictly below 1 (vacuous horizons rejected)."""
        K0, K0b = near_lumpable(F(1, 10)), KNLBAR
        KJ = check({0: {0: ONE}, 1: {0: F(3, 5), 1: F(2, 5)},
                    2: {0: F(2, 5), 2: F(3, 5)}})
        KJb = check({"a": {"a": ONE}, "b": {"a": HALF, "b": HALF}})
        eta0, etaJ = defect(K0, K0b, QNM), defect(KJ, KJb, QNM)
        self.assertEqual((eta0, etaJ), (F(1, 10), F(1, 10)))
        B1 = (0, 1, 2)
        gaps = []
        for T in range(1, 5):
            prop = final_in("b", T)
            budget = min(ONE, T * eta0) + min(ONE, T * etaJ)
            self.assertLess(budget, ONE)
            fine = {y: fine_effect(K0, KJ, QNM, prop, y, T) for y in B1}
            coarse = {y: coarse_effect(K0b, KJb, prop, QNM(y), T) for y in B1}
            for y in B1:
                with self.subTest(T=T, y=y):
                    self.assertLessEqual(abs(fine[y] - coarse[y]), budget)
            gap = abs(min(fine.values()) - min(coarse.values()))
            self.assertLessEqual(gap, budget)
            gaps.append(gap)
        self.assertEqual(gaps[2], F(3, 50))      # T = 3: positive gap, budget 3/5

    def test_baseline_only_certificate_insufficient(self):
        """Exactly lumpable baseline (η₀ = 0) but a non-lumpable matched
        intervention (η_J = 1/10): the margin gap exceeds the baseline-only
        budget `min(1, T η₀) = 0` and is covered only by the full budget."""
        d = F(1, 10)
        KJ = check({0: {0: F(1, 3), 1: F(1, 3), 2: F(1, 3)},
                    1: {1: F(2, 3) - d, 3: F(1, 3) + d},
                    2: {0: F(1, 4), 2: F(3, 4)},
                    3: {1: F(1, 4), 3: F(1, 2), 2: F(1, 4)}})
        KJb = KLbar
        eta0, etaJ = defect(KL, KLbar, QL), defect(KJ, KJb, QL)
        self.assertEqual((eta0, etaJ), (ZERO, d))
        T = 3
        prop = final_in("a", T)
        kappa = min(fine_effect(KL, KJ, QL, prop, y, T) for y in KL)
        kbar = min(coarse_effect(KLbar, KJb, prop, x, T) for x in {QL(y) for y in KL})
        self.assertEqual((kappa, kbar), (F(1, 120), ZERO))
        self.assertGreater(abs(kappa - kbar), min(ONE, T * eta0))
        self.assertLessEqual(abs(kappa - kbar), min(ONE, T * eta0) + min(ONE, T * etaJ))

    def test_exact_lumpability_equal_margins(self):
        """η₀ = η_J = 0 with a different coarse intervention kernel: fine and
        coarse effects coincide state by state (approxQuotient_margin_eq_of_exact)."""
        KJ = check({0: {0: F(1, 8), 1: F(1, 8), 2: F(3, 4)},
                    1: {1: F(1, 4), 3: F(3, 4)},
                    2: {0: HALF, 3: HALF},
                    3: {1: HALF, 2: HALF}})
        KJb = check({"a": {"a": F(1, 4), "b": F(3, 4)}, "b": {"a": HALF, "b": HALF}})
        self.assertEqual((defect(KL, KLbar, QL), defect(KJ, KJb, QL)), (ZERO, ZERO))
        for T in range(1, 5):
            prop = final_in("a", T)
            fine = [fine_effect(KL, KJ, QL, prop, y, T) for y in KL]
            coarse = [coarse_effect(KLbar, KJb, prop, QL(y), T) for y in KL]
            self.assertEqual(fine, coarse)
            self.assertGreater(min(fine), ZERO)

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
        """Positive margins ABOVE the V20.34 budget transfer in both directions
        while the coarse region is not invariant: margin transfer is not an
        Exact-GR certificate.  Identity quotient on {0, 1, 2}; region R = {0, 1};
        B₁ = {0, 1} is admissible (inside R, two DISTINCT path laws in each
        model).  Fine K0 fixes 0 and 1 (R invariant); coarse K̄0 leaks from R
        to the absorbing state 2 with probability ε; the intervention sends
        every state to 2 in both models (η_J = 0)."""
        eps, T = F(1, 50), 3
        ident = lambda z: z
        K0 = check({0: {0: ONE}, 1: {1: ONE}, 2: {2: ONE}})
        K0b = check({0: {0: ONE - eps, 2: eps}, 1: {1: ONE - eps, 2: eps}, 2: {2: ONE}})
        KJ = KJb = check({0: {2: ONE}, 1: {2: ONE}, 2: {2: ONE}})
        R, B1 = {0, 1}, (0, 1)
        eta0, etaJ = defect(K0, K0b, ident), defect(KJ, KJb, ident)
        self.assertEqual((eta0, etaJ), (eps, ZERO))
        # admissibility of B1 in both models: inside R, distinct path laws
        self.assertTrue(set(B1) <= R)
        for K in (K0, K0b):
            self.assertNotEqual(prefix_law(K, 0, T), prefix_law(K, 1, T))
        prop = lambda law: sum((p for w, p in law.items() if w[T] == 2), ZERO)
        fine_margin = min(abs(prop(prefix_law(K0, y, T)) - prop(prefix_law(KJ, y, T)))
                          for y in B1)
        coarse_margin = min(abs(prop(prefix_law(K0b, x, T)) - prop(prefix_law(KJb, x, T)))
                            for x in B1)
        budget = min(ONE, T * eta0) + min(ONE, T * etaJ)
        self.assertEqual((fine_margin, coarse_margin), (ONE, (1 - eps) ** T))
        self.assertLessEqual(abs(fine_margin - coarse_margin), budget)
        # fine region R invariant, coarse region R leaks
        self.assertTrue(all(sum(K0[y].get(z, ZERO) for z in R) == ONE for y in R))
        self.assertTrue(all(sum(K0b[y].get(z, ZERO) for z in R) < ONE for y in R))
        # coarse -> fine: hypothesis on the leaking side, positivity transferred
        self.assertGreater(coarse_margin, budget)
        self.assertGreater(fine_margin, ZERO)
        # fine -> coarse: the RECEIVING side is the leaking (non-invariant) one
        self.assertGreater(fine_margin, budget)
        self.assertGreater(coarse_margin, ZERO)

    def test_unsaturated_region_does_not_descend(self):
        """η = 0, yet the fine region B = {0} is not a union of fibres (fibre
        a = {0, 1}): the one-step hit probability of B differs between two
        fine starts with the SAME projected path law, so the descriptor
        1{y ∈ B} is not a function of the coarse law (B = q⁻¹B̄ is a separate
        obligation, not formalized in E1)."""
        self.assertEqual(defect(KL, KLbar, QL), ZERO)
        self.assertEqual(projected(KL, QL, 0, 4), projected(KL, QL, 1, 4))
        hit = lambda y: sum((p for w, p in prefix_law(KL, y, 1).items() if w[1] == 0), ZERO)
        self.assertEqual((hit(0), hit(1)), (F(1, 3), ZERO))


# --- typing: untyped quotient with zero defect -----------------------------------
def is_type_respecting(q, S, X):
    """q on S × X is type respecting iff its partition is a product of a
    partition of S and a partition of X (q ≅ q_S × q_X)."""
    def partitions(xs):
        if not xs:
            yield []
            return
        head, *rest = xs
        for p in partitions(rest):
            for i in range(len(p)):
                yield p[:i] + [[head] + p[i]] + p[i + 1:]
            yield [[head]] + p
    def label(part):
        return {z: i for i, blk in enumerate(part) for z in blk}
    target = {(s, x): {(s2, x2) for s2 in S for x2 in X if q((s2, x2)) == q((s, x))}
              for s in S for x in X}
    for pS in partitions(list(S)):
        for pX in partitions(list(X)):
            lS, lX = label(pS), label(pX)
            cand = {(s, x): {(s2, x2) for s2 in S for x2 in X
                             if lS[s2] == lS[s] and lX[x2] == lX[x]}
                    for s in S for x in X}
            if cand == target:
                return True
    return False


class TypingTests(unittest.TestCase):

    def test_untyped_quotient_rejected(self):
        """Parity quotient q(s, x) = s XOR x lumps the kernel EXACTLY (η = 0)
        but is not of the form q_S × q_X: ApproxKernelIntertwines /
        TypeRespectingStateCompression rejects it, so the margin theorems do
        not apply although the generic defect is zero."""
        S = X = (0, 1)
        q = lambda y: y[0] ^ y[1]
        K = check({y: ({(0, 1): ONE} if q(y) == 0 else {(0, 0): ONE})
                   for y in product(S, X)})
        Kbar = check({0: {1: ONE}, 1: {0: ONE}})
        self.assertEqual(defect(K, Kbar, q), ZERO)
        self.assertFalse(is_type_respecting(q, S, X))
        self.assertTrue(is_type_respecting(lambda y: (y[0], 0), S, X))
        self.assertTrue(is_type_respecting(lambda y: y, S, X))

if __name__ == "__main__":
    unittest.main()
