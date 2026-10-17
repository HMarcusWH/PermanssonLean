"""Exact-Fraction adversaries for A3 (contractive W1 robustness, V20.16-V20.18).

Independent executable cross-checks of PermanssonResearch/Probability/
KantorovichDual, KantorovichTV and PermanssonResearch/Perturbation/
ContractiveOccupation, ContractiveAdversaries. Finite chains on points of the
real line only, where W1 has the exact formula sum |F_mu - F_nu| * gap; these are
NOT proofs of the general metric-space Lean theorems.
"""
from fractions import Fraction as F
from itertools import product
import random
import unittest

ZERO, ONE, HALF = F(0), F(1), F(1, 2)


def check(K):
    for row in K.values():
        assert sum(row.values(), ZERO) == ONE and all(v >= 0 for v in row.values())
    return K


def w1(mu, nu):
    """Exact W1 on real points: integral of |F_mu - F_nu|."""
    pts = sorted(set(mu) | set(nu))
    total, fm, fn = ZERO, ZERO, ZERO
    for a, b in zip(pts, pts[1:]):
        fm += mu.get(a, ZERO)
        fn += nu.get(a, ZERO)
        total += abs(fm - fn) * (F(b) - F(a))
    return total


def w1_dual_lower(mu, nu):
    """Value of the optimal 1-Lipschitz test f' = sign(F_mu - F_nu) (bounded
    because the support is finite): equals w1 (KR duality on the line)."""
    pts = sorted(set(mu) | set(nu))
    f, fm, fn, val = {pts[0]: ZERO}, ZERO, ZERO, ZERO
    for a, b in zip(pts, pts[1:]):
        fm += mu.get(a, ZERO)
        fn += nu.get(a, ZERO)
        f[b] = f[a] + (F(b) - F(a)) * (1 if fm < fn else -1)
    integ = lambda m: sum((p * f[x] for x, p in m.items()), ZERO)
    return abs(integ(mu) - integ(nu))


def tv(mu, nu):
    keys = set(mu) | set(nu)
    return sum((max(ZERO, mu.get(k, ZERO) - nu.get(k, ZERO)) for k in keys), ZERO)


def apply(mu, K):
    out = {}
    for x, p in mu.items():
        for y, q in K[x].items():
            out[y] = out.get(y, ZERO) + p * q
    return {k: v for k, v in out.items() if v}


def contraction(K):
    """Uniform W1 contraction coefficient sup_{x != y} W1(K_x, K_y) / |x - y|
    (this coefficient bounds W1(mu K, nu K) <= rho W1(mu, nu) by coupling)."""
    xs = sorted(K)
    return max(w1(K[x], K[y]) / abs(F(x) - F(y)) for x in xs for y in xs if x != y)


def defect(K, Kt):
    return max(w1(K[x], Kt[x]) for x in K)


def invariant(K):
    """Exact invariant law by Gaussian elimination (unique for these chains)."""
    xs = sorted(K)
    n = len(xs)
    idx = {x: i for i, x in enumerate(xs)}
    A = [[ZERO] * n for _ in range(n)]
    for x in xs:
        for y, q in K[x].items():
            A[idx[y]][idx[x]] += q
    for i in range(n):
        A[i][i] -= ONE
    A[-1] = [ONE] * n
    b = [ZERO] * (n - 1) + [ONE]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]
        b[c], b[piv] = b[piv], b[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                m = A[r][c] / A[c][c]
                A[r] = [a - m * ac for a, ac in zip(A[r], A[c])]
                b[r] -= m * b[c]
    pi = {x: b[idx[x]] / A[idx[x]][idx[x]] for x in xs}
    assert apply(pi, K) == {k: v for k, v in pi.items() if v}
    return pi


def mean(mu):
    return sum((p * F(x) for x, p in mu.items()), ZERO)


def random_kernel(rng, xs, theta=F(1, 4)):
    """Doeblin-type kernel K(x, .) = (1 - theta) nu + theta R_x with a common
    random law nu: W1(K_x, K_y) = theta W1(R_x, R_y) <= theta * diam, so the
    contraction coefficient is <= theta * diam / min_gap (< 1 for the grids used)."""
    def rlaw():
        w = [F(rng.randint(1, 6)) for _ in xs]
        return {y: wi / sum(w) for y, wi in zip(xs, w)}
    nu = rlaw()
    K = {}
    for x in xs:
        R = rlaw()
        K[x] = {y: (1 - theta) * nu[y] + theta * R[y] for y in xs}
    return check(K)


class DualFormTests(unittest.TestCase):

    def test_dual_equals_coupling_on_the_line(self):
        """The dual (bounded 1-Lipschitz test) value equals W1 on finite real
        supports. KR duality itself is NOT formalized in Lean; this is a check."""
        rng = random.Random(1)
        for _ in range(50):
            pts = sorted(rng.sample(range(10), 4))
            def law():
                w = [F(rng.randint(0, 5)) for _ in pts]
                if sum(w) == 0:
                    w[0] = ONE
                return {x: wi / sum(w) for x, wi in zip(pts, w) if wi}
            mu, nu = law(), law()
            self.assertEqual(w1_dual_lower(mu, nu), w1(mu, nu))

    def test_mixture_of_pointwise_defects(self):
        """Mirrors W1DualLE.comp_of_forall: W1(mu K, mu Kt) <= sup_y W1(K_y, Kt_y)."""
        rng = random.Random(2)
        xs = [0, 1, 3, 4]
        for _ in range(40):
            K, Kt = random_kernel(rng, xs), random_kernel(rng, xs)
            mu = {x: F(1, 4) for x in xs}
            self.assertLessEqual(w1(apply(mu, K), apply(mu, Kt)), defect(K, Kt))

    def test_pushforward_scales_by_lipschitz_constant(self):
        """Mirrors W1DualLE.map_lipschitz with h(x) = L x."""
        mu, nu = {0: HALF, 2: HALF}, {1: ONE}
        for L in (ZERO, F(1, 3), ONE, F(5, 2)):
            push = lambda m: {L * x: p for x, p in m.items()} if L else {0: ONE}
            self.assertLessEqual(w1(push(mu), push(nu)), L * w1(mu, nu))


class InvariantPerturbationTests(unittest.TestCase):

    def test_v20_17_random_contractive_pairs(self):
        """W1(pi, pi~) <= delta / (1 - rho) with rho the contraction coefficient
        of the ORIGINAL kernel and delta the pointwise defect."""
        rng = random.Random(3)
        xs = [0, 1, 2, 3]
        nontrivial = 0
        for _ in range(40):
            K, Kt = random_kernel(rng, xs), random_kernel(rng, xs)
            rho, delta = contraction(K), defect(K, Kt)
            self.assertLess(rho, ONE)
            gap = w1(invariant(K), invariant(Kt))
            bound = delta / (1 - rho)
            self.assertLessEqual(gap, bound)
            nontrivial += gap > 0
        self.assertGreater(nontrivial, 30)

    def test_one_minus_rho_factor_is_needed(self):
        """Slowly mixing two-state chains: delta fixed, rho -> 1, and
        W1(pi, pi~) / delta grows like 1/(1 - rho): the factor cannot be dropped."""
        d = F(1, 100)
        ratios = []
        for a in (F(1, 4), F(1, 16), F(1, 64)):
            K = check({0: {0: 1 - a, 1: a}, 1: {0: a, 1: 1 - a}})
            Kt = check({0: {0: 1 - a - d, 1: a + d}, 1: {0: a, 1: 1 - a}})
            rho, delta = contraction(K), defect(K, Kt)
            self.assertEqual((rho, delta), (1 - 2 * a, d))
            gap = w1(invariant(K), invariant(Kt))
            self.assertLessEqual(gap, delta / (1 - rho))
            ratios.append(gap / delta)
        self.assertTrue(ratios[0] < ratios[1] < ratios[2])
        self.assertGreater(ratios[2], 10 * ratios[0])

    def test_no_contraction_no_bound(self):
        """rho = 1 (identity kernel): every law is invariant; no finite bound."""
        K = check({0: {0: ONE}, 1: {1: ONE}})
        self.assertEqual(contraction(K), ONE)
        self.assertEqual(apply({0: ONE}, K), {0: ONE})
        self.assertEqual(apply({1: ONE}, K), {1: ONE})
        self.assertEqual(w1({0: ONE}, {1: ONE}), ONE)      # with delta = 0


class MarginTests(unittest.TestCase):

    def test_v20_18_margin_budget(self):
        """Descriptor h(x) = x (L_h = 1), functional F = mean (L_F = 1 for W1);
        effects factor through the invariant laws; |kappa~ - kappa| <= budget."""
        rng = random.Random(4)
        xs = [0, 1, 2, 3]
        checked = 0
        for _ in range(40):
            K0, K0t = random_kernel(rng, xs), random_kernel(rng, xs)
            KJ, KJt = random_kernel(rng, xs), random_kernel(rng, xs)
            kappa = abs(mean(invariant(K0)) - mean(invariant(KJ)))
            kappat = abs(mean(invariant(K0t)) - mean(invariant(KJt)))
            budget = (defect(K0, K0t) / (1 - contraction(K0))
                      + defect(KJ, KJt) / (1 - contraction(KJ)))
            self.assertLessEqual(abs(kappat - kappa), budget)
            for pi, pit in ((invariant(K0), invariant(K0t)), (invariant(KJ), invariant(KJt))):
                self.assertLessEqual(abs(mean(pi) - mean(pit)), w1(pi, pit))
            checked += 1
        self.assertEqual(checked, 40)


class LeakageTests(unittest.TestCase):

    def test_a3_3_survival_flips(self):
        """Mirrors contraction_does_not_transfer_survival: rho = 0 for both constant
        kernels, defect eps, survival of B = {0} is 1 versus (1 - eps)^n -> 0."""
        for eps in (F(1, 1000), F(1, 10), HALF, ONE):
            K = check({0: {0: ONE}, 1: {0: ONE}})
            Kt = check({0: {0: 1 - eps, 1: eps}, 1: {0: 1 - eps, 1: eps}})
            self.assertEqual((contraction(K), contraction(Kt)), (ZERO, ZERO))
            self.assertEqual(defect(K, Kt), eps)
            # survival of B = {0} from 0 through n steps: 1 for K, (1 - eps)^n for Kt
            surv = {0: ONE}
            for n in range(1, 13):
                surv = {y: p for y, p in apply(surv, Kt).items() if y == 0}
                self.assertEqual(sum(surv.values(), ZERO), (1 - eps) ** n)
                self.assertEqual(apply({0: ONE}, K), {0: ONE})
            # forever-survival is 0: the n-step survival drops below any 1/m
            n = next(n for n in range(1, 20000) if (1 - eps) ** n < F(1, 100))
            self.assertLess((1 - eps) ** n, F(1, 100))


class ConversionTests(unittest.TestCase):

    def test_bounded_diameter_conversion(self):
        """Mirrors W1DualLE.of_eventTV: W1 <= D * TV when all distances <= D."""
        rng = random.Random(5)
        for _ in range(60):
            D = rng.randint(1, 6)
            pts = list(range(D + 1))
            def law():
                w = [F(rng.randint(0, 4)) for _ in pts]
                if sum(w) == 0:
                    w[0] = ONE
                return {x: wi / sum(w) for x, wi in zip(pts, w) if wi}
            mu, nu = law(), law()
            self.assertLessEqual(w1(mu, nu), D * tv(mu, nu))

    def test_unbounded_no_conversion(self):
        """Mirrors tv_does_not_control_w1_on_real: TV = eps, W1 = eps * n."""
        eps = F(1, 50)
        for n in (1, 10, 1000):
            mu, nu = {0: ONE}, {0: 1 - eps, n: eps}
            self.assertEqual(tv(mu, nu), eps)
            self.assertEqual(w1(mu, nu), eps * n)
        self.assertGreater(w1({0: ONE}, {0: 1 - eps, 1000: eps}), 10 * eps)


if __name__ == "__main__":
    unittest.main()
