"""Exact-Fraction adversaries for C-Exit E (C70): random-entry occupation.

Independent executable cross-checks of the Lean statements in
RegimeExit/OccupationPrefixDeletion.lean, RandomEntryOccupation.lean,
InProbabilityOccupation.lean and Proposition42f.lean. They are NOT proofs:
almost-sure and in-probability limits are only probed at finite horizons,
while the finite identities and inequalities are checked exactly.
"""
from fractions import Fraction as F
from itertools import product
import unittest

ZERO, ONE, HALF = F(0), F(1), F(1, 2)
SOURCE = frozenset((0, 1))          # B
BASIN = frozenset((2,))             # B'_0
TARGET_REGION = frozenset((2, 3))   # B'


def check(K):
    for row in K.values():
        assert sum(row.values(), ZERO) == ONE
        assert all(v >= 0 for v in row.values())
    return K


def switch_chain():
    """0,1 in source; 2 basin of an invariant 2-cycle {2,3}; 4 a
    never-routed trap whose descriptor differs."""
    return check({0: {0: F(1, 4), 2: F(1, 2), 4: F(1, 4)},
                  1: {0: HALF, 2: HALF},
                  2: {3: ONE}, 3: {2: ONE}, 4: {4: ONE}})


def leaky_chain():
    """Entry into 2 is NOT followed by invariance: 2 leaks back to 0."""
    return check({0: {0: F(1, 4), 2: F(3, 4)},
                  1: {0: HALF, 2: HALF},
                  2: {3: HALF, 0: HALF}, 3: {2: ONE}, 4: {4: ONE}})


def descriptor(z):
    """Global descriptor h': 1 on the target cycle, 0 elsewhere."""
    return ONE if z in TARGET_REGION else ZERO


def paths(K, y, length):
    """All (path, prob) with path of `length` states starting at y."""
    cur = {(y,): ONE}
    for _ in range(length - 1):
        nxt = {}
        for w, p in cur.items():
            for z, q in K[w[-1]].items():
                nxt[w + (z,)] = nxt.get(w + (z,), ZERO) + p * q
        cur = nxt
    return cur


def first_exit(w):
    """Index of first exit from SOURCE (None if none in the prefix)."""
    for t, z in enumerate(w):
        if z not in SOURCE:
            return t
    return None


def avg(vals):
    return sum(vals, ZERO) / len(vals)


class PrefixDeletionTests(unittest.TestCase):
    """abs_average_sub_shift_average_le: |avg_{k+T} - avg_T(shift)| <= 2kC/(k+T)."""

    def test_bound_exhaustive_small_sequences(self):
        values = (F(-1), F(-1, 2), ZERO, F(1, 3), ONE)
        C = ONE
        for k in range(0, 4):
            for T in range(1, 4):
                for g in product(values, repeat=k + T):
                    lhs = abs(avg(g) - avg(g[k:]))
                    self.assertLessEqual(lhs, 2 * k * C / (k + T))

    def test_bound_is_attained(self):
        # prefix all +C then suffix all -C: |(kC - TC)/(k+T) - (-C)| = 2kC/(k+T)
        for k in range(1, 5):
            for T in range(1, 5):
                g = (ONE,) * k + (-ONE,) * T
                self.assertEqual(abs(avg(g) - avg(g[k:])), F(2 * k, k + T))

    def test_deletion_error_vanishes(self):
        k, C = 7, ONE
        errs = [F(2 * k) * C / (k + T) for T in (10, 100, 1000, 10000)]
        self.assertTrue(all(a > b for a, b in zip(errs, errs[1:])))
        self.assertLess(errs[-1], F(1, 700))


class RandomEntryOccupationTests(unittest.TestCase):

    def test_post_entry_occupation_exact_on_invariant_cycle(self):
        """After entry into basin 2 of the invariant cycle the post-entry
        descriptor is identically 1: occupation equals the target delta_1."""
        K = switch_chain()
        for w, p in paths(K, 0, 9).items():
            tau = first_exit(w)
            if tau is not None and w[tau] in BASIN:
                self.assertTrue(all(descriptor(z) == ONE for z in w[tau:]))

    def test_whole_path_occupation_converges_with_explicit_rate(self):
        """Whole-path average of h' differs from 1 by exactly tau/T after entry."""
        K = switch_chain()
        T = 10
        for w, p in paths(K, 0, T).items():
            tau = first_exit(w)
            if tau is not None and w[tau] in BASIN:
                self.assertEqual(ONE - avg([descriptor(z) for z in w]), F(tau, T))

    def test_routing_mass_and_never_routed_mass(self):
        """Routed mass 2/3 from 0; trap mass 1/3 never converges to the target."""
        K = switch_chain()
        L = 14
        routed = sum((p for w, p in paths(K, 0, L).items()
                      if first_exit(w) is not None and w[first_exit(w)] in BASIN), ZERO)
        trapped = sum((p for w, p in paths(K, 0, L).items()
                       if first_exit(w) is not None and w[first_exit(w)] == 4), ZERO)
        remainder = F(1, 4) ** (L - 1)
        self.assertEqual(routed + trapped + remainder, ONE)
        self.assertEqual(routed, F(2, 3) * (1 - remainder))
        self.assertEqual(trapped, F(1, 3) * (1 - remainder))

    def test_deviation_probability_bounded_by_eta(self):
        """In-probability corollary: P(|avg h' - 1| > eps) <= eta + o(1) with
        eta = 1/3 the never-routed mass; it does NOT tend to zero."""
        K = switch_chain()
        eps = F(1, 4)
        for T in (8, 12, 14):
            dev = sum((p for w, p in paths(K, 0, T).items()
                       if abs(avg([descriptor(z) for z in w]) - ONE) > eps), ZERO)
            routed_dev = sum((p for w, p in paths(K, 0, T).items()
                              if abs(avg([descriptor(z) for z in w]) - ONE) > eps
                              and first_exit(w) is not None
                              and w[first_exit(w)] in BASIN), ZERO)
            with self.subTest(T=T):
                self.assertLessEqual(dev, F(1, 3) + routed_dev + F(1, 4) ** (T - 1))
                self.assertGreaterEqual(dev, F(1, 3) * (1 - F(1, 4) ** (T - 1)))
                # routed deviation needs tau > eps*T: geometric tail
                self.assertLessEqual(routed_dev, F(1, 4) ** (int(eps * T) - 1))

    def test_per_exit_time_restart_bound(self):
        """firstExit_shift_le_mass_mul + occupationDeviation_subset_shift:
        P(E_k ∩ Dev_eps(T)) <= c_k * P_nu_k(Dev_{eps/2}(T-k-1)) <= c_k, under
        the lemma's hypothesis 2(k+1)C/T < eps/2. Test function
        f = 2h' - 1 in [-1, 1] (C = 1), target integral L = 1, leaky chain
        (so both sides are genuinely positive)."""
        K = leaky_chain()
        f = lambda z: 2 * descriptor(z) - 1
        eps, C, T = ONE, ONE, 13
        for k in range(0, 3):
            err = F(2 * (k + 1)) * C / T
            lhs = sum((p for w, p in paths(K, 0, T).items()
                       if first_exit(w) == k + 1 and w[k + 1] in BASIN
                       and abs(avg([f(z) for z in w]) - ONE) > eps), ZERO)
            arrivals = {}
            for w, p in paths(K, 0, k + 2).items():
                if first_exit(w) == k + 1 and w[k + 1] in BASIN:
                    arrivals[w[k + 1]] = arrivals.get(w[k + 1], ZERO) + p
            c = sum(arrivals.values(), ZERO)
            rhs = ZERO
            for z, pz in arrivals.items():
                rhs += pz * sum((q for v, q in paths(K, z, T - (k + 1)).items()
                                 if abs(avg([f(x) for x in v]) - ONE) > eps / 2), ZERO)
            with self.subTest(k=k):
                self.assertLess(err, eps / 2)          # lemma hypothesis holds
                self.assertGreater(lhs, ZERO)          # nonvacuous
                self.assertLessEqual(lhs, rhs)
                self.assertLessEqual(rhs, c)

    def test_per_exit_time_hypothesis_is_needed(self):
        """Without the deletion-error hypothesis the inclusion can fail:
        a short horizon where the source prefix alone causes the deviation."""
        K = switch_chain()
        f = lambda z: 2 * descriptor(z) - 1
        eps, T, k = ONE, 3, 1
        self.assertGreaterEqual(F(2 * (k + 1), T), eps / 2)
        lhs = sum((p for w, p in paths(K, 0, T).items()
                   if first_exit(w) == k + 1 and w[k + 1] in BASIN
                   and abs(avg([f(z) for z in w]) - ONE) > eps), ZERO)
        rhs = ZERO   # post-entry path is identically on target: no deviation
        self.assertGreater(lhs, rhs)


class FirewallCounterexampleTests(unittest.TestCase):

    def test_leaky_target_entry_does_not_certify_occupation(self):
        """Entering basin 2 without target invariance: the long-run fraction
        of time on the target cycle is strictly below 1 (exact stationary law
        of the recurrent class {0,2,3})."""
        K = leaky_chain()
        # stationary pi on {0,2,3}: pi0 = 1/4 pi0 + 1/2 pi2 ; pi2 = 3/4 pi0 + pi3 ;
        # pi3 = 1/2 pi2 ; normalized
        pi2 = ONE
        pi3 = HALF * pi2
        pi0 = (HALF * pi2) / (ONE - F(1, 4))
        tot = pi0 + pi2 + pi3
        pi = {0: pi0 / tot, 2: pi2 / tot, 3: pi3 / tot}
        for j in pi:
            self.assertEqual(sum(pi[i] * K[i].get(j, ZERO) for i in pi), pi[j])
        target_share = pi[2] + pi[3]
        self.assertEqual(target_share, F(9, 13))
        self.assertLess(target_share, ONE)

    def test_custom_mode_without_prefix_invariance_not_transported(self):
        """A custom 'horizon-1 occupation equals target' predicate holds from
        every basin start but fails for the whole path after random entry
        from the source: deleting the prefix is not harmless for it."""
        K = switch_chain()
        for w, p in paths(K, 2, 5).items():
            self.assertEqual(descriptor(w[0]), ONE)       # holds from basin
        for w, p in paths(K, 0, 5).items():
            self.assertEqual(descriptor(w[0]), ZERO)      # fails from source

    def test_eta_one_gives_no_routing_guarantee(self):
        """Routing bound with eta = 1 is vacuous: a chain that never routes
        satisfies it, and the switching probability is zero."""
        K = check({0: {0: ONE}, 1: {1: ONE}, 2: {3: ONE}, 3: {2: ONE}, 4: {4: ONE}})
        routed = sum((p for w, p in paths(K, 0, 12).items()
                      if first_exit(w) is not None), ZERO)
        self.assertEqual(routed, ZERO)
        self.assertGreaterEqual(routed, 1 - ONE)


if __name__ == "__main__":
    unittest.main()
