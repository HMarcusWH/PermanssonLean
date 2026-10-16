"""Exact-Fraction tests for C-Exit C stopped-future routing.

These independently compute finite-cylinder conditionals from a literal
finite Markov matrix. They do not substitute for the arbitrary measurable
infinite-path restart theorem in Lean.
"""
from fractions import Fraction as F
import unittest

ZERO, ONE, HALF = F(0), F(1), F(1, 2)
STATES = (0, 1, 2, 3, 4)
SOURCE = frozenset((0, 1, 4))
TARGET = frozenset((2, 3))

def check(K):
    assert set(K) == set(STATES)
    for row in K.values():
        assert sum(row.values(), ZERO) == ONE
        assert all(v >= 0 for v in row.values())
        assert set(row) <= set(STATES)
    return K

def switched():
    return check({0:{0:HALF, 2:HALF}, 1:{1:HALF,3:HALF},
                  2:{3:ONE}, 3:{3:ONE}, 4:{4:ONE}})

def partial():
    return check({0:{4:HALF,2:HALF}, 1:{4:HALF,3:HALF},
                  2:{3:ONE}, 3:{3:ONE}, 4:{4:ONE}})

def baseline():
    return check({0:{1:ONE}, 1:{4:ONE}, 2:{3:ONE},
                  3:{3:ONE}, 4:{4:ONE}})

def branching():
    """Two distinct exit destinations and stochastic post-arrival futures."""
    return check({0:{0:F(1,4),2:F(1,2),3:F(1,4)},
                  1:{1:F(1,4),2:F(1,4),3:F(1,2)},
                  2:{2:F(1,3),3:F(2,3)},
                  3:{3:ONE},4:{4:ONE}})

def arrival_submeasure(K, start, n):
    """Mass exiting exactly at observation n+1; no normalization."""
    living={start:ONE}
    for _ in range(n):
        stepped={}
        for y,p in living.items():
            for z,q in K[y].items():
                if z in SOURCE:
                    stepped[z]=stepped.get(z,ZERO)+p*q
        living=stepped
    landed={}
    for y,p in living.items():
        for z,q in K[y].items():
            if z not in SOURCE:
                landed[z]=landed.get(z,ZERO)+p*q
    return landed

def path_weight(K, word):
    """Probability of a complete finite path, including time-zero state."""
    result=ONE
    for a,b in zip(word,word[1:]):
        result *= K[a].get(b,ZERO)
    return result

def future_prob(K,z,word):
    return path_weight(K,(z,)+tuple(word))

def direct(K,start,n,D,tail):
    """Explicit enumeration from time 0 through the requested tail."""
    horizon = (n+1) + max(0, len(tail)-1)
    curr={(start,):ONE}
    for _ in range(horizon):
        nxt={}
        for w,p in curr.items():
            for z,q in K[w[-1]].items():
                w2=w+(z,)
                nxt[w2]=nxt.get(w2,ZERO)+p*q
        curr=nxt
    return sum((p for w,p in curr.items()
        if all(z in SOURCE for z in w[:n+1])
        and w[n+1] in (set(D)-SOURCE)
        and (not tail or tuple(w[n+1:])==tuple(tail))),ZERO)

def mixture(K,start,n,D,tail):
    arrival=arrival_submeasure(K,start,n)
    if not tail:
        return sum((p for z,p in arrival.items() if z in (set(D)-SOURCE)),ZERO)
    return sum((p*path_weight(K,tail) for z,p in arrival.items()
        if z in (set(D)-SOURCE) and z==tail[0]),ZERO)

class StoppedFutureTests(unittest.TestCase):
    def test_full_matrix_stochastic(self): self.assertEqual(len(switched()),5)
    def test_partial_matrix_stochastic(self): self.assertEqual(len(partial()),5)
    def test_baseline_matrix_stochastic(self): self.assertEqual(len(baseline()),5)
    def test_half_arrival_at_step_one(self):
        self.assertEqual(arrival_submeasure(switched(),0,0),{2:HALF})
    def test_half_arrival_other_start(self):
        self.assertEqual(arrival_submeasure(switched(),1,0),{3:HALF})
    def test_delayed_arrival(self):
        self.assertEqual(arrival_submeasure(switched(),0,4),{2:F(1,32)})
    def test_no_exit_baseline(self):
        self.assertEqual(arrival_submeasure(baseline(),0,5),{})
    def test_no_exit_already_absorbing(self):
        self.assertEqual(arrival_submeasure(switched(),4,5),{})
    def test_destination_mask(self):
        self.assertEqual(mixture(switched(),0,0,{0,1,2,3,4},(2,3)),HALF)
    def test_wrong_destination(self):
        self.assertEqual(mixture(switched(),0,0,{3},(2,3)),ZERO)
    def test_zero_mass_condition(self):
        self.assertEqual(mixture(switched(),1,0,{2},(2,3)),ZERO)
    def test_partial_reaches_target(self):
        self.assertEqual(mixture(partial(),0,0,{2,3},(2,3)),HALF)
    def test_partial_stays_source_otherwise(self):
        self.assertEqual(sum(arrival_submeasure(partial(),0,0).values(),ZERO),HALF)
    def test_future_starts_at_arrival_state(self):
        self.assertEqual(future_prob(switched(),2,(3,3)),ONE)
    def test_future_wrong_word(self):
        self.assertEqual(future_prob(switched(),2,(2,2)),ZERO)
    def test_delayed_future_total(self):
        self.assertEqual(mixture(switched(),0,3,{2,3},()),F(1,16))
    def test_delayed_future_observed(self):
        self.assertEqual(mixture(switched(),0,3,{2,3},(2,3,3)),F(1,16))
    def test_never_exit_tail_positive(self):
        self.assertEqual(F(1,2)**8,F(1,256))
    def test_exact_finite_cylinders(self):
        for K in (switched(),partial(),baseline(),branching()):
            for y in (0,1):
                for n in (0,1,2,3):
                    for D in ({2,3},{2},{3},set(STATES)):
                        for tail in ((2,),(2,3),(2,3,3),(3,3),(3,3,3)):
                            with self.subTest(start=y,n=n,dest=D,tail=tail):
                                self.assertEqual(direct(K,y,n,D,tail),mixture(K,y,n,D,tail))
    def test_branching_multiple_arrivals(self):
        self.assertEqual(arrival_submeasure(branching(),0,0),
                         {2:F(1,2),3:F(1,4)})
    def test_branching_both_destinations_total(self):
        self.assertEqual(mixture(branching(),0,0,{2,3},()),F(3,4))
    def test_branching_delayed_mass(self):
        self.assertEqual(arrival_submeasure(branching(),0,1),
                         {2:F(1,8),3:F(1,16)})
    def test_branching_future_not_just_endpoint(self):
        self.assertEqual(mixture(branching(),0,0,{2,3},(2,2,3)),F(1,9))
        self.assertEqual(mixture(branching(),0,0,{2,3},(2,3,3)),F(1,3))
        self.assertEqual(mixture(branching(),0,0,{2,3},(3,3,3)),F(1,4))
    def test_branching_future_event_zero(self):
        self.assertEqual(mixture(branching(),0,0,{2,3},(3,2)),ZERO)
    def test_empty_tail_direct_matches_routing(self):
        self.assertEqual(direct(branching(),0,0,{2,3},()),
                         mixture(branching(),0,0,{2,3},()))
    def test_post_exit_kernel_change_is_not_the_same_protocol(self):
        altered=branching()
        altered[2]={3:ONE}
        self.assertNotEqual(direct(altered,0,0,{2,3},(2,2,3)),
                            mixture(branching(),0,0,{2,3},(2,2,3)))
    def test_branching_eventual_absorption_geometric_identity(self):
        self.assertEqual(F(2,3)/(ONE-F(1,3)),ONE)
    def test_independent_tail_words_not_just_endpoint(self):
        self.assertEqual(mixture(switched(),0,0,{2,3},(2,3,3)),HALF)
        self.assertEqual(mixture(switched(),0,0,{2,3},(2,2,2)),ZERO)


# ---------------------------------------------------------------------------
# C69 (PR #69) — unconditional last-state restart and countable routing.
# Independent exact-Fraction computations from literal matrices. These are
# executable cross-checks of the Lean statements, NOT proofs of them.
# ---------------------------------------------------------------------------

def survivor():
    """Positive never-exit mass: state 4 is an absorbing trap INSIDE B."""
    return check({0:{0:F(1,4),4:F(1,4),2:F(1,2)},
                  1:{0:F(1,3),1:F(1,3),3:F(1,3)},
                  2:{2:F(1,2),3:F(1,2)},
                  3:{3:F(1,2),2:F(1,2)},
                  4:{4:ONE}})

def history_prob(K, hist):
    """P_{hist[0]}(Y_0..Y_m = hist): exact finite cylinder weight."""
    return path_weight(K, tuple(hist))

def conditional_future(K, hist, word):
    """P(Y_{m..m+k} = word | Y_{0..m} = hist), computed by brute force
    on the ORIGINAL chain (not by the restart formula)."""
    assert word and word[0] == hist[-1]
    joint = path_weight(K, tuple(hist) + tuple(word[1:]))
    base = history_prob(K, hist)
    assert base > 0
    return joint / base

def future_event_prob(K, z, event, horizon):
    """P_z(event) for an event given as a predicate on the (horizon+1)-word."""
    total = ZERO
    words = {(z,): ONE}
    for _ in range(horizon):
        nxt = {}
        for w, p in words.items():
            for v, q in K[w[-1]].items():
                nxt[w + (v,)] = nxt.get(w + (v,), ZERO) + p * q
        words = nxt
    for w, p in words.items():
        if event(w):
            total += p
    return total

def direct_event(K, start, n, D, event, horizon):
    """Brute-force P_y(first exit at n+1 into D\\B, theta_{n+1} word in event)."""
    total = ZERO
    words = {(start,): ONE}
    for _ in range(n + 1 + horizon):
        nxt = {}
        for w, p in words.items():
            for v, q in K[w[-1]].items():
                nxt[w + (v,)] = nxt.get(w + (v,), ZERO) + p * q
        words = nxt
    for w, p in words.items():
        if (all(x in SOURCE for x in w[:n + 1]) and w[n + 1] in set(D) - SOURCE
                and event(w[n + 1:])):
            total += p
    return total

def mixture_event(K, start, n, D, event, horizon):
    arr = arrival_submeasure(K, start, n)
    return sum((p * future_event_prob(K, z, event, horizon)
                for z, p in arr.items() if z in set(D) - SOURCE), ZERO)

def solve_exact(Amat, b):
    """Exact Gaussian elimination over Fractions."""
    n = len(b)
    M = [list(row) + [bi] for row, bi in zip(Amat, b)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [v / pv for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return [M[r][n] for r in range(n)]

def can_exit(K):
    reach = {y for y in SOURCE if any(z not in SOURCE for z in K[y])}
    changed = True
    while changed:
        changed = False
        for y in SOURCE:
            if y not in reach and any(z in reach for z in K[y] if z in SOURCE):
                reach.add(y); changed = True
    return reach

def infinite_routing(K, start, D):
    """Exact R_B^(inf)(start, D) = sum_n (K_B^n E_B)(start, D)."""
    T = sorted(can_exit(K))
    if start not in T:
        return ZERO
    idx = {y: i for i, y in enumerate(T)}
    Amat = [[(ONE if i == j else ZERO) - K[y].get(T[j], ZERO)
             for j in range(len(T))] for i, y in enumerate(T)]
    b = [sum((q for z, q in K[y].items() if z in set(D) - SOURCE), ZERO) for y in T]
    return solve_exact(Amat, b)[idx[start]]

def infinite_arrival(K, start):
    """Exact infinite routing measure on singleton destinations."""
    return {z: infinite_routing(K, start, {z}) for z in STATES if z not in SOURCE}

def finite_routing(K, start, D, L):
    return sum((sum((p for z, p in arrival_submeasure(K, start, n).items()
                     if z in set(D) - SOURCE), ZERO) for n in range(L)), ZERO)

def killed_survival(K, start, L):
    living = {start: ONE}
    for _ in range(L):
        nxt = {}
        for y, p in living.items():
            for z, q in K[y].items():
                if z in SOURCE:
                    nxt[z] = nxt.get(z, ZERO) + p * q
        living = nxt
    return sum(living.values(), ZERO)

def forever_survival(K, start):
    return ONE - infinite_routing(K, start, set(STATES) - SOURCE)

def time_inhomogeneous_direct(kernels, start, n, D, word):
    """Brute force for a NONSTATIONARY chain with kernel K_t at step t."""
    total = ZERO
    words = {(start,): ONE}
    for t in range(n + len(word)):
        Kt = kernels(t)
        nxt = {}
        for w, p in words.items():
            for v, q in Kt[w[-1]].items():
                nxt[w + (v,)] = nxt.get(w + (v,), ZERO) + p * q
        words = nxt
    for w, p in words.items():
        if (all(x in SOURCE for x in w[:n + 1]) and w[n + 1] in set(D) - SOURCE
                and tuple(w[n + 1:]) == tuple(word)):
            total += p
    return total


class C69LastStateRestartTests(unittest.TestCase):
    """C69.1/C69.2: the conditional future depends on the history only
    through its LAST state, for every horizon (not just one coordinate)."""

    def test_different_pasts_same_last_state(self):
        K = branching()
        h1, h2, h3 = (0, 0, 2), (1, 1, 2), (0, 2)
        for word in ((2,), (2, 3), (2, 2, 3), (2, 2, 2, 3), (2, 3, 3, 3)):
            with self.subTest(word=word):
                a = conditional_future(K, h1, word)
                self.assertEqual(a, conditional_future(K, h2, word))
                self.assertEqual(a, conditional_future(K, h3, word))
                self.assertEqual(a, future_prob(K, 2, word[1:]))

    def test_every_prefix_horizon_matches_restart(self):
        K = survivor()
        for hist in ((0, 0, 2), (1, 0, 0, 2), (0, 2), (1, 3), (1, 1, 3)):
            z = hist[-1]
            for T in range(0, 5):
                words = {(z,): ONE}
                for _ in range(T):
                    nxt = {}
                    for w, p in words.items():
                        for v, q in K[w[-1]].items():
                            nxt[w + (v,)] = p * q
                    words = nxt
                for w, p in words.items():
                    with self.subTest(hist=hist, T=T, word=w):
                        self.assertEqual(conditional_future(K, hist, w), p)

    def test_shifted_time_zero_is_last_state(self):
        K = branching()
        self.assertEqual(conditional_future(K, (0, 0, 3), (3,)), ONE)

    def test_negative_control_past_dependent_chain(self):
        """A second-order (history-dependent) chain violates last-state
        restart: the Lean theorem needs the canonical stationary
        last-state kernel, it is not a property of arbitrary processes."""
        def second_order(prev, cur):
            if cur == 2:
                return {3: ONE} if prev == 0 else {2: ONE}
            return branching()[cur]
        def weight(word):
            p = ONE
            for i in range(1, len(word)):
                prev = word[i - 2] if i >= 2 else None
                p *= second_order(prev, word[i - 1]).get(word[i], ZERO)
            return p
        a = weight((0, 2, 3)) / weight((0, 2))
        b = weight((1, 2, 3)) / weight((1, 2))
        self.assertNotEqual(a, b)


class C69StoppedFutureTests(unittest.TestCase):
    """C69.3: finite first exit at n+1 restarts at the exit endpoint for
    future-DEPENDENT events, with unnormalized arrival submeasures."""

    EVENTS = {
        "visits_2_twice": lambda w: sum(1 for x in w if x == 2) >= 2,
        "ends_in_3": lambda w: w[-1] == 3,
        "alternates": lambda w: all(a != b for a, b in zip(w, w[1:])),
        "never_3_after_arrival": lambda w: all(x != 3 for x in w[1:]),
        "everything": lambda w: True,
        "nothing": lambda w: False,
    }

    def test_future_dependent_events(self):
        for K in (branching(), survivor(), switched(), partial()):
            for y in (0, 1):
                for n in (0, 1, 2):
                    for D in ({2}, {3}, {2, 3}, set(STATES)):
                        for name, ev in self.EVENTS.items():
                            for horizon in (1, 3):
                                with self.subTest(y=y, n=n, D=D, ev=name, H=horizon):
                                    self.assertEqual(
                                        direct_event(K, y, n, D, ev, horizon),
                                        mixture_event(K, y, n, D, ev, horizon))

    def test_first_exit_time_is_n_plus_one_not_n(self):
        K = switched()
        # exit at time 1 has mass 1/2; the formula indexed at n (time 0)
        # would read the start state 0 in B and give zero destination mass
        self.assertEqual(sum(arrival_submeasure(K, 0, 0).values(), ZERO), HALF)
        self.assertEqual(direct(K, 0, 0, {2}, (2, 3)), HALF)
        self.assertNotEqual(direct(K, 0, 0, {2}, (2, 3)),
                            mixture(K, 0, 1, {2}, (2, 3)))

    def test_destination_inside_B_is_masked(self):
        K = survivor()
        self.assertEqual(mixture_event(K, 0, 0, {0, 4}, lambda w: True, 2), ZERO)
        self.assertEqual(mixture_event(K, 0, 0, {0, 2}, lambda w: True, 2),
                         mixture_event(K, 0, 0, {2}, lambda w: True, 2))

    def test_competing_destinations_add(self):
        for K in (branching(), survivor()):
            for n in (0, 1, 2):
                for ev in self.EVENTS.values():
                    with self.subTest(n=n):
                        both = mixture_event(K, 0, n, {2, 3}, ev, 3)
                        self.assertEqual(both,
                            mixture_event(K, 0, n, {2}, ev, 3) +
                            mixture_event(K, 0, n, {3}, ev, 3))

    def test_zero_arrival_is_not_normalized(self):
        K = baseline()
        for n in range(4):
            self.assertEqual(arrival_submeasure(K, 0, n), {})
            self.assertEqual(mixture_event(K, 0, n, {2, 3}, lambda w: True, 2), ZERO)
            self.assertEqual(direct_event(K, 0, n, {2, 3}, lambda w: True, 2), ZERO)

    def test_arrival_submeasure_mass_below_one(self):
        K = survivor()
        self.assertEqual(sum(arrival_submeasure(K, 0, 0).values(), ZERO), HALF)
        self.assertLess(sum(arrival_submeasure(K, 0, 0).values(), ZERO), ONE)

    def test_post_intervention_kernel_mismatch_rejected(self):
        """The restart law must be the SAME (post-intervention) kernel:
        mixing J-arrivals with baseline futures is wrong."""
        KJ, K0 = survivor(), branching()
        arr = arrival_submeasure(KJ, 1, 0)
        wrong = sum((p * future_prob(K0, z, (3, 3)) for z, p in arr.items()), ZERO)
        right = direct(KJ, 1, 0, {2, 3}, (3, 3, 3))
        self.assertEqual(right, mixture(KJ, 1, 0, {2, 3}, (3, 3, 3)))
        self.assertNotEqual(right, wrong)

    def test_nonstationary_kernel_breaks_restart(self):
        """Counterexample to silently dropping stationarity: with a
        time-dependent kernel, the future after exit is NOT P_z of the
        time-zero kernel."""
        K0 = switched()
        K1 = check({0: {0: HALF, 2: HALF}, 1: {1: HALF, 3: HALF},
                    2: {2: ONE}, 3: {3: ONE}, 4: {4: ONE}})
        kernels = lambda t: K0 if t == 0 else K1
        lhs = time_inhomogeneous_direct(kernels, 0, 0, {2}, (2, 3))
        restart_with_time0_kernel = mixture(K0, 0, 0, {2}, (2, 3))
        self.assertEqual(lhs, ZERO)
        self.assertEqual(restart_with_time0_kernel, HALF)
        self.assertNotEqual(lhs, restart_with_time0_kernel)


class C69CountableRoutingTests(unittest.TestCase):
    """C69.4: countable sum over finite exit times, exact infinite
    routing, preserved never-exit mass."""

    def test_infinite_routing_closed_form(self):
        K = survivor()
        # from 0: stay w.p. 1/4, trap 4 w.p. 1/4, exit to 2 w.p. 1/2
        self.assertEqual(infinite_routing(K, 0, {2}), F(2, 3))
        self.assertEqual(infinite_routing(K, 0, {3}), ZERO)
        self.assertEqual(forever_survival(K, 0), F(1, 3))

    def test_never_exit_mass_preserved(self):
        for K in (survivor(), branching(), switched(), partial(), baseline()):
            for y in sorted(SOURCE):
                with self.subTest(y=y):
                    total = infinite_routing(K, y, set(STATES) - SOURCE)
                    self.assertEqual(total + forever_survival(K, y), ONE)
                    self.assertGreaterEqual(forever_survival(K, y), ZERO)
        self.assertGreater(forever_survival(survivor(), 0), ZERO)
        self.assertEqual(forever_survival(baseline(), 0), ONE)

    def test_finite_partial_sums_and_exact_remainder(self):
        """R^(inf) - R^(L) = (K_B^L R^(inf)) exactly: the countable sum is
        the limit of the finite routing, with an explicit remainder."""
        for K in (survivor(), branching(), switched(), partial()):
            for y in (0, 1):
                for D in ({2}, {3}, {2, 3}):
                    Rinf = {x: infinite_routing(K, x, D) for x in SOURCE}
                    for L in range(0, 7):
                        living = {y: ONE}
                        for _ in range(L):
                            nxt = {}
                            for a, p in living.items():
                                for b, q in K[a].items():
                                    if b in SOURCE:
                                        nxt[b] = nxt.get(b, ZERO) + p * q
                            living = nxt
                        remainder = sum((p * Rinf[a] for a, p in living.items()), ZERO)
                        with self.subTest(y=y, D=D, L=L):
                            self.assertEqual(Rinf[y] - finite_routing(K, y, D, L),
                                             remainder)
                            self.assertEqual(finite_routing(K, y, set(STATES) - SOURCE, L)
                                             + killed_survival(K, y, L), ONE)

    def test_infinite_stopped_future_mixture(self):
        """mu_D^inf(F) = int P_z(F) R^inf(y,dz)|_D and its tail remainder."""
        for K in (survivor(), branching()):
            for y in (0, 1):
                for D in ({2}, {3}, {2, 3}):
                    for ev in C69StoppedFutureTests.EVENTS.values():
                        Rinf_pts = infinite_arrival(K, y)
                        mix = sum((Rinf_pts[z] * future_event_prob(K, z, ev, 3)
                                   for z in Rinf_pts if z in D), ZERO)
                        # sum over exit times n < L (brute force) plus the
                        # exact remainder from surviving mass at time L
                        L = 4
                        partial_direct = sum((direct_event(K, y, n, D, ev, 3)
                                              for n in range(L)), ZERO)
                        living = {y: ONE}
                        for _ in range(L):
                            nxt = {}
                            for a, p in living.items():
                                for b, q in K[a].items():
                                    if b in SOURCE:
                                        nxt[b] = nxt.get(b, ZERO) + p * q
                            living = nxt
                        rem = sum((p * sum((infinite_routing(K, a, {z}) *
                                            future_event_prob(K, z, ev, 3)
                                            for z in D if z not in SOURCE), ZERO)
                                   for a, p in living.items()), ZERO)
                        with self.subTest(y=y, D=D):
                            self.assertEqual(partial_direct + rem, mix)

    def test_routing_zero_gives_zero_future(self):
        K = survivor()
        self.assertEqual(infinite_routing(K, 4, {2, 3}), ZERO)
        self.assertEqual(infinite_routing(K, 0, {3}), ZERO)
        for ev in C69StoppedFutureTests.EVENTS.values():
            self.assertEqual(sum((direct_event(K, 0, n, {3}, ev, 2)
                                  for n in range(6)), ZERO), ZERO)

    def test_infinite_routing_not_normalized(self):
        K = survivor()
        total = infinite_routing(K, 0, set(STATES) - SOURCE)
        self.assertEqual(total, F(2, 3))
        self.assertNotEqual(total, ONE)

    def test_stopped_future_never_exceeds_routing_mass(self):
        K = branching()
        for y in (0, 1):
            Rinf_pts = infinite_arrival(K, y)
            for ev in C69StoppedFutureTests.EVENTS.values():
                mix = sum((Rinf_pts[z] * future_event_prob(K, z, ev, 3)
                           for z in Rinf_pts), ZERO)
                self.assertLessEqual(mix, sum(Rinf_pts.values(), ZERO))


if __name__ == "__main__": unittest.main()
