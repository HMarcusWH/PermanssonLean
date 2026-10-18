"""Independent exact-arithmetic adversaries for A2-P02 localized finite-prefix bounds.

This suite is NOT a Lean proof. It checks the intended law/visit/score/margin
semantics with Python Fraction, and deliberately attempts incorrect contracts.
No external data or floats are used. Two explicitly seeded randomized test loops
supplement the fixed cases; neither substitutes for universal Lean proofs.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import product
import random
import unittest

STATES = (0, 1, 2)
MAX_HORIZON = 8  # finite test-oracle resource limit, not a theorem restriction


def rational(value):
    if isinstance(value, Q):
        return value
    if type(value) is int:
        return Q(value)
    raise ValueError("probabilities and budgets require exact int/Fraction values; not float/bool")


def validate_horizon(T):
    if type(T) is not int or not 0 <= T <= MAX_HORIZON:
        raise ValueError("invalid horizon or exact-oracle resource limit")


def initial_law(initial):
    if not initial or any(type(z) is not int or z not in STATES for z in initial):
        raise ValueError("initial law contains an unknown state")
    data = {z: rational(v) for z, v in initial.items()}
    if sum(data.values(), Q(0)) != 1 or any(v < 0 for v in data.values()):
        raise ValueError("initial law is not a probability")
    return data


def checked_good(good, n, w):
    value = good(n, w)
    if type(value) is not bool:
        raise ValueError("good-history predicate must return bool")
    return value


def check_domain(frozen, claimed):
    if not frozen or len(set(frozen)) != len(frozen):
        raise ValueError("frozen comparison domain must be nonempty and have unique starts")
    if len(set(claimed)) != len(claimed) or set(claimed) != set(frozen):
        raise ValueError("claimed domain is not the entire frozen comparison domain")
    return tuple(frozen)


def kernel(rows):
    if set(rows) != set(STATES) or any(type(z) is not int for z in rows):
        raise ValueError("wrong set of source states")
    result = {}
    for y in STATES:
        row = tuple(rational(v) for v in rows[y])
        if len(row) != len(STATES) or min(row) < 0 or sum(row) != 1:
            raise ValueError("every stochastic row must be normalized and nonnegative")
        result[y] = row
    return result


def deterministic(*next_states):
    if len(next_states) != len(STATES):
        raise ValueError("wrong number of states")
    return kernel({y: tuple(Q(int(z == next_states[y])) for z in STATES)
                   for y in STATES})


def tv(p, q):
    p, q = tuple(map(rational, p)), tuple(map(rational, q))
    if len(p) != len(q) or not p:
        raise ValueError("incompatible measures")
    if min(p + q) < 0 or sum(p) != 1 or sum(q) != 1:
        raise ValueError("TV inputs must be probability vectors")
    return sum((abs(a - b) for a, b in zip(p, q)), Q(0)) / 2


def law(K, initial, T):
    validate_horizon(T)
    K, initial = kernel(K), initial_law(initial)
    out = {(y,): p for y, p in initial.items() if p}
    for _ in range(T):
        new = {}
        for w, p in out.items():
            for z, r in zip(STATES, K[w[-1]]):
                if r:
                    nxt = w + (z,)
                    new[nxt] = new.get(nxt, Q(0)) + p * r
        out = new
    if sum(out.values(), Q(0)) != 1:
        raise AssertionError("mass conservation failed")
    return out


def law_tv(a, b):
    keys = set(a) | set(b)
    if not keys or len({len(w) for w in keys}) != 1:
        raise ValueError("path laws must use the same horizon")
    return tv([a.get(k, Q(0)) for k in keys], [b.get(k, Q(0)) for k in keys])


def score(K, start, T, observable):
    a = law(K, {start: Q(1)}, T)
    out = Q(0)
    for w, p in a.items():
        v = rational(observable(w))
        if not Q(0) <= v <= Q(1):
            raise ValueError("not a normalized [0,1] path score")
        out += p * v
    return out


def local_bound(K, L, left_initial, right_initial, T, good, eta, visits, *, initial_budget=None):
    """Prove by exhaustive finite enumeration that all supplied premises hold.

    good(n,history) is measurable automatically on finite states. Bounds use
    the true LEFT law, for every time n<T. `visits` are user-supplied budgets,
    independently checked against the actual bad-history frequencies.
    """
    validate_horizon(T)
    K, L = kernel(K), kernel(L)
    left_initial, right_initial = initial_law(left_initial), initial_law(right_initial)
    if any(len(seq) != T for seq in (eta, visits)):
        raise ValueError("incomplete budget")
    initial_left = [left_initial.get(z, Q(0)) for z in STATES]
    initial_right = [right_initial.get(z, Q(0)) for z in STATES]
    init_error = tv(initial_left, initial_right)
    declared_initial = init_error if initial_budget is None else rational(initial_budget)
    if declared_initial < init_error:
        raise ValueError("initial TV budget underestimated")
    accumulated = Q(0)
    for n in range(T):
        en, vn = rational(eta[n]), rational(visits[n])
        if not Q(0) <= en <= Q(1) or vn < 0:
            raise ValueError("invalid declared defect or visit budget")
        for w in product(STATES, repeat=n+1):
            if checked_good(good, n, w) and tv(K[w[-1]], L[w[-1]]) > en:
                raise ValueError("good-history row defect underestimated")
        left = law(K, left_initial, n)
        bad_probability = sum((p for w, p in left.items() if not checked_good(good, n, w)), Q(0))
        if bad_probability > vn:
            raise ValueError("left-law bad visit underestimated")
        actual_average = sum((p * tv(K[w[-1]], L[w[-1]]) for w, p in left.items()), Q(0))
        if actual_average > en + vn:
            raise AssertionError("good-history integral lemma violated")
        accumulated += en + vn
    limit = min(Q(1), declared_initial + accumulated)
    actual = law_tv(law(K, left_initial, T), law(L, right_initial, T))
    if actual > limit:
        raise AssertionError("localized finite-prefix theorem violated")
    return actual, limit, init_error


def margin(values, comparison_domain):
    if not comparison_domain:
        raise ValueError("original comparison domain must be nonempty")
    return min(abs(rational(values[y][0]) - rational(values[y][1])) for y in comparison_domain)


def bound_true_reported(true, reported, domain, e0, eJ):
    e0, eJ = rational(e0), rational(eJ)
    if min(e0, eJ) < 0:
        raise ValueError("errors must be nonnegative")
    for y in domain:
        if y not in true or y not in reported:
            raise ValueError("missing output for original comparison start")
        if abs(rational(true[y][0]) - rational(reported[y][0])) > e0:
            raise ValueError("baseline report error underestimated")
        if abs(rational(true[y][1]) - rational(reported[y][1])) > eJ:
            raise ValueError("treated report error underestimated")
    genuine, observed = margin(true, domain), margin(reported, domain)
    if abs(genuine - observed) > e0 + eJ:
        raise AssertionError("original margin perturbation lemma violated")
    return genuine, observed


class LocalizedPrefixTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.K0 = deterministic(0, 0, 0)
        cls.K1 = deterministic(1, 2, 2)
        cls.L1 = deterministic(1, 0, 2)
        cls.good = staticmethod(lambda n, w: w[-1] != 1)

    def test_01_zero_horizon_point_start(self):
        for y in STATES:
            actual, b, initial = local_bound(self.K1, self.L1,
                {y: Q(1)}, {y: Q(1)}, 0, self.good, [], [])
            self.assertEqual((actual, b, initial), (0, 0, 0))

    def test_02_initial_mismatch_is_not_lost(self):
        actual, b, initial = local_bound(self.K0, self.K0,
            {0: Q(1)}, {1: Q(1)}, 0, self.good, [], [])
        self.assertEqual((actual, b, initial), (1, 1, 1))

    def test_03_one_step_good_uniform(self):
        actual, b, _ = local_bound(self.K1, self.L1,
            {0: Q(1)}, {0: Q(1)}, 1, self.good, [0], [0])
        self.assertEqual((actual, b), (0, 0))

    def test_04_treated_reaches_bad_after_first_transition(self):
        actual, b, _ = local_bound(self.K1, self.L1,
            {0: Q(1)}, {0: Q(1)}, 2, self.good, [0, 0], [0, 1])
        self.assertEqual((actual, b), (1, 1))

    def test_05_missing_treated_visit_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "visit underestimated"):
            local_bound(self.K1, self.L1, {0: Q(1)}, {0: Q(1)},
                        2, self.good, [0, 0], [0, 0])

    def test_06_baseline_only_visit_does_not_cover_treatment(self):
        true_baseline, approx_baseline = self.K0, self.K0
        zero, limit, _ = local_bound(true_baseline, approx_baseline,
                    {0: Q(1)}, {0: Q(1)}, 2, self.good, [0, 0], [0, 0])
        self.assertEqual((zero, limit), (0, 0))
        self.assertEqual(law_tv(law(self.K1, {0: Q(1)}, 2),
                                law(self.L1, {0: Q(1)}, 2)), 1)
        with self.assertRaisesRegex(ValueError, "visit underestimated"):
            local_bound(self.K1, self.L1, {0: Q(1)}, {0: Q(1)},
                        2, self.good, [0, 0], [0, 0])

    def test_07_right_process_visit_not_a_valid_substitute(self):
        # Left K reaches state 1; right L also reaches 1 at n=1,
        # so use differing initial distributions to force an asymmetric visit.
        with self.assertRaisesRegex(ValueError, "visit underestimated"):
            local_bound(self.K1, self.L1, {1: Q(1)}, {2: Q(1)},
                        1, self.good, [0], [0])

    def test_08_exact_partial_visit_saturates_bound(self):
        p = Q(2, 7)
        K = kernel({0: (1-p, p, 0), 1: (0, 0, 1), 2: (0, 0, 1)})
        L = kernel({0: (1-p, p, 0), 1: (1, 0, 0), 2: (0, 0, 1)})
        actual, b, _ = local_bound(K, L, {0: Q(1)}, {0: Q(1)},
                                 2, self.good, [0, 0], [0, p])
        self.assertEqual((actual, b), (p, p))

    def test_09_nontrivial_good_row_error(self):
        K = kernel({0: (Q(3,4), Q(1,4), 0),
                    1: (0, 1, 0), 2: (0, 0, 1)})
        L = kernel({0: (Q(2,3), Q(1,3), 0),
                    1: (0, 1, 0), 2: (0, 0, 1)})
        actual, b, _ = local_bound(K, L, {0: Q(1)}, {0: Q(1)},
                                 2, lambda n, w: True,
                                 [Q(1,12), Q(1,12)], [0, 0])
        self.assertLessEqual(actual, b)
        self.assertEqual(b, Q(1,6))

    def test_10_underdeclared_good_row_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "row defect underestimated"):
            local_bound(self.K1, self.L1, {0: Q(1)}, {0: Q(1)},
                        2, lambda n,w: True, [0, 0], [0, 0])

    def test_11_bad_complement_measured_as_bad_not_good(self):
        K = deterministic(1, 1, 1)
        L = deterministic(1, 2, 1)
        actual, b, _ = local_bound(K, L, {0: Q(1)}, {0: Q(1)},
                                 2, self.good, [0, 0], [0, 1])
        self.assertEqual(actual, 1)
        self.assertEqual(b, 1)

    def test_12_zero_defect_all_histories(self):
        for T in range(4):
            for start in STATES:
                actual, b, _ = local_bound(self.K0, self.K0,
                        {start: Q(1)}, {start: Q(1)}, T,
                        lambda n,w: True, [0]*T, [0]*T)
                self.assertEqual((actual, b), (0, 0))

    def test_13_invalid_eta(self):
        for value in (Q(-1), Q(11,10)):
            with self.assertRaisesRegex(ValueError, "invalid declared"):
                local_bound(self.K0, self.K0, {0: Q(1)}, {0: Q(1)},
                            1, self.good, [value], [0])

    def test_14_invalid_bad_visit(self):
        with self.assertRaisesRegex(ValueError, "invalid declared"):
            local_bound(self.K0, self.K0, {0: Q(1)}, {0: Q(1)},
                        1, self.good, [0], [-1])

    def test_15_incomplete_schedule(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            local_bound(self.K0, self.K0, {0: Q(1)}, {0: Q(1)},
                        2, self.good, [0], [0, 0])

    def test_16_invalid_kernel_mass(self):
        with self.assertRaisesRegex(ValueError, "stochastic row"):
            kernel({0: (Q(1,2), Q(1,3), 0), 1: (0, 1, 0), 2: (0, 0, 1)})

    def test_17_score_range_boundary(self):
        for bad in (Q(-1,2), Q(5,4)):
            with self.assertRaisesRegex(ValueError, "normalized"):
                score(self.K0, 0, 1, lambda w: bad)
        self.assertEqual(score(self.K0, 0, 1, lambda w: Q(1)), 1)
        self.assertEqual(score(self.K0, 0, 1, lambda w: Q(0)), 0)

    def test_18_score_bounded_by_tv(self):
        for T in range(4):
            a = law(self.K1, {0: Q(1)}, T)
            b = law(self.L1, {0: Q(1)}, T)
            f = lambda w: Q(1) if w[-1] == 2 else Q(0)
            difference = abs(sum((p*f(w) for w,p in a.items()), Q(0)) -
                             sum((p*f(w) for w,p in b.items()), Q(0)))
            self.assertLessEqual(difference, law_tv(a,b))

    def test_19_reporting_margin_two_independent_errors(self):
        domain = (0,1)
        true = {y: (Q(1), Q(0)) for y in domain}
        reported = {y: (Q(9,10), Q(1,10)) for y in domain}
        self.assertEqual(bound_true_reported(true, reported, domain,
                          Q(1,10), Q(1,10)), (1, Q(4,5)))
        self.assertGreater(Q(4,5) - Q(1,5), 0)
        self.assertEqual(Q(4,5) - Q(1,5), Q(3,5))

    def test_20_reporting_omission_baseline_detected(self):
        domain=(0,1)
        true={y:(Q(1),Q(0)) for y in domain}
        reported={y:(Q(9,10),Q(1,10)) for y in domain}
        with self.assertRaisesRegex(ValueError, "baseline report"):
            bound_true_reported(true,reported,domain,0,Q(1,10))

    def test_21_reporting_omission_treated_detected(self):
        domain=(0,1)
        true={y:(Q(1),Q(0)) for y in domain}
        reported={y:(Q(9,10),Q(1,10)) for y in domain}
        with self.assertRaisesRegex(ValueError, "treated report"):
            bound_true_reported(true,reported,domain,Q(1,10),0)

    def test_22_original_margin_can_be_zero_despite_positive_one_start(self):
        domain=(0,1)
        true={0:(Q(1),Q(0)),1:(Q(1),Q(1))}
        self.assertEqual(margin(true,domain),0)
        self.assertEqual(abs(true[0][0]-true[0][1]),1)

    def test_23_original_domain_change_cannot_be_captured_by_number(self):
        domain=(0,1,2)
        values={0:(Q(1),0),1:(Q(1),0),2:(Q(1),0)}
        self.assertEqual(margin(values,domain),margin(values,(0,1)))
        self.assertNotEqual(set(domain),set((0,1)))

    def test_24_no_automatic_exact_regime(self):
        # From state 0, retention 1-epsilon of {0} is never exact invariance.
        for n in (10,100,1000):
            eps=Q(1,n)
            K=kernel({0:(1-eps,eps,0),1:(0,1,0),2:(0,0,1)})
            self.assertLess(score(K,0,1,lambda w: Q(int(all(x==0 for x in w)))),1)

    def test_25_full_history_not_just_terminal(self):
        K=deterministic(1,2,2)
        L=deterministic(2,2,2)
        self.assertEqual(score(K,0,2,lambda w: Q(int(w[1]==1))),1)
        self.assertEqual(score(L,0,2,lambda w: Q(int(w[1]==1))),0)
        self.assertEqual(score(K,0,2,lambda w: Q(int(w[-1]==2))),1)
        self.assertEqual(score(L,0,2,lambda w: Q(int(w[-1]==2))),1)

    def test_26_time_zero_score_uses_initial_distribution(self):
        x=law(self.K1,{0:Q(1)},0)
        y=law(self.K1,{1:Q(1)},0)
        self.assertEqual(law_tv(x,y),1)
        self.assertEqual(sum(p*Q(w[0]==0) for w,p in x.items()),1)

    def test_27_treated_measure_uses_true_not_approximate_law(self):
        K=deterministic(1,0,2)
        L=deterministic(2,2,2)
        good = lambda n, w: True if n==0 else w[-1]==2
        self.assertEqual(sum(p for w,p in law(K,{0:Q(1)},1).items()
                             if not good(1,w)),1)
        self.assertEqual(sum(p for w,p in law(L,{0:Q(1)},1).items()
                             if not good(1,w)),0)
        with self.assertRaisesRegex(ValueError, "visit underestimated"):
            local_bound(K,L,{0:Q(1)},{0:Q(1)},2,good,
                        [1,0],[0,0])

    def test_28_margin_infimum_uses_all_starts(self):
        true={0:(Q(1),0),1:(Q(2,5),Q(1,5)),2:(Q(4,5),0)}
        self.assertEqual(margin(true,(0,1,2)),Q(1,5))
        self.assertEqual(margin(true,(0,2)),Q(4,5))

    def test_29_report_error_does_not_change_true_margin(self):
        true={0:(Q(1),0),1:(Q(1),0)}
        reported={0:(Q(9,10),Q(1,10)),1:(Q(9,10),Q(1,10))}
        k_true,k_report=bound_true_reported(true,reported,(0,1),Q(1,10),Q(1,10))
        self.assertEqual(k_true,1)
        self.assertEqual(k_report,Q(4,5))

    def test_30_empty_comparison_domain_rejected(self):
        with self.assertRaisesRegex(ValueError, "nonempty"):
            margin({},())

    def test_31_seeded_random_localized_bounds(self):
        rng = random.Random(20261018)
        for _ in range(64):
            def random_row():
                raw=[rng.randint(1,7) for _ in STATES]
                return [Q(v,sum(raw)) for v in raw]
            def random_kernel():
                return kernel({z: random_row() for z in STATES})
            K,L = random_kernel(),random_kernel()
            y=rng.choice(STATES)
            T=rng.randint(0,3)
            good=lambda n,w: w[-1] != (n % 3)
            es=[]
            vs=[]
            for n in range(T):
                es.append(max(tv(K[z],L[z]) for z in STATES if z != n % 3))
                vs.append(sum((p for w,p in law(K,{y:Q(1)},n).items()
                               if not good(n,w)),Q(0)))
            actual,limit,_=local_bound(K,L,{y:Q(1)},{y:Q(1)},T,good,es,vs)
            self.assertLessEqual(actual,limit)

    def test_33_direction_report_to_true_uses_upper_abs_arm(self):
        # |reported-true| <= e entails true >= reported-e, not the reverse.
        reported, true, e = Q(4,5), Q(3,5), Q(1,5)
        self.assertEqual(reported - true, e)
        self.assertLessEqual(reported - true, e)
        self.assertEqual(true, reported - e)
        self.assertGreater(true, 0)

    def test_34_direction_true_to_report_uses_lower_abs_arm(self):
        # |reported-true| <= e entails report >= true-e.
        reported, true, e = Q(3,5), Q(4,5), Q(1,5)
        self.assertEqual(true - reported, e)
        self.assertGreaterEqual(reported - true, -e)
        self.assertEqual(reported, true - e)
        self.assertGreater(reported, 0)

    def test_35_missing_error_makes_false_certification_possible(self):
        # Dropping BOTH model/reporting uncertainty would falsely promote
        # a positive reported gap to a positive true gap.
        domain=(0,1)
        true={z:(Q(0),Q(0)) for z in domain}
        report={z:(Q(4,5),Q(0)) for z in domain}
        self.assertEqual(margin(true,domain),0)
        self.assertGreater(margin(report,domain),0)
        with self.assertRaisesRegex(ValueError, "baseline report"):
            bound_true_reported(true,report,domain,0,0)

    def test_36_localized_budget_clamped_at_one(self):
        K,L=self.K1,self.L1
        actual,b,_=local_bound(K,L,{0:Q(1)},{0:Q(1)},3,
                  self.good,[0,0,0],[0,1,1])
        self.assertEqual(b,1)
        self.assertLessEqual(actual,b)

    def test_32_seeded_random_initial_law_mismatch(self):
        rng=random.Random(79)
        for _ in range(35):
            def random_row():
                raw=[rng.randint(1,8) for _ in STATES]
                return [Q(v,sum(raw)) for v in raw]
            K,L=kernel({z: random_row() for z in STATES}),kernel({z: random_row() for z in STATES})
            mu={z:v for z,v in zip(STATES,random_row())}
            nu={z:v for z,v in zip(STATES,random_row())}
            T=rng.randrange(0,3)
            es=[max(tv(K[z],L[z]) for z in STATES)]*T
            actual,limit,initial=local_bound(K,L,mu,nu,T,
                        lambda n,w:True,es,[0]*T)
            self.assertLessEqual(actual,limit)
            self.assertEqual(initial,tv([mu[z] for z in STATES],[nu[z] for z in STATES]))


    def test_37_unknown_initial_state_rejected_at_zero_horizon(self):
        with self.assertRaisesRegex(ValueError, "unknown state"):
            law(self.K0, {99: Q(1)}, 0)

    def test_38_float_and_bool_probabilities_rejected(self):
        for x in (0.5, True, float("nan"), float("inf")):
            with self.assertRaisesRegex(ValueError, "exact"):
                kernel({0: (x, 0, 1), 1: (0, 1, 0), 2: (0, 0, 1)})

    def test_39_invalid_or_excessive_horizon_rejected(self):
        for horizon in (True, 1.5, -1, MAX_HORIZON + 1):
            with self.assertRaisesRegex(ValueError, "horizon"):
                law(self.K0, {0: Q(1)}, horizon)

    def test_40_invalid_initial_mass_at_zero_horizon(self):
        for initial in ({}, {0: Q(1, 2)}, {0: Q(2), 1: Q(-1)}):
            with self.assertRaises(ValueError):
                law(self.K0, initial, 0)

    def test_41_declared_initial_budget_cannot_be_omitted(self):
        with self.assertRaisesRegex(ValueError, "initial TV budget"):
            local_bound(self.K0, self.K0, {0: Q(1)}, {1: Q(1)}, 0,
                        self.good, [], [], initial_budget=0)

    def test_42_tied_start_drop_is_actually_rejected(self):
        values = {z: (Q(1), Q(0)) for z in STATES}
        self.assertEqual(margin(values, STATES), margin(values, (0, 1)))
        with self.assertRaisesRegex(ValueError, "entire frozen"):
            check_domain(STATES, (0, 1))

    def test_43_duplicate_domain_rejected(self):
        with self.assertRaisesRegex(ValueError, "entire frozen"):
            check_domain(STATES, (0, 1, 2, 2))

    def test_44_non_boolean_good_predicate_rejected(self):
        with self.assertRaisesRegex(ValueError, "return bool"):
            local_bound(self.K0, self.K0, {0: Q(1)}, {0: Q(1)}, 1,
                        lambda n, w: 1, [0], [0])

    def test_45_zero_mass_bad_history_costs_zero(self):
        actual, budget, _ = local_bound(self.K0, self.K0, {0: Q(1)}, {0: Q(1)}, 3,
            lambda n, w: w[-1] == 0, [0, 0, 0], [0, 0, 0])
        self.assertEqual((actual, budget), (0, 0))

    def test_46_mixture_equals_weighted_actual_point_prefixes(self):
        initial = {0: Q(1, 3), 1: Q(1, 2), 2: Q(1, 6)}
        for T in range(4):
            mixture = {}
            for start, mass in initial.items():
                for history, p in law(self.K1, {start: Q(1)}, T).items():
                    mixture[history] = mixture.get(history, Q(0)) + mass * p
            self.assertEqual(mixture, law(self.K1, initial, T))

    def test_47_mixture_initial_tv_data_processing(self):
        mu = {0: Q(3, 4), 1: Q(1, 4)}
        nu = {0: Q(1, 2), 2: Q(1, 2)}
        expected = tv([mu.get(z, Q(0)) for z in STATES], [nu.get(z, Q(0)) for z in STATES])
        for T in range(4):
            # Full prefixes retain the initial coordinate, so here equality holds.
            self.assertEqual(law_tv(law(self.K0, mu, T), law(self.K0, nu, T)), expected)

    def test_48_mixed_initial_error_plus_local_error(self):
        nu = {0: Q(9, 10), 2: Q(1, 10)}
        actual, bound, init = local_bound(self.K1, self.L1, {0: Q(1)}, nu, 2,
            self.good, [0, 0], [0, 1])
        self.assertEqual(init, Q(1, 10))
        self.assertEqual(bound, 1)
        self.assertLessEqual(actual, bound)

    def test_49_negative_report_values_are_not_silently_clipped(self):
        true = {0: (Q(0), Q(1)), 1: (Q(0), Q(1))}
        report = {0: (Q(-1, 10), Q(11, 10)), 1: (Q(-1, 10), Q(11, 10))}
        self.assertEqual(bound_true_reported(true, report, (0, 1), Q(1, 10), Q(1, 10)),
                         (Q(1), Q(6, 5)))

    def test_50_strict_gap_boundary_does_not_certify_positivity(self):
        true = {0: (Q(0), Q(0)), 1: (Q(0), Q(0))}
        report = {0: (Q(1, 5), Q(0)), 1: (Q(1, 5), Q(0))}
        genuine, observed = bound_true_reported(true, report, (0, 1), Q(1, 5), 0)
        self.assertEqual(genuine, 0)
        self.assertEqual(observed - Q(1, 5), 0)

    def test_51_missing_comparison_output_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing output"):
            bound_true_reported({0: (0, 0)}, {0: (0, 0)}, (0, 1), 0, 0)

    def test_52_tv_does_not_accept_subprobabilities(self):
        with self.assertRaisesRegex(ValueError, "probability"):
            tv([Q(1, 2), 0], [0, Q(1, 2)])

    def test_53_extra_schedule_items_rejected(self):
        with self.assertRaisesRegex(ValueError, "incomplete"):
            local_bound(self.K0, self.K0, {0: Q(1)}, {0: Q(1)}, 0,
                        self.good, [0], [0])

    def test_54_reports_cannot_be_called_exact_model_outputs(self):
        for start in (0, 2):
            baseline = score(self.K0, start, 1, lambda w: Q(int(w[-1] == 0)))
            treated = score(self.K1, start, 1, lambda w: Q(int(w[-1] == 0)))
            self.assertEqual((baseline, treated), (Q(1), Q(0)))
            self.assertNotEqual((baseline, treated), (Q(9, 10), Q(1, 10)))

    def test_55_wellformed_wrong_kernel_not_only_row_mass_failure(self):
        wrong = deterministic(2, 2, 2)
        actual, bound, _ = local_bound(self.K1, wrong, {0: Q(1)}, {0: Q(1)}, 1,
                                      lambda n, w: True, [1], [0])
        self.assertEqual((actual, bound), (1, 1))
        with self.assertRaisesRegex(ValueError, "row defect underestimated"):
            local_bound(self.K1, wrong, {0: Q(1)}, {0: Q(1)}, 1,
                        lambda n, w: True, [0], [0])

    def test_56_bounded_majorant_not_an_arbitrary_raw_budget(self):
        eta = Q(1, 4)
        masses = (Q(1, 3), Q(2, 3))
        bounded = (eta, Q(1))
        raw = (eta, Q(1000))
        self.assertLessEqual(sum(p * d for p, d in zip(masses, bounded)), eta + masses[1])
        self.assertGreater(sum(p * d for p, d in zip(masses, raw)), eta + masses[1])

if __name__=='__main__':
    unittest.main()
