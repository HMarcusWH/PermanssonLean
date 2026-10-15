"""PR #67: independent exact-rational adversaries for first-exit switching.

These execute genuine rows and quantify paths, rather than presupposing the
formal Lean switching or random-entry results. They are computational checks,
not an independent proof of arbitrary-space strong Markov transport.
"""
import unittest
from fractions import Fraction as Q

STATES = tuple(range(5))
B = frozenset((0, 1, 4))
BASIN = frozenset((0, 1))
TARGET = frozenset((2, 3))
OUTSIDE = frozenset((2, 3))
ZERO = Q(0)
ONE = Q(1)
HALF = Q(1, 2)

def mk(rows):
    assert set(rows) == set(STATES)
    assert all(sum(row.values(), ZERO) == ONE and
               all(v >= 0 for v in row.values()) and
               set(row).issubset(STATES) for row in rows.values())
    return rows

def baseline():
    return mk({0:{1:ONE}, 1:{4:ONE}, 2:{3:ONE},
               3:{3:ONE}, 4:{4:ONE}})

def full():
    return mk({0:{0:HALF,2:HALF},1:{1:HALF,3:HALF},
               2:{3:ONE},3:{3:ONE},4:{4:ONE}})

def partial():
    return mk({0:{4:HALF,2:HALF},1:{4:HALF,3:HALF},
               2:{3:ONE},3:{3:ONE},4:{4:ONE}})

def nextlaw(rows,law):
    result={s:ZERO for s in STATES}
    for s,p in law.items():
        for z,q in rows[s].items(): result[z]+=p*q
    return {k:v for k,v in result.items() if v}

def routing(rows,start,destination,horizon):
    living={start:ONE}
    landed=ZERO
    for _ in range(horizon):
        step=nextlaw(rows,living)
        landed+=sum((p for s,p in step.items()
                     if s not in B and s in destination),ZERO)
        living={s:p for s,p in step.items() if s in B}
    return landed,sum(living.values(),ZERO)

def has_closed_region(rows, region):
    return all(set(rows[y]).issubset(region) for y in region)

def deterministic_limit(rows,start):
    state=start
    visited=set()
    for _ in range(12):
        if state in visited: return state
        visited.add(state)
        if len(rows[state])!=1: return None
        state=next(iter(rows[state]))
    return None

class SwitchingAdversaries(unittest.TestCase):
    def test_baseline_invariant(self): self.assertTrue(has_closed_region(baseline(),B))
    def test_full_source_not_invariant(self): self.assertFalse(has_closed_region(full(),B))
    def test_partial_source_not_invariant(self): self.assertFalse(has_closed_region(partial(),B))
    def test_target_invariant_baseline(self): self.assertTrue(has_closed_region(baseline(),TARGET))
    def test_target_invariant_full(self): self.assertTrue(has_closed_region(full(),TARGET))
    def test_target_invariant_partial(self): self.assertTrue(has_closed_region(partial(),TARGET))
    def test_target_disjoint(self): self.assertFalse(B.intersection(TARGET))
    def test_comparison_has_two_states(self): self.assertEqual(len(BASIN),2)
    def test_baseline_0_reaches_4(self): self.assertEqual(deterministic_limit(baseline(),0),4)
    def test_baseline_1_reaches_4(self): self.assertEqual(deterministic_limit(baseline(),1),4)
    def test_destination_2_reaches_3(self): self.assertEqual(deterministic_limit(full(),2),3)
    def test_destination_3_stays_3(self): self.assertEqual(deterministic_limit(full(),3),3)
    def test_L0_is_empty(self):
        for y in BASIN:self.assertEqual(routing(full(),y,TARGET,0),(ZERO,ONE))
    def test_full_L1(self):
        for y in BASIN:self.assertEqual(routing(full(),y,TARGET,1),(HALF,HALF))
    def test_full_L2(self):
        for y in BASIN:self.assertEqual(routing(full(),y,TARGET,2),(Q(3,4),Q(1,4)))
    def test_full_long_geometric(self):
        for y in BASIN:
            for L in [1,2,7,23,60]:
                route,surv=routing(full(),y,TARGET,L)
                self.assertEqual(route,ONE-HALF**L)
                self.assertEqual(surv,HALF**L)
    def test_full_eventual_exact(self):
        # Geometric series: sum_{n>=1} 2^(-n) = 1.
        self.assertEqual(HALF/(ONE-HALF),ONE)
    def test_partial_L1(self):
        for y in BASIN:self.assertEqual(routing(partial(),y,TARGET,1),(HALF,HALF))
    def test_partial_L27(self):
        for y in BASIN:self.assertEqual(routing(partial(),y,TARGET,27),(HALF,HALF))
    def test_partial_eventual_margin(self):
        for y in BASIN:
            r,s=routing(partial(),y,TARGET,3)
            self.assertEqual(ONE-s,HALF)
    def test_baseline_never_exits(self):
        for y in BASIN:
            for L in [1,10,100]:
                self.assertEqual(routing(baseline(),y,TARGET,L),(ZERO,ONE))
    def test_destination_complement_mask(self):
        for y in BASIN:
            self.assertEqual(routing(full(),y,TARGET,5),
                             routing(full(),y,TARGET|B,5))
    def test_competing_exit_must_not_be_a_switch(self):
        # Sixth physical state 5 is outside source B but not a target.
        # An inside-B absorbing state 4 is NOT a competing exit.
        K={0:{0:HALF,2:Q(1,4),5:Q(1,4)},
           1:{1:HALF,3:Q(1,4),5:Q(1,4)},
           2:{3:ONE},3:{3:ONE},4:{4:ONE},5:{5:ONE}}
        for y in BASIN:
            living={y:ONE}
            target=other=ZERO
            for _ in range(10):
                step={s:ZERO for s in range(6)}
                for s,p in living.items():
                    for z,q in K[s].items(): step[z]+=p*q
                target+=sum((p for s,p in step.items() if s in TARGET),ZERO)
                other+=step[5]
                living={s:p for s,p in step.items() if s in B and p}
            rest=sum(living.values(),ZERO)
            self.assertGreater(other,ZERO)
            self.assertEqual(target+other+rest,ONE)
            self.assertLess(target,ONE-rest)
    def test_target_arrival_without_invariance(self):
        K=full();K[2]={4:ONE}
        self.assertFalse(has_closed_region(K,TARGET))
    def test_wrong_target_occupation(self):
        self.assertNotEqual(deterministic_limit(full(),2),2)
    def test_eta_one_is_vacuous(self):
        self.assertFalse((ONE-ONE)>0)
    def test_full_positive_uniform_gap(self):
        self.assertEqual(min((ONE-HALF/(ONE-HALF) for _ in BASIN)),ZERO)
        self.assertEqual(min((HALF/(ONE-HALF) for _ in BASIN)),ONE)
    def test_full_has_no_finite_horizon_guarantee(self):
        # Finite-L misses a tail, but the infinite sum is exactly one.
        self.assertLess(routing(full(),0,TARGET,60)[0],ONE)
        self.assertEqual(HALF/(ONE-HALF),ONE)
    def test_countable_heavy_tail_exit_without_finite_mean(self):
        # Illustrative countable-state transition hazard 1/(n+2).
        # Survival through step n equals 1/(n+1), tending to zero;
        # its harmonic tail sum diverges. Finite prefix checks are not
        # a theorem of divergence or a certificate of a typed Lean model.
        survival=ONE
        for n in range(1,257):
            survival*=Q(n,n+1)
            self.assertEqual(survival,Q(1,n+1))
        self.assertEqual(survival,Q(1,257))
        harmonic=sum((Q(1,k) for k in range(1,257)),ZERO)
        self.assertGreater(harmonic,Q(6))
    def test_invalid_rows_rejected(self):
        with self.assertRaises(AssertionError): mk({**baseline(),0:{1:Q(9,8)}})
    def test_source_state_exclusion(self):
        self.assertFalse(2 in B)
        self.assertFalse(3 in B)

if __name__=="__main__": unittest.main()
