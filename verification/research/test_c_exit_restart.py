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

def direct_restarted_cylinder(K, start, n, D, future):
    """Enumerate full paths, filter the first exit and future-cylinder."""
    length=n+len(future)
    current={(start,):ONE}
    for _ in range(length):
        nxt={}
        for history,p in current.items():
            for z,q in K[history[-1]].items():
                w=history+(z,)
                nxt[w]=nxt.get(w,ZERO)+p*q
        current=nxt
    return sum((p for w,p in current.items()
                if all(w[k] in SOURCE for k in range(n+1))
                and w[n+1] in (set(D)-SOURCE)
                and tuple(w[n+1:n+2+len(future)])[:len(future)+1]==tuple(future)),
               ZERO)

def routed_future_cylinder(K,start,n,D,future):
    if not future:
        return sum((v for z,v in arrival_submeasure(K,start,n).items()
                    if z in (set(D)-SOURCE)),ZERO)
    return sum((q*path_weight(K,future)
                for z,q in arrival_submeasure(K,start,n).items()
                if z in (set(D)-SOURCE) and z==future[0]),ZERO)

def future_prob(K,z,word):
    return path_weight(K,(z,)+tuple(word))

def direct(K,start,n,D,tail):
    """Explicit enumeration from time 0 through the requested tail."""
    horizon = (n+1) + (len(tail)-1)
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
        for K in (switched(),partial(),baseline()):
            for y in (0,1):
                for n in (0,1,2,3):
                    for D in ({2,3},{2},{3},set(STATES)):
                        for tail in ((2,),(2,3),(2,3,3),(3,3),(3,3,3)):
                            with self.subTest(start=y,n=n,dest=D,tail=tail):
                                self.assertEqual(direct(K,y,n,D,tail),mixture(K,y,n,D,tail))
    def test_independent_tail_words_not_just_endpoint(self):
        self.assertEqual(mixture(switched(),0,0,{2,3},(2,3,3)),HALF)
        self.assertEqual(mixture(switched(),0,0,{2,3},(2,2,2)),ZERO)

if __name__ == "__main__": unittest.main()
