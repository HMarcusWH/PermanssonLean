"""NEXT-03 independent finite arithmetic/adversarial fixture checks.

No synthetic proof is represented as a Lean certificate. Actual compiler
mutation checks are in test_next03_stochastic_lean.py.
"""
from collections import defaultdict
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
TABLES=ROOT/'research/paper_closures/spec/certificates/x1_exact_tables.json'

def tv(a,b):
    states=set(a)|set(b)
    return sum((abs(a.get(s,Q(0))-b.get(s,Q(0))) for s in states),Q(0))/2

def markov_update(law,transition):
    next_law=defaultdict(Q)
    for state,pr in law.items():
        for nxt,p in transition(state).items():
            assert Q(0)<=p<=Q(1)
            next_law[nxt]+=pr*p
    assert sum(next_law.values(),Q(0))==1
    return dict(next_law)

class Next03FiniteAdversaries(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=json.loads(TABLES.read_text(encoding='utf-8'))

    def test_x1_stochastic_wrong_world_row_is_a_real_false_claim(self):
        m=[[Q(x) for x in row] for row in self.data['models']['E/baseline']['matrix']]
        self.assertEqual((len(m),{len(x) for x in m}),(18,{18}))
        self.assertTrue(all(sum(row,Q(0))==1 for row in m))
        before=list(m[2])
        self.assertEqual(before[2:4],[Q(3,4),Q(1,4)])
        mutant=[row[:] for row in m]
        mutant[2][2],mutant[2][3]=Q(1,2),Q(1,2)
        self.assertTrue(all(sum(row,Q(0))==1 for row in mutant))
        self.assertTrue(all(Q(0)<=x<=1 for row in mutant for x in row))
        self.assertEqual(mutant[2][2],Q(1,2))
        self.assertNotEqual(mutant[2][2],m[2][2])
        self.assertEqual(mutant[0],m[0])
        self.assertEqual(mutant[3:],m[3:])
        # This attacks the model-to-literal equality, not input stochasticity.

    def test_x1_tied_margin_retains_entire_original_comparison_domain(self):
        r=self.data['margins']['E/action']['rows']
        domain={tuple(x['state']) for x in r}
        declared={(p,q,1) for p in range(3) for q in range(3)}
        self.assertEqual(domain,declared)
        self.assertEqual(len(domain),9)
        effect={tuple(x['state']):Q(x['absolute_effect']) for x in r}
        self.assertEqual(set(effect.values()),{Q(271,800)})
        missing=(0,0,1)
        dropped=domain-{missing}
        self.assertEqual(min(effect[x] for x in dropped), min(effect.values()))
        self.assertNotEqual(dropped,domain)
        self.assertNotIn(missing,dropped)
        # Numerically identical minima do NOT certify the original B1 quantifier.

    def test_true_dependent_three_stage_product_saturates_bound(self):
        defects=(Q(1,10),Q(1,5),Q(1,4))
        baseline={True:Q(1)}
        intervention={True:Q(1)}
        for delta in defects:
            baseline=markov_update(baseline,lambda alive:{alive:Q(1)})
            intervention=markov_update(intervention,lambda alive,delta=delta:
                {True:1-delta,False:delta} if alive else {False:Q(1)})
        bound=1
        for delta in defects: bound*=1-delta
        bound=1-bound
        self.assertEqual(intervention,{True:Q(27,50),False:Q(23,50)})
        self.assertEqual(tv(baseline,intervention),Q(23,50))
        self.assertEqual(bound,Q(23,50))
        self.assertLess(bound,sum(defects))
        # Second-stage unconditional failure probability is (.9)*(.2), not .2;
        # the stages are history-dependent, not independent error events.
        self.assertEqual(Q(9,10)*Q(1,5),Q(9,50))

    def test_equal_key_marginals_different_marked_action_coupling(self):
        # Keys are first coordinates, actions second. Both marginals for the key
        # are 50/50 while the action-marked joint laws are mutually singular.
        base={(False,False):Q(1,2),(True,True):Q(1,2)}
        changed={(False,True):Q(1,2),(True,False):Q(1,2)}
        def projection(law):
            q=defaultdict(Q)
            for (key,action),p in law.items():q[key]+=p
            return dict(q)
        self.assertEqual(projection(base),projection(changed))
        self.assertEqual(tv(projection(base),projection(changed)),0)
        self.assertEqual(tv(base,changed),1)
        self.assertEqual({p for p in base.values()}, {Q(1,2)})

    def test_asymmetric_swap_must_transport_private_and_common_update(self):
        # This is a fully specified deterministic four-coordinate transport
        # adversary; NOT a theorem about all measurable F1 games.
        def original(c,p1,p2,x,a1,a2):
            xnext = bool((a1 and not x) or (p2 and a2))
            cnext = bool((not c and a1) or (c and not a2))
            p1next=bool(p1 ^ a1 ^ c)
            p2next=bool(p2 ^ a2 ^ (not c))
            return (cnext,p1next,p2next,xnext)
        def swapped_correct(c,p2,p1,x,a2,a1):
            c0,p10,p20,x0=original(c,p1,p2,x,a1,a2)
            return (c0,p20,p10,x0)
        def swapped_wrong(c,p2,p1,x,a2,a1):
            c0,p10,p20,x0=original(c,p1,p2,x,a2,a1)
            return (c0,p20,p10,x0)
        witnesses=[]
        for c,p1,p2,x,a1,a2 in itertools.product([False,True],repeat=6):
            expected=original(c,p1,p2,x,a1,a2)
            transported=swapped_correct(c,p2,p1,x,a2,a1)
            self.assertEqual(transported,(expected[0],expected[2],expected[1],expected[3]))
            if swapped_wrong(c,p2,p1,x,a2,a1)!=transported:
                witnesses.append((c,p1,p2,x,a1,a2))
        self.assertTrue(witnesses)
        self.assertEqual(len(list(itertools.product([False,True],repeat=6))),64)

    def test_initial_shift_remains_at_zero_transition_horizon(self):
        self.assertEqual(tv({False:Q(1)},{True:Q(1)}),Q(1))
        self.assertEqual(sum((),Q(0)),0)

if __name__=='__main__':unittest.main()
