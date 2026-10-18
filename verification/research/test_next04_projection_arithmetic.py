"""NEXT-04 arithmetic adversaries for time-varying projected prefix laws.

Independent finite enumeration, not a theorem about general measurable kernels.
No Markov assumption is imposed on the visible projected process.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import unittest

FINE=tuple(product((False,True),repeat=2))
COARSE=(False,True)

def event_tv(x,y):
    return sum((abs(x.get(z,Q(0))-y.get(z,Q(0)))
                for z in set(x)|set(y)),Q(0))/2

def projected_row(row):
    ret=defaultdict(Q)
    for (visible,hidden), mass in row.items(): ret[visible]+=mass
    return dict(ret)

def push_prefix(law,step):
    out=defaultdict(Q)
    for history,p in law.items():
        for next_state,w in step(history[-1]).items():
            out[history+(next_state,)]+=p*w
    if sum(out.values(),Q(0))!=1:
        raise AssertionError('nonstochastic row')
    return dict(out)

def projected_prefix(law):
    ret=defaultdict(Q)
    for history,mass in law.items():
        ret[tuple(x[0] for x in history)]+=mass
    return dict(ret)

def fine_step(stage,eta):
    def step(state):
        visible,hidden=state
        defect=eta if not hidden else eta/2
        return {(visible,not hidden):1-defect,
                (not visible,not hidden):defect}
    return step

def coarse_step(_stage):
    return lambda visible: {visible:Q(1)}

class NonstationaryProjectionFiniteChecks(unittest.TestCase):
    def test_time_varying_initial_and_row_budget(self):
        eta=(Q(1,10),Q(1,5),Q(1,4))
        eps=Q(1,7)
        fine={( (False,False), ):Q(1)}
        coarse={(False,):1-eps,(True,):eps}
        self.assertEqual(sum(fine.values()),1)
        for t,d in enumerate(eta):
            for y in FINE:
                row=fine_step(t,d)(y)
                self.assertEqual(sum(row.values(),Q(0)),1)
                self.assertLessEqual(event_tv(projected_row(row),coarse_step(t)(y[0])),d)
            fine=push_prefix(fine,fine_step(t,d))
            coarse=push_prefix(coarse,coarse_step(t))
        error=event_tv(projected_prefix(fine),coarse)
        retained=(1-eps)
        for e in eta:retained*=1-e
        self.assertEqual(1-retained,Q(94,175))
        self.assertLessEqual(error,1-retained)
        self.assertGreater(error,0)

    def test_violating_projected_markov_assumption_is_detectable(self):
        # Same visible state, different hidden state: different next-visible law.
        left=projected_row(fine_step(0,Q(1,5))((False,False)))
        right=projected_row(fine_step(0,Q(1,5))((False,True)))
        self.assertNotEqual(left,right)
        self.assertEqual(event_tv(left,right),Q(1,10))

    def test_zero_kernel_defect_does_not_delete_initial_mismatch(self):
        eps=Q(1,7)
        fine={((False,False),):Q(1)}
        coarse={(False,):1-eps,(True,):eps}
        for t in range(3):
            fine=push_prefix(fine,fine_step(t,Q(0)))
            coarse=push_prefix(coarse,coarse_step(t))
            self.assertEqual(event_tv(projected_prefix(fine),coarse),eps)

    def test_unit_defect_allows_total_prefix_separation(self):
        fine={((False,False),):Q(1)}
        coarse={(False,):Q(1)}
        fine=push_prefix(fine,lambda s:{(not s[0],not s[1]):Q(1)})
        coarse=push_prefix(coarse,coarse_step(0))
        self.assertEqual(event_tv(projected_prefix(fine),coarse),1)

    def test_repeated_tiny_leaks_do_not_justify_exact_invariance(self):
        eta=Q(1,100)
        survival=[(1-eta)**h for h in (1,2,3,10,100)]
        self.assertTrue(all(Q(0)<v<1 for v in survival))
        self.assertEqual(sum((eta*(1-eta)**k for k in range(100)),Q(0)),
                         1-(1-eta)**100)
        # Exact all-time survival is ZERO as (1-eta)^n -> 0; this script
        # checks finite arithmetic only and makes no infinite theorem claim.

if __name__=='__main__':unittest.main()
