#!/usr/bin/env python3
"""Independent arithmetic crosschecks against stated finite model assumptions.

This script does NOT compile Lean or certify an original source theorem.
These are finite exact rational observations only, using mathematical
expressions restated separately from the repository's test helpers.
"""
from fractions import Fraction as Q
import json

def expect_equal(actual, expected, label):
    if actual != expected:
        raise AssertionError(f'{label}: observed {actual}, expected {expected}')
    return {'label': label, 'fraction': str(actual), 'pass': True}

result=[]
# Q-05: beta=1/3, s'=False (baseline), s'=True (treatment);
# world-next=action. Discounted score=(1-beta)sum_t beta^t x_t.
beta=Q(1,3)
normal=1-beta
base_fine_false=beta * Q(1,10)
base_fine_true=normal + base_fine_false
# First treatment step samples action p=.7, later fixed s=True has p=.8.
trt_fine_false=normal*beta*Q(7,10)+beta**2*Q(4,5)
trt_fine_true=normal+trt_fine_false
base_coarse_false=beta*Q(3,20)
base_coarse_true=normal+base_coarse_false
trt_coarse_false=beta*Q(3,4)
trt_coarse_true=normal+trt_coarse_false
for label,val,expected in [
    ('Q05 fine baseline false',base_fine_false,Q(1,30)),
    ('Q05 fine baseline true',base_fine_true,Q(7,10)),
    ('Q05 fine treated false',trt_fine_false,Q(11,45)),
    ('Q05 fine treated true',trt_fine_true,Q(41,45)),
    ('Q05 coarse baseline false',base_coarse_false,Q(1,20)),
    ('Q05 coarse baseline true',base_coarse_true,Q(43,60)),
    ('Q05 coarse treated false',trt_coarse_false,Q(1,4)),
    ('Q05 coarse treated true',trt_coarse_true,Q(11,12)),
    ('Q05 fine calculated margin',trt_fine_false-base_fine_false,Q(19,90)),
    ('Q05 coarse calculated margin',trt_coarse_false-base_coarse_false,Q(1,5)),
    ('Q05 exact margin discrepancy',abs((trt_fine_false-base_fine_false)-(trt_coarse_false-base_coarse_false)),Q(1,90)),
    ('Q05 discounted retention envelope',beta*Q(1,20)/(1-beta+beta*Q(1,20)),Q(1,41)),
]:result.append(expect_equal(val,expected,label))
# D-09's two absorbing *physical* classes: this is not the distinct
# phase-aware vs deterministic phase-blind optimization fixture.
F=lambda p: 1-abs(p-Q(2,3))
mixture=(F(Q(0))+F(Q(1)))/2
barycenter=F(Q(1,2))
result.append(expect_equal(mixture,Q(1,2),'D09 expected nonlinear class score'))
result.append(expect_equal(barycenter,Q(5,6),'D09 nonlinear score of barycenter'))
result.append(expect_equal(barycenter-mixture,Q(1,3),'D09 aggregation gap'))
# D-05 two-stage committed model identity is different from rectangular
# reselection across stages, with P(first true)=.1, P(second true)=.9
result.append(expect_equal(Q(1,10)*Q(9,10),Q(9,100),'D05 committed two-stage selected atom'))
result.append(expect_equal(Q(1,10)*Q(1,10),Q(1,100),'D05 rectangular reselection selected atom'))
# Addendum: derive D-06 from complete finite joint paths of the declared model.
# A single initial flag is false; actions are equally likely; the update writes
# the realized action; the physical readout is the same Unit value in both cases.
prior = {False: Q(1), True: Q(0)}
policy = {False: Q(1, 2), True: Q(1, 2)}
paths = {}
for before, p_before in prior.items():
    for action, p_action in policy.items():
        for after in (False, True):
            p_update = Q(int(after == action))
            readout = ()
            paths[(before, action, after, readout)] = p_before * p_action * p_update
result.append(expect_equal(sum(prior.values(), Q(0)), Q(1), 'D06 single initial law normalized'))
result.append(expect_equal(sum(paths.values(), Q(0)), Q(1), 'D06 complete chronological joint law normalized'))
for action in (False, True):
    denominator = sum((mass for (_, a, _, _) , mass in paths.items() if a == action), Q(0))
    numerator = sum((mass for (_, a, after, _) , mass in paths.items() if a == action and after), Q(0))
    if denominator <= 0:
        raise AssertionError('D06 reachable history must have strictly positive mass')
    posterior = numerator / denominator
    result.append(expect_equal(denominator, Q(1, 2), f'D06 action {action} actual history mass'))
    result.append(expect_equal(posterior, Q(int(action)), f'D06 action {action} posterior true from Bayes ratio'))
readout_laws = {a: {r: sum((m for (_, aa, _, rr), m in paths.items() if aa == a and rr == r), Q(0)) / sum((m for (_, aa, _, _), m in paths.items() if aa == a), Q(0)) for r in ((),)} for a in (False, True)}
if readout_laws[False] != readout_laws[True]:
    raise AssertionError('D06 physical readout laws differ')
result.append(expect_equal(readout_laws[False][()], Q(1), 'D06 same deterministic physical readout under both histories'))
# Count the bound check explicitly; the historical script ran it outside its20 result records.
gap = abs((trt_fine_false-base_fine_false)-(trt_coarse_false-base_coarse_false))
budget = 2 * beta * Q(1, 20) / (1 - beta + beta * Q(1, 20))
if gap > budget:
    raise AssertionError('Q05 exact arithmetic gap exceeds the two-sided bound')
result.append({'label': 'Q05 calculated exact gap bounded by two-sided retention budget', 'fraction': str(gap), 'bound': str(budget), 'pass': True})
print(json.dumps({'format':'Permansson.CERT.FractionCrosscheckAddendum.v1','scope':'Independent finite arithmetic only; no canonical Lean identity or certification asserted','checks':len(result),'failures':0,'status':'PASS','observations':result},indent=2))
