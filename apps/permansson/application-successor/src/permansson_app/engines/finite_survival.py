"""Exact killed-kernel finite-survival calculation on fully reified α/P/U input.

This is a finite-horizon diagnostic. It is not exact invariance, an EGR/PR
classification, a QSD theorem or an empirical probability-of-collapse forecast.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..finite_world import parse_finite_world,compare_strategic_intervention,induced_kernel
from ..identity import rational_text,semantic_identity

FORMAT='Permansson.App.FiniteSurvivalComparison.v1'
RECEIPT='Permansson.App.FiniteSurvivalReceipt.v1'


def parse_comparison(raw:object):
    if type(raw) is not dict or set(raw)!={'format','baseline','treated','target','region','comparison_states','horizon'} or raw['format']!=FORMAT:
        raise AppError('SURVIVAL_FORMAT','complete fixed finite-survival comparison required')
    baseline=parse_finite_world(raw['baseline'])
    treated=parse_finite_world(raw['treated'])
    compare_strategic_intervention(baseline,treated,raw['target'])
    states=tuple((s,x) for s in baseline.strategic for x in baseline.world)
    if len(states)>12:raise AppError('SURVIVAL_LIMIT','full numeric survival profile supports <=12 joint states')
    def parse_subset(value,name):
        if type(value) is not list or not value or len(value)>len(states):
            raise AppError('SURVIVAL_REGION',f'{name} must be nonempty finite state list')
        out=[]
        for item in value:
            if type(item) is not list or len(item)!=2 or any(type(t) is not str for t in item):
                raise AppError('SURVIVAL_REGION',f'{name} must use exact [strategic,world] state pairs')
            st=tuple(item)
            if st not in states or st in out:raise AppError('SURVIVAL_REGION','foreign or duplicate state')
            out.append(st)
        return tuple(out)
    region=parse_subset(raw['region'],'region')
    selected=parse_subset(raw['comparison_states'],'comparison_states')
    if not set(selected)<=set(region):
        raise AppError('SURVIVAL_REGION','full comparison set must lie within declared region')
    horizon=raw['horizon']
    if type(horizon) is not int or not 0<=horizon<=32:
        raise AppError('SURVIVAL_LIMIT','exact finite horizon must be 0..32')
    return baseline,treated,states,region,selected,horizon


def _survival_table(K,states,region,horizon:int):
    """q_n(i)=P_i(X_0..X_n ∈ B), including inside-B test at time zero."""
    target=set(region)
    rows=[tuple(Fraction(int(s in target)) for s in states)]
    for _ in range(horizon):
        last=rows[-1]
        row=tuple(sum((K[i][j]*last[j] for j,sp in enumerate(states) if sp in target),Fraction(0))
                  if state in target else Fraction(0) for i,state in enumerate(states))
        if any(x<0 or x>1 for x in row):raise AppError('SURVIVAL_ARITHMETIC','invalid exact killed kernel')
        if any(max(x.numerator.bit_length(),x.denominator.bit_length())>8192 for x in row):
            raise AppError('SURVIVAL_RESOURCE','rational denominator exploded beyond run budget')
        rows.append(row)
    return tuple(rows)


def propose_finite_survival(raw:object)->dict:
    b,t,states,region,selected,horizon=parse_comparison(raw)
    qb=_survival_table(induced_kernel(b),states,region,horizon)
    qt=_survival_table(induced_kernel(t),states,region,horizon)
    last_b,last_t=qb[-1],qt[-1]
    differences=[last_b[states.index(s)]-last_t[states.index(s)] for s in selected]
    gap=min(map(abs,differences))
    receipt={
        'format':RECEIPT,'baseline_id':b.semantic_id(),'treated_id':t.semantic_id(),
        'comparison_identity':semantic_identity('finite-survival-comparison',raw),
        'states':[list(s) for s in states],
        'region':[list(s) for s in region],
        'comparison_states':[list(s) for s in selected],
        'horizon':horizon,
        'baseline_survival':[[rational_text(x) for x in row] for row in qb],
        'treated_survival':[[rational_text(x) for x in row] for row in qt],
        'minimum_abs_effect':rational_text(gap),
        'finite_effect_signs':['positive' if d>0 else 'negative' if d<0 else 'zero' for d in differences],
        'finite_scope_status':'ALL_DECLARED_STARTS_SEPARATED' if gap>0 else 'NO_UNIFORM_FINITE_SEPARATION',
        'exact_GR_or_PR_certified':False,'lean_status':'NOT_EXECUTED'
    }
    return receipt
