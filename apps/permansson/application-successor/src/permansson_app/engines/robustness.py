"""Exact finite-horizon kernel/initial-law total-variation error certificate.

Bound for a shared-state path event: TV(mu0,nu0) + horizon * max_y
TV(K(y,.),L(y,.)), clipped at one.  This is a *finite-horizon*
comparison of two actual typed α/P/U chains, not a long-run GR/PR theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld, parse_finite_world, induced_kernel, exact_ratio
from ..identity import rational_text, semantic_identity

FORMAT='Permansson.App.FinitePerturbation.v1'
RECEIPT='Permansson.App.FinitePerturbationReceipt.v1'
MAX_STATES=12
MAX_HORIZON=32
MAX_BITS=8192

@dataclass(frozen=True)
class PerturbationProblem:
    baseline:FiniteWorld
    alternative:FiniteWorld
    region:tuple[int,...]
    initial_baseline:tuple[Fraction,...]
    initial_alternative:tuple[Fraction,...]
    horizon:int
    identity:dict


def parse_perturbation(raw:object)->PerturbationProblem:
    if type(raw) is not dict or set(raw)!={'format','baseline','alternative','region','initial_baseline','initial_alternative','horizon'} or raw['format']!=FORMAT:
        raise AppError('PERTURBATION_INPUT','complete typed versioned error profile required')
    b=parse_finite_world(raw['baseline']);a=parse_finite_world(raw['alternative'])
    if (b.strategic,b.world,b.actions)!=(a.strategic,a.world,a.actions):
        raise AppError('PERTURBATION_MODELS','state/action inventories must agree for error comparison')
    pairs=[(s,x) for s in b.strategic for x in b.world]
    n=len(pairs)
    if n>MAX_STATES or type(raw['horizon']) is not int or not 0<=raw['horizon']<=MAX_HORIZON:
        raise AppError('PERTURBATION_SCOPE','at most 12 joint states and 32 transitions')
    region=raw['region']
    if type(region) is not list or not region or len(region)>n:
        raise AppError('PERTURBATION_REGION','nonempty declared region required')
    indices=set()
    for state in region:
        if type(state) is not list or len(state)!=2 or any(type(t) is not str for t in state):
            raise AppError('PERTURBATION_REGION','region must use exact [strategic,world] pairs')
        key=tuple(state)
        if key not in pairs or pairs.index(key) in indices:
            raise AppError('PERTURBATION_REGION','duplicate or unknown region state')
        indices.add(pairs.index(key))
    def law(key):
        values=raw[key]
        if type(values) is not list or len(values)!=n:
            raise AppError('PERTURBATION_LAW',f'{key} must have one weight per canonical joint state')
        result=tuple(exact_ratio(v,probability=True) for v in values)
        if sum(result,Fraction(0))!=1:raise AppError('PERTURBATION_LAW','initial law not normalized')
        return result
    mu,nu=law('initial_baseline'),law('initial_alternative')
    normal={'format':FORMAT,'baseline_model':b.semantic_id(),'alternative_model':a.semantic_id(),
            'region_indices':sorted(indices),'initial_baseline':list(map(rational_text,mu)),
            'initial_alternative':list(map(rational_text,nu)),'horizon':raw['horizon']}
    return PerturbationProblem(b,a,tuple(sorted(indices)),mu,nu,raw['horizon'],semantic_identity('finite-kernel-perturbation',normal))


def _survival_rows(K,region,h):
    n=len(K);B=set(region)
    table=[tuple(Fraction(int(i in B)) for i in range(n))]
    for _ in range(h):
        previous=table[-1]
        next_row=tuple(sum((K[i][j]*previous[j] for j in B),Fraction(0)) if i in B else Fraction(0) for i in range(n))
        if any(max(v.numerator.bit_length(),v.denominator.bit_length())>MAX_BITS for v in next_row):
            raise AppError('PERTURBATION_RESOURCE','survival rational exceeded precision cap')
        table.append(next_row)
    return table


def propose_perturbation(problem:PerturbationProblem)->dict:
    b,a=problem.baseline,problem.alternative
    K,L=induced_kernel(b),induced_kernel(a)
    n=len(K)
    row_tvs=[sum((abs(K[i][j]-L[i][j]) for j in range(n)),Fraction(0))/2 for i in range(n)]
    initial_tv=sum((abs(x-y) for x,y in zip(problem.initial_baseline,problem.initial_alternative)),Fraction(0))/2
    delta=max(row_tvs)
    bound=min(Fraction(1),initial_tv+problem.horizon*delta)
    sb,sa=_survival_rows(K,problem.region,problem.horizon),_survival_rows(L,problem.region,problem.horizon)
    pb=sum((x*y for x,y in zip(problem.initial_baseline,sb[-1])),Fraction(0))
    pa=sum((x*y for x,y in zip(problem.initial_alternative,sa[-1])),Fraction(0))
    if abs(pb-pa)>bound:raise AppError('PERTURBATION_INTERNAL','computed event difference exceeded universal path bound')
    return {'format':RECEIPT,'problem_semantic_identity':problem.identity,'baseline_model_identity':b.semantic_id(),
            'alternative_model_identity':a.semantic_id(),
            'joint_states':[{'strategic':s,'world':x} for s in b.strategic for x in b.world],
            'region_indices':list(problem.region),'horizon':problem.horizon,
            'row_total_variations':list(map(rational_text,row_tvs)),
            'maximum_row_tv':rational_text(delta),'initial_law_tv':rational_text(initial_tv),
            'bound_at_horizon':rational_text(bound),
            'baseline_survival_rows':[[rational_text(x) for x in row] for row in sb],
            'alternative_survival_rows':[[rational_text(x) for x in row] for row in sa],
            'baseline_event_probability':rational_text(pb),'alternative_event_probability':rational_text(pa),
            'observed_abs_difference':rational_text(abs(pb-pa)),
            'scope':'FINITE_PATH_EVENT_TV_COUPLING_BOUND_ONLY',
            'no_long_run_claim':True,'scientific_claims_verified':False,
            'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED'}
