"""Finite first-exit routing and eventual never-exit mass for exact rational chains.

Time-zero starts are required to lie inside the declared region. An exit occurs
at the first transition to its complement; it is not a normalized conditional
law. Finite survival does not establish GR invariance or basin persistence.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld,induced_kernel
from ..identity import rational_text,semantic_identity
from .occupation import bottom_classes
from .rational_linear import solve_unique

FORMAT='Permansson.App.FiniteRegion.v1'

@dataclass(frozen=True)
class Region:
    joint_indices:tuple[int,...]
    horizon:int
    semantic_id:dict


def parse_region(raw:object,model:FiniteWorld)->Region:
    if type(raw) is not dict or set(raw)!={'format','joint_states','horizon'} or raw['format']!=FORMAT:
        raise AppError('REGION_INPUT','unsupported finite region format')
    if type(raw['horizon']) is not int or not 0<=raw['horizon']<=64:
        raise AppError('REGION_INPUT','horizon must be a bounded nonnegative integer')
    pairs=[(s,x) for s in model.strategic for x in model.world]
    v=raw['joint_states']
    if type(v) is not list or not v or len(v)>len(pairs):
        raise AppError('REGION_INPUT','region must be a nonempty set of joint states')
    selected=[]
    for item in v:
        if type(item) is not dict or set(item)!={'strategic','world'} or type(item['strategic']) is not str or type(item['world']) is not str:
            raise AppError('REGION_INPUT','region state has invalid type')
        pair=(item['strategic'],item['world'])
        if pair not in pairs or pairs.index(pair) in selected:
            raise AppError('REGION_INPUT','region contains foreign/duplicate joint state')
        selected.append(pairs.index(pair))
    selected=tuple(sorted(selected))
    canonical={'format':FORMAT,'joint_states':[{'strategic':pairs[i][0],'world':pairs[i][1]} for i in selected],
               'horizon':raw['horizon'],'model_semantic_identity':model.semantic_id()}
    return Region(selected,raw['horizon'],semantic_identity('finite-region',canonical))


def _eventual_exit(K, region):
    n=len(K);B=set(region); outside=[i for i in range(n) if i not in B]
    inside_closed={i for c in bottom_classes(K) if set(c)<=B for i in c}
    transient=[i for i in region if i not in inside_closed]
    probabilities={i:[Fraction(0) for _ in outside] for i in region}
    if transient:
        A=[[Fraction(int(i==j))-K[i][j] for j in transient] for i in transient]
        for col,destination in enumerate(outside):
            sol=solve_unique(A,[K[i][destination] for i in transient])
            for i,p in zip(transient,sol):probabilities[i][col]=p
    return outside, probabilities


def compute_exit(model:FiniteWorld,region:Region)->dict:
    K=induced_kernel(model)
    B=region.joint_indices;Bset=set(B);n=len(K)
    outside,ever=_eventual_exit(K,B)
    finite=[]
    for start in B:
        p=[Fraction(int(i==start)) for i in B]
        survival=[Fraction(1)];exits=[]
        for step in range(region.horizon):
            exitrow=[sum((p[k]*K[i][j] for k,i in enumerate(B)),Fraction(0)) for j in outside]
            new=[sum((p[k]*K[i][j] for k,i in enumerate(B)),Fraction(0)) for j in B]
            exits.append(exitrow);p=new
            survival.append(sum(p,Fraction(0)))
        probs=ever[start]
        if any(q<0 or q>1 for q in probs) or sum(probs)>1:
            raise AppError('EXIT_ERROR','invalid eventual exit probabilities')
        finite.append({'start_index':start,
                       'survival_through':[rational_text(v) for v in survival],
                       'first_exit_by_step_and_destination':[[rational_text(v) for v in row] for row in exits],
                       'eventual_exit_by_destination':[rational_text(v) for v in probs],
                       'never_exit':rational_text(Fraction(1)-sum(probs,Fraction(0)))})
    return {'format':'Permansson.App.FiniteExitReceipt.v1',
            'model_semantic_identity':model.semantic_id(),
            'region_semantic_identity':region.semantic_id,'region_indices':list(B),
            'outside_indices':outside,'horizon':region.horizon,
            'initial_inside_only':True,
            'rows':finite,'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
