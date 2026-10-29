"""Fully observed exact finite-horizon hitting Bellman values and admissible feedback.

The target is terminal for *evaluation only*: underlying P/U are not changed.
The policy chooses permitted controls by remaining horizon and observed state.
This profile corresponds numerically to the D1-B Bellman recurrence, but no
new data-to-Lean correspondence proof is claimed here.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld,parse_finite_world
from ..identity import rational_text,semantic_identity

FORMAT='Permansson.App.FiniteHittingControl.v1'
RECEIPT='Permansson.App.FiniteBellmanReceipt.v1'
MAX_STATES=12
MAX_HORIZON=24
MAX_OUTPUT_BITS=8192


@dataclass(frozen=True)
class HittingProblem:
    world:FiniteWorld
    goal:tuple[int,...]
    forbidden:tuple[int,...]
    horizon:int
    semantic_id:dict


def parse_hitting_problem(raw:object)->HittingProblem:
    if type(raw) is not dict or set(raw)!={'format','model','goal','forbidden','horizon'} or raw['format']!=FORMAT:
        raise AppError('BELLMAN_INPUT','invalid finite hitting problem envelope')
    model=parse_finite_world(raw['model'])
    pairs=[(s,x) for s in model.strategic for x in model.world]
    if len(pairs)>MAX_STATES or type(raw['horizon']) is not int or not 0<=raw['horizon']<=MAX_HORIZON:
        raise AppError('BELLMAN_SCOPE','only <=12 joint states and <=24 transitions supported')
    def read_subset(key):
        v=raw[key]
        if type(v) is not list or len(v)>len(pairs):
            raise AppError('BELLMAN_INPUT',f'{key} must be an array of declared joint states')
        indices=[]
        for item in v:
            if type(item) is not dict or set(item)!={'strategic','world'} or any(type(item[k]) is not str for k in item):
                raise AppError('BELLMAN_INPUT','state identifier must have exact fields')
            pair=(item['strategic'],item['world'])
            if pair not in pairs or pairs.index(pair) in indices:
                raise AppError('BELLMAN_INPUT','duplicate or unknown state')
            indices.append(pairs.index(pair))
        return tuple(sorted(indices))
    goal,forbidden=read_subset('goal'),read_subset('forbidden')
    if set(goal)&set(forbidden):
        raise AppError('BELLMAN_INPUT','goal and forbidden must be disjoint')
    canon={'format':FORMAT,'model_semantic_identity':model.semantic_id(),'horizon':raw['horizon'],
           'goal_indices':list(goal),'forbidden_indices':list(forbidden)}
    return HittingProblem(model,goal,forbidden,raw['horizon'],semantic_identity('finite-hitting-control',canon))


def controlled_transition(world:FiniteWorld,s:str,x:str,a:str,pairs:tuple)->tuple[Fraction,...]:
    """Action-conditioned α/P/U row with fixed P and U, irrespective of baseline α."""
    return tuple(world.P[s,x,a][world.world.index(xp)]*world.U[s,x,a,xp][world.strategic.index(sp)] for sp,xp in pairs)


def propose_bellman(problem:HittingProblem)->dict:
    model=problem.world
    pairs=tuple((s,x) for s in model.strategic for x in model.world)
    n=len(pairs)
    goal=set(problem.goal); forbidden=set(problem.forbidden)
    value=[[Fraction(int(i in goal)) for i in range(n)]]
    choices=[[None]*n]
    argmax=[[[] for _ in pairs]]
    for remaining in range(1,problem.horizon+1):
        previous=value[-1]
        row=[];selected=[];possible=[]
        for index,(s,x) in enumerate(pairs):
            if index in goal:
                row.append(Fraction(1));selected.append(None);possible.append([])
            elif index in forbidden:
                row.append(Fraction(0));selected.append(None);possible.append([])
            else:
                outcomes=[]
                for a in model.feasible[s,x]:
                    transition=controlled_transition(model,s,x,a,pairs)
                    score=sum((prob*prior for prob,prior in zip(transition,previous)),Fraction(0))
                    outcomes.append((a,score))
                maximum=max(q for _,q in outcomes)
                maximizing=[a for a,score in outcomes if score==maximum]
                row.append(maximum);selected.append(maximizing[0]);possible.append(maximizing)
        if any(not 0<=r<=1 or max(r.numerator.bit_length(),r.denominator.bit_length())>MAX_OUTPUT_BITS for r in row):
            raise AppError('BELLMAN_RESOURCE','finite rational value exceeds bounds')
        value.append(row);choices.append(selected);argmax.append(possible)
    return {'format':RECEIPT,'problem_semantic_identity':problem.semantic_id,
            'model_semantic_identity':model.semantic_id(),
            'joint_states':[{'strategic':s,'world':x} for s,x in pairs],
            'horizon':problem.horizon,
            'goal_indices':list(problem.goal),'forbidden_indices':list(problem.forbidden),
            'values_by_remaining_transitions':[[rational_text(v) for v in row] for row in value],
            'selected_actions_by_remaining_transitions':choices,
            'argmax_actions_by_remaining_transitions':argmax,
            'policy_class':'fully_observed_remaining_horizon_deterministic_Markov',
            'terminal_states_for_evaluation_only':True,
            'baseline_alpha_optimized_over_not_assumed_equilibrium':True,
            'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
