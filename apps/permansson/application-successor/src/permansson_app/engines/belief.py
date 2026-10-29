"""Exact one-step finite Bayesian observation-conditioned control.

The policy sees only the declared observation, never the hidden world state.
This is a bounded one-transition profile, not a general POMDP/alpha-tree solver.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
import re
from ..errors import AppError
from ..finite_world import FiniteWorld,parse_finite_world,exact_ratio
from ..identity import rational_text,semantic_identity

REQUEST='Permansson.App.OneStepBeliefRequest.v1'
RECEIPT='Permansson.App.OneStepBeliefReceipt.v1'
TOKEN=re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')
MAX_BITS=8192

@dataclass(frozen=True)
class BeliefProblem:
    model:FiniteWorld
    prior:tuple[Fraction,...]
    observations:tuple[str,...]
    likelihood:tuple[tuple[Fraction,...],...]
    terminal_rewards:tuple[Fraction,...]
    identity:dict


def parse_belief(raw:object)->BeliefProblem:
    if type(raw) is not dict or set(raw)!={'format','model','prior','observations','likelihoods','terminal_rewards'} or raw['format']!=REQUEST:
        raise AppError('BELIEF_INPUT','unsupported one-step belief request or fields')
    m=parse_finite_world(raw['model'])
    if len(m.strategic)!=1 or len(m.world)>3 or len(m.actions)>3:
        raise AppError('BELIEF_SCOPE','one strategic state, at most three world states/actions')
    observations=raw['observations']
    if type(observations) is not list or not 1<=len(observations)<=3 or any(type(o) is not str or not TOKEN.fullmatch(o) for o in observations) or len(set(observations))!=len(observations):
        raise AppError('BELIEF_INPUT','must declare 1..3 unique observation labels')
    def table(key,field,probability=False):
        rows=raw[key]
        if type(rows) is not list or len(rows)!=len(m.world):
            raise AppError('BELIEF_INPUT','must supply one row per hidden world state: '+key)
        result={}
        for row in rows:
            if type(row) is not dict or set(row)!={'x',field} or type(row['x']) is not str or row['x'] not in m.world or row['x'] in result:
                raise AppError('BELIEF_INPUT','invalid or duplicate '+key+' hidden-state row')
            result[row['x']]=exact_ratio(row[field],probability=probability)
        return tuple(result[x] for x in m.world)
    prior=table('prior','mass',True)
    if sum(prior,Fraction(0))!=1:
        raise AppError('BELIEF_INPUT','hidden prior must sum to one')
    rewards=table('terminal_rewards','value')
    lines=raw['likelihoods']
    if type(lines) is not list or len(lines)!=len(m.world):
        raise AppError('BELIEF_INPUT','observation kernel must cover all hidden states')
    rows={}
    for row in lines:
        if type(row) is not dict or set(row)!={'x','weights'} or type(row['x']) is not str or row['x'] not in m.world or row['x'] in rows or type(row['weights']) is not dict or set(row['weights'])!=set(observations):
            raise AppError('BELIEF_INPUT','observation likelihood has foreign/incomplete labels')
        vals=tuple(exact_ratio(row['weights'][o],probability=True) for o in observations)
        if sum(vals,Fraction(0))!=1:
            raise AppError('BELIEF_INPUT','observation likelihood not stochastic')
        rows[row['x']]=vals
    return BeliefProblem(m,prior,tuple(observations),tuple(rows[x] for x in m.world),rewards,
                         semantic_identity('one-step-observation-control',raw))


def _exact_str(value:Fraction)->str:
    if max(value.numerator.bit_length(),value.denominator.bit_length())>MAX_BITS:
        raise AppError('BELIEF_RESOURCE','exact output exceeds bounded rational precision')
    return rational_text(value)


def propose_belief(raw:object)->dict:
    p=parse_belief(raw);m=p.model;s=m.strategic[0]
    policy=[];chosen={}
    for j,o in enumerate(p.observations):
        weights=tuple(p.prior[i]*p.likelihood[i][j] for i in range(len(m.world)))
        mass=sum(weights,Fraction(0))
        if not mass:
            policy.append({'observation':o,'observation_probability':'0','posterior':None,
                'available_actions':[],'action_scores':{},'tied_max_actions':[],
                'selected_action':None,'unreachable':True})
            continue
        supported=[i for i,v in enumerate(weights) if v]
        allowed=[a for a in m.actions if all(a in m.feasible[s,m.world[i]] for i in supported)]
        if not allowed:
            raise AppError('BELIEF_COMMON_MENU','reachable observation has no common legal action')
        scores={}
        for a in allowed:
            scores[a]=sum((weights[i]*sum((pout*rw for pout,rw in zip(m.P[s,x,a],p.terminal_rewards)),Fraction(0))
                         for i,x in enumerate(m.world) if weights[i]>0),Fraction(0))
        best=max(scores.values())
        ties=[a for a in allowed if scores[a]==best]
        chosen[o]=ties[0]
        policy.append({'observation':o,'observation_probability':_exact_str(mass),
            'posterior':[_exact_str(v/mass) for v in weights],
            'available_actions':allowed,'action_scores':{a:_exact_str(scores[a]) for a in allowed},
            'tied_max_actions':ties,'selected_action':ties[0],'unreachable':False})
    law=[]
    for xp in m.world:
        k=m.world.index(xp)
        law.append(sum((p.prior[i]*p.likelihood[i][j]*m.P[s,x,chosen[o]][k]
                    for i,x in enumerate(m.world) for j,o in enumerate(p.observations)
                    if o in chosen and p.prior[i]*p.likelihood[i][j]>0),Fraction(0)))
    if sum(law,Fraction(0))!=1:
        raise AppError('BELIEF_INTERNAL','observed policy induced law not normalized')
    result=sum((v*r for v,r in zip(law,p.terminal_rewards)),Fraction(0))
    blind_options=[a for a in m.actions if all(a in m.feasible[s,m.world[i]] for i,v in enumerate(p.prior) if v)]
    if blind_options:
        blind=max(sum((p.prior[i]*sum((z*r for z,r in zip(m.P[s,x,a],p.terminal_rewards)),Fraction(0)) for i,x in enumerate(m.world) if p.prior[i]>0),Fraction(0)) for a in blind_options)
    else:blind=None
    if blind is not None and result<blind:raise AppError('BELIEF_INTERNAL','observation policy underperforms admissible blind policy')
    return {'format':RECEIPT,'request_identity':p.identity,'source_model_identity':m.semantic_id(),
            'hidden_world_states':list(m.world),'observation_labels':list(p.observations),
            'prior':[_exact_str(x) for x in p.prior],
            'likelihood_matrix':[[_exact_str(v) for v in row] for row in p.likelihood],
            'terminal_rewards':[_exact_str(x) for x in p.terminal_rewards],
            'policy':policy,'next_world_law':[_exact_str(v) for v in law],
            'optimal_expected_terminal_reward':_exact_str(result),
            'best_blind_policy_reward':_exact_str(blind) if blind is not None else None,
            'value_of_observation':_exact_str(result-blind) if blind is not None else None,
            'scope':'one_transition_observe_then_act_fully_enumerated_deterministic_observation_policies',
            'unreachable_observations':'never_normalized_or_promoted_to_state_evidence',
            'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
