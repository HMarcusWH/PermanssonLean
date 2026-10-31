"""Independent original-kernel and exhaustive-policy checker for one-step belief control.

No import from the numerical belief producer; re-derives every posterior,
realized next-world law, legal observation-only policy, and optimality by
independently enumerating all bounded observation-contingent action maps.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from itertools import product
import re
from ..errors import AppError
from ..finite_world import parse_finite_world,exact_ratio
from ..identity import rational_text,semantic_identity,canonical_bytes

TOKEN=re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')
REQUEST='Permansson.App.OneStepBeliefRequest.v1'
RECEIPT='Permansson.App.OneStepBeliefReceipt.v1'


def _same(actual,expected,where='belief receipt'):
    if type(actual) is not type(expected):
        raise AppError('BELIEF_RECEIPT',where+' wrong type')
    if type(expected) is dict:
        if set(actual)!=set(expected):raise AppError('BELIEF_RECEIPT',where+' altered field set')
        for key in expected:_same(actual[key],expected[key],where+'.'+key)
    elif type(expected) is list:
        if len(actual)!=len(expected):raise AppError('BELIEF_RECEIPT',where+' altered list length')
        for i,(a,b) in enumerate(zip(actual,expected)):_same(a,b,where+'['+str(i)+']')
    elif actual!=expected:
        raise AppError('BELIEF_RECEIPT',where+' altered value')


def check_belief(raw:object,receipt:object)->dict:
    if type(raw) is not dict or set(raw)!={'format','model','prior','observations','likelihoods','terminal_rewards'} or raw['format']!=REQUEST:
        raise AppError('BELIEF_INPUT','unexpected input contract')
    m=parse_finite_world(raw['model'])
    if len(m.strategic)!=1 or len(m.world)>3 or len(m.actions)>3:
        raise AppError('BELIEF_SCOPE','too large or strategically non-singleton')
    os=raw['observations']
    if type(os) is not list or not 1<=len(os)<=3 or any(type(o) is not str or not TOKEN.fullmatch(o) for o in os) or len(set(os))!=len(os):
        raise AppError('BELIEF_INPUT','wrong observation alphabet')
    def vector(field,value_key,prob=False):
        supplied=raw[field]
        if type(supplied) is not list or len(supplied)!=len(m.world):raise AppError('BELIEF_INPUT','incomplete '+field)
        result={}
        for item in supplied:
            if type(item) is not dict or set(item)!={'x',value_key} or type(item['x']) is not str or item['x'] not in m.world or item['x'] in result:
                raise AppError('BELIEF_INPUT','duplicate/unknown '+field+' state')
            result[item['x']]=exact_ratio(item[value_key],probability=prob)
        return tuple(result[x] for x in m.world)
    prior=vector('prior','mass',True)
    if sum(prior,Fraction(0))!=1:raise AppError('BELIEF_INPUT','initial hidden prior not probability')
    rewards=vector('terminal_rewards','value')
    Q={}
    lr=raw['likelihoods']
    if type(lr) is not list or len(lr)!=len(m.world):raise AppError('BELIEF_INPUT','likelihood matrix incomplete')
    for entry in lr:
        if type(entry) is not dict or set(entry)!={'x','weights'} or type(entry['x']) is not str or entry['x'] not in m.world or entry['x'] in Q or type(entry['weights']) is not dict or set(entry['weights'])!=set(os):
            raise AppError('BELIEF_INPUT','likelihood row has missing or foreign observation')
        vals=tuple(exact_ratio(entry['weights'][o],probability=True) for o in os)
        if sum(vals,Fraction(0))!=1:raise AppError('BELIEF_INPUT','likelihood row not stochastic')
        Q[entry['x']]=vals
    matrix=tuple(Q[x] for x in m.world)
    def rat(v):
        if max(v.numerator.bit_length(),v.denominator.bit_length())>8192:raise AppError('BELIEF_RESOURCE','precision budget exceeded')
        return rational_text(v)
    s=m.strategic[0]
    possible={};observation_rows=[]
    for j,o in enumerate(os):
        initial_obs=tuple(prior[i]*matrix[i][j] for i in range(len(m.world)))
        obs_prob=sum(initial_obs,Fraction(0))
        if obs_prob==0:
            observation_rows.append({'observation':o,'observation_probability':'0','posterior':None,
                'available_actions':[],'action_scores':{},'tied_max_actions':[],
                'selected_action':None,'unreachable':True})
            continue
        # Same action must be legal for every hidden state consistent with this observation.
        support=[i for i in range(len(m.world)) if initial_obs[i]>0]
        common=[a for a in m.actions if all(a in m.feasible[s,m.world[i]] for i in support)]
        if not common:raise AppError('BELIEF_COMMON_MENU','no jointly legal action after reachable observation')
        vals={}
        for a in common:
            total=Fraction(0)
            for i,x in enumerate(m.world):
                if initial_obs[i]==0:continue
                for k,xp in enumerate(m.world):
                    transition=m.P[s,x,a][k]*m.U[s,x,a,xp][0]
                    total+=initial_obs[i]*transition*rewards[k]
            vals[a]=total
        highest=max(vals.values());ties=[a for a in common if vals[a]==highest]
        possible[o]=common
        observation_rows.append({'observation':o,'observation_probability':rat(obs_prob),
            'posterior':[rat(x/obs_prob) for x in initial_obs],
            'available_actions':common,'action_scores':{a:rat(vals[a]) for a in common},
            'tied_max_actions':ties,'selected_action':None,'unreachable':False})
    if type(receipt) is not dict or type(receipt.get('policy')) is not list or len(receipt['policy'])!=len(os):
        raise AppError('BELIEF_RECEIPT','missing full observation-only policy')
    chosen={}
    for j,o in enumerate(os):
        item=receipt['policy'][j]
        if type(item) is not dict or type(item.get('selected_action')) not in (str,type(None)):
            raise AppError('BELIEF_RECEIPT','wrong chosen-action scalar type')
        action=item['selected_action']; row=observation_rows[j]
        if o in possible:
            if action not in row['tied_max_actions']:
                raise AppError('BELIEF_RECEIPT','policy not an optimal legal shared-observation action')
            chosen[o]=action
        elif action is not None:
            raise AppError('BELIEF_RECEIPT','unreachable observation cannot receive an inferred action')
        row['selected_action']=action
    # Enumerate the full bounded cartesian product of observation-based deterministic policies.
    active=list(possible)
    total_policies=1
    for o in active:total_policies*=len(possible[o])
    if total_policies>27:raise AppError('BELIEF_RESOURCE','policy enumeration above contract')
    all_rewards=[]
    def reward_for(policy):
        score=Fraction(0)
        for j,o in enumerate(os):
            if o not in policy:continue
            a=policy[o]
            for i,x in enumerate(m.world):
                if prior[i]*matrix[i][j]==0:continue
                for k,xp in enumerate(m.world):
                    score+=prior[i]*matrix[i][j]*m.P[s,x,a][k]*m.U[s,x,a,xp][0]*rewards[k]
        return score
    for choices in product(*(possible[o] for o in active)):
        all_rewards.append(reward_for(dict(zip(active,choices))))
    if not all_rewards or reward_for(chosen)!=max(all_rewards):
        raise AppError('BELIEF_RECEIPT','chosen policy does not maximize complete bounded policy class')
    law=[]
    for k,xp in enumerate(m.world):
        mass=Fraction(0)
        for j,o in enumerate(os):
            if o not in chosen:continue
            a=chosen[o]
            for i,x in enumerate(m.world):
                if prior[i]*matrix[i][j]==0:continue
                mass+=prior[i]*matrix[i][j]*m.P[s,x,a][k]*m.U[s,x,a,xp][0]
        law.append(mass)
    if sum(law,Fraction(0))!=1:raise AppError('BELIEF_RECEIPT','chosen actual next world law not stochastic')
    result=reward_for(chosen)
    blind_actions=[a for a in m.actions if all(a in m.feasible[s,m.world[i]] for i,p in enumerate(prior) if p>0)]
    blind=max((sum((prior[i]*m.P[s,x,a][k]*m.U[s,x,a,xp][0]*rewards[k]
                          for i,x in enumerate(m.world) if prior[i]>0 for k,xp in enumerate(m.world)),Fraction(0)) for a in blind_actions),default=None)
    if blind is not None and result<blind:raise AppError('BELIEF_RECEIPT','reported observation policy below blind best')
    expected={'format':RECEIPT,'request_identity':semantic_identity('one-step-observation-control',raw),
              'source_model_identity':m.semantic_id(),
              'hidden_world_states':list(m.world),'observation_labels':list(os),
              'prior':[rat(x) for x in prior],
              'likelihood_matrix':[[rat(v) for v in row] for row in matrix],
              'terminal_rewards':[rat(x) for x in rewards],
              'policy':observation_rows,'next_world_law':[rat(v) for v in law],
              'optimal_expected_terminal_reward':rat(result),
              'best_blind_policy_reward':rat(blind) if blind is not None else None,
              'value_of_observation':rat(result-blind) if blind is not None else None,
              'scope':'one_transition_observe_then_act_fully_enumerated_deterministic_observation_policies',
              'unreachable_observations':'never_normalized_or_promoted_to_state_evidence',
              'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
              'scientific_claims_verified':False}
    _same(receipt,expected)
    return {'format':'Permansson.App.IndependentOneStepBeliefCheck.v1','status':'PASS',
            'original_source_bound':True,'bounded_policies_exhaustively_checked':total_policies,
            'observation_action_scope':'SHARED_ACTION_FOR_ALL_SUPPORTED_HIDDEN_STATES',
            'posterior_status':'EXACT_WHEN_REACHABLE_UNDEFINED_WHEN_UNREACHABLE',
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','scientific_claims_verified':False}
