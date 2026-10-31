"""Independent exact forward-path and unnormalized-mass checker for belief trees.

The checker never imports the belief-tree producer. It calculates the action
values with unnormalized joint-state flows, verifies every admitted action at
every observation history, and independently accumulates terminal trajectories
from the actual P/U transition tables and the receipt's chosen policy.
"""
from __future__ import annotations
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
import re
from ..errors import AppError
from ..finite_world import parse_finite_world, exact_ratio
from ..identity import rational_text, semantic_identity, canonical_bytes

REQUEST='Permansson.App.FiniteBeliefTreeRequest.v1'
RECEIPT='Permansson.App.FiniteBeliefTreeReceipt.v1'
TOKEN=re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')


def _same(a,b,name='receipt'):
    if type(a) is not type(b):raise AppError('BELIEF_TREE_RECEIPT',name+' changed type')
    if type(b) is dict:
        if set(a)!=set(b):raise AppError('BELIEF_TREE_RECEIPT',name+' changed keys')
        for k in b:_same(a[k],b[k],name+'.'+str(k))
    elif type(b) is list:
        if len(a)!=len(b):raise AppError('BELIEF_TREE_RECEIPT',name+' changed length')
        for i,(x,y) in enumerate(zip(a,b)):_same(x,y,name+'['+str(i)+']')
    elif a!=b:raise AppError('BELIEF_TREE_RECEIPT',name+' changed value')


def check_belief_tree(raw:object,receipt:object)->dict:
    if (type(raw) is not dict or set(raw)!={'format','model','horizon','prior','observations','likelihoods','terminal_rewards'}
        or raw['format']!=REQUEST):
        raise AppError('BELIEF_TREE_INPUT','unsupported original request')
    m=parse_finite_world(raw['model']);h=raw['horizon']
    if type(h) is not int or not 1<=h<=3 or len(m.strategic)>2 or len(m.world)>3 or len(m.actions)>3:
        raise AppError('BELIEF_TREE_SCOPE','unqualified horizon/model dimensions')
    states=tuple((s,x) for s in m.strategic for x in m.world)
    obs=raw['observations']
    if (type(obs) is not list or not 1<=len(obs)<=3 or len(set(obs))!=len(obs)
        or any(type(o) is not str or not TOKEN.fullmatch(o) for o in obs)):
        raise AppError('BELIEF_TREE_INPUT','invalid observation alphabet')

    def state_rows(name,field,probability=False):
        rows=raw[name]
        if type(rows) is not list or len(rows)!=len(states):
            raise AppError('BELIEF_TREE_INPUT',name+' rows do not cover joint state')
        values={}
        for row in rows:
            if (type(row) is not dict or set(row)!={'s','x',field} or
                type(row['s']) is not str or type(row['x']) is not str or
                (row['s'],row['x']) not in states or (row['s'],row['x']) in values):
                raise AppError('BELIEF_TREE_INPUT',name+' duplicate or malformed')
            values[row['s'],row['x']]=exact_ratio(row[field],probability=probability)
        return tuple(values[p] for p in states)

    prior=state_rows('prior','mass',True)
    if sum(prior,Fraction(0))!=1:raise AppError('BELIEF_TREE_INPUT','bad initial probability mass')
    rewards=state_rows('terminal_rewards','value')
    likelihoods={}
    qrows=raw['likelihoods']
    if type(qrows) is not list or len(qrows)!=len(m.world):
        raise AppError('BELIEF_TREE_INPUT','incomplete observation kernel')
    for row in qrows:
        if (type(row) is not dict or set(row)!={'x','weights'} or type(row['x']) is not str or
            row['x'] not in m.world or row['x'] in likelihoods or type(row['weights']) is not dict
            or set(row['weights'])!=set(obs)):
            raise AppError('BELIEF_TREE_INPUT','invalid observation-kernel row')
        vals=tuple(exact_ratio(row['weights'][o],probability=True) for o in obs)
        if sum(vals,Fraction(0))!=1:raise AppError('BELIEF_TREE_INPUT','observation kernel not stochastic')
        likelihoods[row['x']]=vals
    Q=tuple(likelihoods[x] for x in m.world)
    xidx={x:i for i,x in enumerate(m.world)}
    sidx={s:i for i,s in enumerate(m.strategic)}
    def rat(v):
        if max(v.numerator.bit_length(),v.denominator.bit_length())>8192:
            raise AppError('BELIEF_TREE_RESOURCE','rational checker precision exhausted')
        return rational_text(v)

    def flow(weights,a):
        """Unnormalized post-transition state mass, no producer code or posterior division."""
        out=[Fraction(0) for _ in states]
        for i,(s,x) in enumerate(states):
            if weights[i]==0:continue
            if a not in m.feasible[s,x]:
                raise AppError('BELIEF_TREE_COMMON_MENU','action not feasible on hidden support')
            for j,(sp,xp) in enumerate(states):
                out[j]+=weights[i]*m.P[s,x,a][xidx[xp]]*m.U[s,x,a,xp][sidx[sp]]
        if sum(out,Fraction(0))!=sum(weights,Fraction(0)):
            raise AppError('BELIEF_TREE_INTERNAL','flow loses probability mass')
        return tuple(out)

    def allowed(weights):
        return [a for a in m.actions if all(a in m.feasible[s,x]
                    for w,(s,x) in zip(weights,states) if w)]

    def observe(weights,j):
        return tuple(weight*Q[xidx[x]][j] for weight,(_,x) in zip(weights,states))

    # Direct recursive maximization of UNNORMALIZED flow values. This is a
    # different representation from the producer's normalized Bayesian V recursion.
    # None: no complete legal policy continues from these weights. A legal action
    # without one is excluded from the maximization, as in the producer.
    @lru_cache(maxsize=8192)
    def exhaustive_value(weights,remaining):
        if remaining==0:
            return sum((w*r for w,r in zip(weights,rewards)),Fraction(0))
        total=Fraction(0)
        for j in range(len(obs)):
            joint=observe(weights,j)
            if not any(joint):continue
            values=[v for v in (exhaustive_value(flow(joint,a),remaining-1) for a in allowed(joint)) if v is not None]
            if not values:
                return None
            total+=max(values)
        return total

    if type(receipt) is not dict or type(receipt.get('optimal_policy_tree')) is not dict:
        raise AppError('BELIEF_TREE_RECEIPT','missing policy tree')
    branches_checked=0
    def verify_tree(tree,weights,remaining):
        nonlocal branches_checked
        if (type(tree) is not dict or type(tree.get('observations')) is not list
            or len(tree['observations'])!=len(obs)):
            raise AppError('BELIEF_TREE_RECEIPT','malformed observation tree')
        rows=[]
        realized=[Fraction(0) for _ in states]
        for j,o in enumerate(obs):
            original_row=tree['observations'][j]
            if type(original_row) is not dict:raise AppError('BELIEF_TREE_RECEIPT','malformed row')
            part=observe(weights,j)
            mass=sum(part,Fraction(0))
            if not mass:
                expected={'observation':o,'observation_probability':'0','posterior':None,
                    'available_actions':[],'action_scores':{},'tied_max_actions':[],
                    'selected_action':None,'next_prior':None,'next_tree':None,
                    'terminal_joint_law':None,'unreachable':True}
                rows.append(expected)
                _same(original_row,expected,'observation '+o)
                continue
            posterior=tuple(x/mass for x in part)
            legal=allowed(part)
            vals={a:v/mass for a in legal if (v:=exhaustive_value(flow(part,a),remaining-1)) is not None}
            if not vals:raise AppError('BELIEF_TREE_COMMON_MENU','no complete legal continuation on the selected tree')
            branches_checked+=len(vals)
            maximum=max(vals.values());ties=[a for a in legal if a in vals and vals[a]==maximum]
            chosen=original_row.get('selected_action')
            if type(chosen) is not str or chosen not in ties:
                raise AppError('BELIEF_TREE_RECEIPT','chosen action not maximizing or not legal')
            next_weights=flow(part,chosen)
            next_prior=tuple(v/mass for v in next_weights)
            if remaining==1:
                child=None
                end=next_prior
                tail=[rat(v) for v in end]
            else:
                child=original_row.get('next_tree')
                end=verify_tree(child,next_prior,remaining-1)
                tail=None
            for i,v in enumerate(end):realized[i]+=mass*v
            expected={'observation':o,'observation_probability':rat(mass),
                'posterior':[rat(x) for x in posterior],
                'available_actions':legal,'action_scores':{a:rat(v) for a,v in vals.items()},
                'tied_max_actions':ties,'selected_action':chosen,
                'next_prior':[rat(v) for v in next_prior],
                'next_tree':child,'terminal_joint_law':tail,'unreachable':False}
            # Comparison is strict except nested child validated separately.
            _same(original_row,expected,'observation '+o)
            rows.append(expected)
        _same(tree,{'remaining_transitions':remaining,'prior':[rat(v) for v in weights],
                    'observations':rows},'policy tree')
        if sum(realized,Fraction(0))!=1:
            raise AppError('BELIEF_TREE_RECEIPT','selected tree does not conserve terminal mass')
        return tuple(realized)

    # The policy tree's actual realized future is computed directly from its
    # leaf paths; independent of the producer's output terminal-law recurrence.
    terminal=verify_tree(receipt['optimal_policy_tree'],prior,h)
    expected_reward=sum((m0*r for m0,r in zip(terminal,rewards)),Fraction(0))
    optimal=exhaustive_value(prior,h)
    if optimal is None:
        raise AppError('BELIEF_TREE_COMMON_MENU','no complete legal observation-history policy exists')
    if expected_reward!=optimal:
        raise AppError('BELIEF_TREE_RECEIPT','selected policy is not globally optimal in declared class')

    @lru_cache(maxsize=8192)
    def blind(weights,steps):
        if not steps:
            return sum((w*r for w,r in zip(weights,rewards)),Fraction(0))
        options=[blind(flow(weights,a),steps-1) for a in allowed(weights)]
        nonempty=[v for v in options if v is not None]
        return max(nonempty) if nonempty else None
    best_blind=blind(prior,h)
    if best_blind is not None and optimal<best_blind:
        raise AppError('BELIEF_TREE_RECEIPT','observed policy inferior to legal blind sequence')
    expected={'format':RECEIPT,
      'request_identity':semantic_identity('finite-observation-history-tree',raw),
      'source_model_identity':m.semantic_id(),
      'horizon':h,
      'hidden_joint_states':[{'s':s,'x':x} for s,x in states],
      'observation_labels':list(obs),
      'initial_joint_prior':[rat(v) for v in prior],
      'likelihood_matrix':[[rat(x) for x in row] for row in Q],
      'terminal_rewards':[rat(v) for v in rewards],
      'optimal_policy_tree':receipt['optimal_policy_tree'],
      'terminal_joint_law':[rat(v) for v in terminal],
      'optimal_expected_terminal_reward':rat(optimal),
      'best_blind_action_sequence_reward':rat(best_blind) if best_blind is not None else None,
      'value_of_observation_history':rat(optimal-best_blind) if best_blind is not None else None,
      'scope':'bounded_observe_act_then_P_then_U_history_policies_terminal_reward',
      'source_alpha_policy_status':'BOUND_SOURCE_ONLY_NOT_REPLACEMENT_CONTROLLER',
      'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
      'scientific_claims_verified':False}
    _same(receipt,expected)
    return {'format':'Permansson.App.IndependentBeliefTreeCheck.v1',
        'status':'PASS','policy_scope':'OBSERVATION_HISTORY_ONLY_COMMON_HIDDEN_SUPPORT_ACTION',
        'source_model_bound':True,'bounded_action_branches_checked':branches_checked,
        'unnormalized_value_subproblems_checked':exhaustive_value.cache_info().currsize,
        'terminal_law_from_actual_P_U':True,
        'unreachable_observations':'NO_POSTERIOR_OR_ACTION',
        'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
        'lean_status':'NOT_EXECUTED','scientific_claims_verified':False}
