"""Bounded exact rational finite-horizon observation-history policy trees.

At each time t the current joint state (s,x) generates observation o from Q(o|x),
then the controller chooses a jointly legal action using only its observation
history. The physical transition P(x'|s,x,a) occurs before the strategic update
U(s'|s,x,a,x'). Rewards are paid only on the resulting final joint state.

Numeric computations are not Lean replay, independent certification, identified
empirical dynamics, or unrestricted partially observed policy optimization.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from fractions import Fraction
import re
from ..errors import AppError
from ..finite_world import FiniteWorld, parse_finite_world, exact_ratio
from ..identity import rational_text, semantic_identity

REQUEST = 'Permansson.App.FiniteBeliefTreeRequest.v1'
RECEIPT = 'Permansson.App.FiniteBeliefTreeReceipt.v1'
TOKEN = re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')
MAX_BITS = 8192


@dataclass(frozen=True)
class TreeProblem:
    model: FiniteWorld
    states: tuple[tuple[str, str], ...]
    horizon: int
    prior: tuple[Fraction, ...]
    observations: tuple[str, ...]
    likelihoods: tuple[tuple[Fraction, ...], ...]
    terminal_rewards: tuple[Fraction, ...]
    identity: dict


def parse_belief_tree(raw: object) -> TreeProblem:
    keys = {'format', 'model', 'horizon', 'prior', 'observations', 'likelihoods', 'terminal_rewards'}
    if type(raw) is not dict or set(raw) != keys or raw['format'] != REQUEST:
        raise AppError('BELIEF_TREE_INPUT', 'unexpected belief-tree request version/fields')
    h = raw['horizon']
    if type(h) is not int or not 1 <= h <= 3:
        raise AppError('BELIEF_TREE_SCOPE', 'horizon must be an integer 1..3')
    m = parse_finite_world(raw['model'])
    if len(m.strategic)>2 or len(m.world)>3 or len(m.actions)>3:
        raise AppError('BELIEF_TREE_SCOPE', 'at most 2 strategic, 3 world and 3 action states')
    states = tuple((s, x) for s in m.strategic for x in m.world)
    observations = raw['observations']
    if (type(observations) is not list or not 1<=len(observations)<=3 or
        any(type(o) is not str or not TOKEN.fullmatch(o) for o in observations) or
        len(set(observations)) != len(observations)):
        raise AppError('BELIEF_TREE_INPUT', 'observation alphabet must contain 1..3 unique tokens')

    def joint_rows(key, field, probability=False):
        entries=raw[key]
        if type(entries) is not list or len(entries)!=len(states):
            raise AppError('BELIEF_TREE_INPUT',key+' must cover every joint state')
        seen={}
        for row in entries:
            if (type(row) is not dict or set(row)!={'s','x',field} or
                type(row['s']) is not str or type(row['x']) is not str):
                raise AppError('BELIEF_TREE_INPUT','invalid '+key+' row')
            pair=(row['s'],row['x'])
            if pair not in states or pair in seen:
                raise AppError('BELIEF_TREE_INPUT','duplicate or foreign joint state in '+key)
            seen[pair]=exact_ratio(row[field],probability=probability)
        return tuple(seen[p] for p in states)

    prior=joint_rows('prior','mass',True)
    if sum(prior,Fraction(0))!=1:
        raise AppError('BELIEF_TREE_INPUT','initial joint-state prior not stochastic')
    rewards=joint_rows('terminal_rewards','value')
    supplied=raw['likelihoods']
    if type(supplied) is not list or len(supplied)!=len(m.world):
        raise AppError('BELIEF_TREE_INPUT','likelihood matrix must cover all world states')
    likelihoods={}
    for row in supplied:
        if (type(row) is not dict or set(row)!={'x','weights'} or type(row['x']) is not str or
            row['x'] not in m.world or row['x'] in likelihoods or
            type(row['weights']) is not dict or set(row['weights'])!=set(observations)):
            raise AppError('BELIEF_TREE_INPUT','incomplete or duplicate likelihood row')
        weights=tuple(exact_ratio(row['weights'][o],probability=True) for o in observations)
        if sum(weights,Fraction(0))!=1:
            raise AppError('BELIEF_TREE_INPUT','likelihood weights must sum to 1')
        likelihoods[row['x']]=weights
    return TreeProblem(m,states,h,prior,tuple(observations),tuple(likelihoods[x] for x in m.world),rewards,
                       semantic_identity('finite-observation-history-tree',raw))


def _text(v: Fraction) -> str:
    if max(v.numerator.bit_length(),v.denominator.bit_length()) > MAX_BITS:
        raise AppError('BELIEF_TREE_RESOURCE','exact rational output exceeds 8192 bits')
    return rational_text(v)


def _step(p: TreeProblem, belief: tuple[Fraction,...], a: str) -> tuple[Fraction,...]:
    m=p.model
    result=[]
    for sp,xp in p.states:
        mass=Fraction(0)
        for index,(s,x) in enumerate(p.states):
            if belief[index]==0:continue
            if a not in m.feasible[s,x]:
                raise AppError('BELIEF_TREE_COMMON_MENU','hidden-infeasible controller action')
            mass+=belief[index]*m.P[s,x,a][m.world.index(xp)]*m.U[s,x,a,xp][m.strategic.index(sp)]
        result.append(mass)
    if sum(result,Fraction(0))!=1:
        raise AppError('BELIEF_TREE_INTERNAL','joint alpha/P/U next law not normalized')
    return tuple(result)


def _observe(p: TreeProblem, belief:tuple[Fraction,...], obs_index:int):
    weights=tuple(b*p.likelihoods[p.model.world.index(x)][obs_index] for b,(_,x) in zip(belief,p.states))
    mass=sum(weights,Fraction(0))
    return mass,(tuple(x/mass for x in weights) if mass else None)


def _common(p:TreeProblem, posterior:tuple[Fraction,...]):
    return tuple(a for a in p.model.actions if all(a in p.model.feasible[s,x]
                       for (s,x),b in zip(p.states,posterior) if b))


def _solver(p:TreeProblem):
    """Optimal value from a belief, or None when no complete legal policy exists.

    An action that is legal now but leads to a reachable posterior with no
    common legal action has no complete continuation; it is excluded from the
    maximization instead of aborting it.
    """
    @lru_cache(maxsize=8192)
    def best(belief:tuple[Fraction,...], left:int)->Fraction|None:
        if left==0:
            return sum((v*r for v,r in zip(belief,p.terminal_rewards)),Fraction(0))
        result=Fraction(0)
        for j in range(len(p.observations)):
            mass,posterior=_observe(p,belief,j)
            if not mass:continue
            values=[v for v in (best(_step(p,posterior,a),left-1) for a in _common(p,posterior)) if v is not None]
            if not values:
                return None
            result+=mass*max(values)
        return result
    return best


def _blind(p:TreeProblem):
    """Best fixed, non-observation-contingent legal action sequence (or no such sequence)."""
    @lru_cache(maxsize=8192)
    def solve(b:tuple[Fraction,...],h:int):
        if not h:return sum((v*r for v,r in zip(b,p.terminal_rewards)),Fraction(0))
        available=_common(p,b)
        scores=[solve(_step(p,b,a),h-1) for a in available]
        scores=[v for v in scores if v is not None]
        return max(scores) if scores else None
    return solve(p.prior,p.horizon)


def _make_tree(p:TreeProblem, belief:tuple[Fraction,...],h:int,best):
    rows=[]
    for j,o in enumerate(p.observations):
        mass,posterior=_observe(p,belief,j)
        if not mass:
            rows.append({'observation':o,'observation_probability':'0',
                'posterior':None,'available_actions':[],'action_scores':{},
                'tied_max_actions':[],'selected_action':None,'next_prior':None,
                'next_tree':None,'terminal_joint_law':None,'unreachable':True})
            continue
        actions=_common(p,posterior)
        # available_actions: legal now; action_scores: only those with a complete
        # legal continuation (the others are never part of an admitted policy).
        scores={a:v for a in actions if (v:=best(_step(p,posterior,a),h-1)) is not None}
        if not scores:raise AppError('BELIEF_TREE_INTERNAL','selected branch has no complete continuation')
        highest=max(scores.values())
        ties=[a for a in actions if a in scores and scores[a]==highest]
        selected=ties[0]
        after=_step(p,posterior,selected)
        rows.append({'observation':o,'observation_probability':_text(mass),
            'posterior':[_text(v) for v in posterior],
            'available_actions':list(actions),'action_scores':{a:_text(scores[a]) for a in actions if a in scores},
            'tied_max_actions':ties,'selected_action':selected,
            'next_prior':[_text(v) for v in after],
            'next_tree':_make_tree(p,after,h-1,best) if h>1 else None,
            'terminal_joint_law':[_text(v) for v in after] if h==1 else None,
            'unreachable':False})
    return {'remaining_transitions':h,'prior':[_text(v) for v in belief],'observations':rows}


def _law(p:TreeProblem,tree:dict)->tuple[Fraction,...]:
    """Forward realization of the selected observation-history tree."""
    totals=[Fraction(0) for _ in p.states]
    for row in tree['observations']:
        if row['unreachable']:continue
        weight=Fraction(row['observation_probability'])
        nxt=(tuple(Fraction(v) for v in row['terminal_joint_law']) if row['terminal_joint_law'] is not None
             else _law(p,row['next_tree']))
        for i,mass in enumerate(nxt):totals[i]+=weight*mass
    return tuple(totals)


def propose_belief_tree(raw:object)->dict:
    p=parse_belief_tree(raw)
    best=_solver(p)
    optimum=best(p.prior,p.horizon)
    if optimum is None:
        raise AppError('BELIEF_TREE_COMMON_MENU','no complete legal observation-history policy exists')
    tree=_make_tree(p,p.prior,p.horizon,best)
    law=_law(p,tree)
    realized=sum((b*r for b,r in zip(law,p.terminal_rewards)),Fraction(0))
    if realized!=optimum or sum(law,Fraction(0))!=1:
        raise AppError('BELIEF_TREE_INTERNAL','policy law/value disagreement')
    blind=_blind(p)
    if blind is not None and optimum < blind:
        raise AppError('BELIEF_TREE_INTERNAL','observation strategy worse than a legal blind policy')
    return {'format':RECEIPT,'request_identity':p.identity,'source_model_identity':p.model.semantic_id(),
        'horizon':p.horizon,
        'hidden_joint_states':[{'s':s,'x':x} for s,x in p.states],
        'observation_labels':list(p.observations),
        'initial_joint_prior':[_text(v) for v in p.prior],
        'likelihood_matrix':[[_text(v) for v in row] for row in p.likelihoods],
        'terminal_rewards':[_text(v) for v in p.terminal_rewards],
        'optimal_policy_tree':tree,'terminal_joint_law':[_text(v) for v in law],
        'optimal_expected_terminal_reward':_text(optimum),
        'best_blind_action_sequence_reward':_text(blind) if blind is not None else None,
        'value_of_observation_history':_text(optimum-blind) if blind is not None else None,
        'scope':'bounded_observe_act_then_P_then_U_history_policies_terminal_reward',
        'source_alpha_policy_status':'BOUND_SOURCE_ONLY_NOT_REPLACEMENT_CONTROLLER',
        'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False}
