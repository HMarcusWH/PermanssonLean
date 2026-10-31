"""Independent Bellman table checker: recompose actual action kernels from P/U."""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..engines.hitting import HittingProblem,RECEIPT

_KEYS={'format','problem_semantic_identity','model_semantic_identity','joint_states',
       'horizon','goal_indices','forbidden_indices','values_by_remaining_transitions',
       'selected_actions_by_remaining_transitions','argmax_actions_by_remaining_transitions',
       'policy_class','terminal_states_for_evaluation_only',
       'baseline_alpha_optimized_over_not_assumed_equilibrium',
       'lean_status','empirical_identification','scientific_claims_verified'}


def check_bellman(problem:HittingProblem,receipt:object)->dict:
    if type(receipt) is not dict or set(receipt)!=_KEYS or receipt['format']!=RECEIPT:
        raise AppError('BELLMAN_RECEIPT','invalid or incomplete Bellman receipt')
    m=problem.world
    pairs=[(s,x) for s in m.strategic for x in m.world]
    n=len(pairs)
    if receipt['problem_semantic_identity']!=problem.semantic_id or receipt['model_semantic_identity']!=m.semantic_id():
        raise AppError('BELLMAN_RECEIPT','problem/model identity mismatch')
    for k,v in [('joint_states',[{'strategic':s,'world':x} for s,x in pairs]),
                ('horizon',problem.horizon),('goal_indices',list(problem.goal)),
                ('forbidden_indices',list(problem.forbidden)),
                ('policy_class','fully_observed_remaining_horizon_deterministic_Markov'),
                ('terminal_states_for_evaluation_only',True),
                ('baseline_alpha_optimized_over_not_assumed_equilibrium',True),
                ('lean_status','NOT_EXECUTED'),('empirical_identification','NOT_IDENTIFIED'),
                ('scientific_claims_verified',False)]:
        if type(v) is bool:
            if receipt[k] is not v:raise AppError('BELLMAN_RECEIPT',f'{k} wrong')
        elif receipt[k]!=v:raise AppError('BELLMAN_RECEIPT',f'{k} mismatch')
    all_values=receipt['values_by_remaining_transitions']
    all_choices=receipt['selected_actions_by_remaining_transitions']
    all_argmax=receipt['argmax_actions_by_remaining_transitions']
    if any(type(data) is not list or len(data)!=problem.horizon+1 for data in [all_values,all_choices,all_argmax]):
        raise AppError('BELLMAN_RECEIPT','time dimension mismatch')
    goal=set(problem.goal);forbidden=set(problem.forbidden)
    prior=None
    for t in range(problem.horizon+1):
        row=all_values[t];chosen=all_choices[t];args=all_argmax[t]
        if any(type(data) is not list or len(data)!=n for data in (row,chosen,args)):
            raise AppError('BELLMAN_RECEIPT','state dimension mismatch')
        current=[exact_result(v,probability=True) for v in row]
        for i,(s,x) in enumerate(pairs):
            if t==0 or i in goal or i in forbidden:
                expected=Fraction(int(i in goal))
                if current[i]!=expected or chosen[i] is not None or args[i]!=[]:
                    raise AppError('BELLMAN_RECEIPT','terminal/zero-step case wrong')
                continue
            if type(args[i]) is not list or type(chosen[i]) is not str:
                raise AppError('BELLMAN_RECEIPT','missing optimizing policy')
            scores=[]
            for a in m.feasible[s,x]:
                # This checker never imports the producer's controlled_transition.
                k=[m.P[s,x,a][m.world.index(xp)]*m.U[s,x,a,xp][m.strategic.index(sp)] for sp,xp in pairs]
                if sum(k,Fraction(0))!=1:raise AppError('BELLMAN_RECEIPT','P/U row is not stochastic')
                scores.append((a,sum((p*v for p,v in zip(k,prior)),Fraction(0))))
            maximum=max(v for _,v in scores)
            actual_argmax=[a for a,v in scores if v==maximum]
            if current[i]!=maximum or args[i]!=actual_argmax or chosen[i] not in actual_argmax:
                raise AppError('BELLMAN_RECEIPT','value, argmax set or selected action is not optimal')
        prior=current
    return {'format':'Permansson.App.IndependentBellmanCheck.v1','status':'PASS',
            'checked_states':n,'checked_horizons':problem.horizon+1,
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'FINITE_MARKOV_BELLMAN_NUMERIC_ONLY'}
