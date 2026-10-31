"""Bounded exact Bellman DP for retryable, first-ever and danger-avoid residence.

All transitions use the physical P/U and choose admissible controls for the
actual fully observed augmented monitor state. This is a numeric result only.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld
from ..identity import rational_text
from .monitors import parse_residence,ResidenceProblem
from .hitting import controlled_transition

RECEIPT='Permansson.App.FiniteResidenceReceipt.v1'
MAX_OUTPUT_BITS=8192


def solve_residence(raw:object)->dict:
    p=parse_residence(raw)
    m=p.model
    pairs=tuple((s,x) for s in m.strategic for x in m.world)
    statuses=p.monitor_states
    n=len(pairs);q=len(statuses);H=p.horizon
    values=[None]*(H+1); selected=[None]*(H+1); ties=[None]*(H+1)
    values[H]=[[Fraction(int(status=='success')) for status in statuses] for _ in pairs]
    selected[H]=[[None]*q for _ in pairs]
    ties[H]=[[[] for _ in statuses] for _ in pairs]
    for t in range(H-1,-1,-1):
        current=[];current_action=[];current_argmax=[]
        for s,x in pairs:
            row=[];chosen=[];argmax=[]
            for status in statuses:
                if status in ('success','failed'):
                    row.append(Fraction(int(status=='success')));chosen.append(None);argmax.append([])
                    continue
                scores=[]
                for a in m.feasible[s,x]:
                    K=controlled_transition(m,s,x,a,pairs)
                    v=sum((k*values[t+1][j][statuses.index(p.observe(status,j,t+1))]
                           for j,k in enumerate(K)),Fraction(0))
                    scores.append((a,v))
                best=max(v for a,v in scores)
                maxima=[a for a,v in scores if v==best]
                row.append(best);chosen.append(maxima[0]);argmax.append(maxima)
            current.append(row);current_action.append(chosen);current_argmax.append(argmax)
        for row in current:
            for val in row:
                if not 0<=val<=1 or max(val.numerator.bit_length(),val.denominator.bit_length())>MAX_OUTPUT_BITS:
                    raise AppError('RESIDENCE_RESOURCE','exact rational monitor DP exceeded numerical bound')
        values[t]=current;selected[t]=current_action;ties[t]=current_argmax
    initial_monitor=[p.observe('search',i,0) for i in range(n)]
    by_start=[values[0][i][statuses.index(initial_monitor[i])] for i in range(n)]
    total=sum((mass*value for mass,value in zip(p.initial_law,by_start)),Fraction(0))
    return {'format':RECEIPT,'problem_semantic_identity':p.semantic_id,
            'model_semantic_identity':m.semantic_id(),
            'joint_states':[{'strategic':s,'world':x} for s,x in pairs],
            'target_indices':list(p.target),'danger_indices':list(p.danger),
            'mode':p.mode,'deadline':p.deadline,'deadline_semantics':p.deadline_semantics,
            'dwell_transitions':p.dwell_transitions,'latest_entry':p.latest_entry,'horizon':H,
            'monitor_states':list(statuses),
            'values_by_observation_time':[[[rational_text(v) for v in row] for row in table] for table in values],
            'chosen_actions_by_observation_time':selected,
            'argmax_actions_by_observation_time':ties,
            'initial_monitor_states':initial_monitor,
            'initial_law':[rational_text(v) for v in p.initial_law],
            'probability_by_initial_state':[rational_text(v) for v in by_start],
            'optimal_success_probability':rational_text(total),
            'policy_class':'fully_observed_time_and_monitor_deterministic_Markov',
            'physical_P_U_held_fixed':True,
            'danger_priority':'BEFORE_OR_AT_SUCCESS' if p.mode=='avoid' else 'NOT_APPLICABLE',
            'through_horizon_risk':'NOT_EVALUATED',
            'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
