"""Independent exact check of every finite-monitor Bellman row and event semantics."""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes,rational_text
from ..engines.monitors import parse_residence

KEYS={'format','problem_semantic_identity','model_semantic_identity','joint_states',
      'target_indices','danger_indices','mode','deadline','deadline_semantics',
      'dwell_transitions','latest_entry','horizon','monitor_states',
      'values_by_observation_time','chosen_actions_by_observation_time',
      'argmax_actions_by_observation_time','initial_monitor_states','initial_law',
      'probability_by_initial_state','optimal_success_probability','policy_class',
      'physical_P_U_held_fixed','danger_priority','through_horizon_risk',
      'lean_status','empirical_identification','scientific_claims_verified'}


def check_residence(raw:object,receipt:object):
    p=parse_residence(raw)
    m=p.model
    pairs=[(s,x) for s in m.strategic for x in m.world]
    st=p.monitor_states;n=len(pairs);k=len(st);H=p.horizon
    if type(receipt) is not dict or set(receipt)!=KEYS or receipt['format']!='Permansson.App.FiniteResidenceReceipt.v1':
        raise AppError('RESIDENCE_RECEIPT','incorrect monitor receipt shape')
    fields={'problem_semantic_identity':p.semantic_id,
        'model_semantic_identity':m.semantic_id(),
        'joint_states':[{'strategic':s,'world':x} for s,x in pairs],
        'target_indices':list(p.target),'danger_indices':list(p.danger),
        'mode':p.mode,'deadline':p.deadline,'deadline_semantics':p.deadline_semantics,
        'dwell_transitions':p.dwell_transitions,'latest_entry':p.latest_entry,
        'horizon':H,'monitor_states':list(st),
        'initial_law':[rational_text(x) for x in p.initial_law],
        'policy_class':'fully_observed_time_and_monitor_deterministic_Markov',
        'physical_P_U_held_fixed':True,
        'danger_priority':'BEFORE_OR_AT_SUCCESS' if p.mode=='avoid' else 'NOT_APPLICABLE',
        'through_horizon_risk':'NOT_EVALUATED',
        'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False}
    for name,value in fields.items():
        if type(value) is bool:
            if receipt[name] is not value:raise AppError('RESIDENCE_RECEIPT',f'{name} wrong')
        elif receipt[name]!=value:raise AppError('RESIDENCE_RECEIPT',f'{name} mismatch')
    values=receipt['values_by_observation_time']
    chosen=receipt['chosen_actions_by_observation_time']
    args=receipt['argmax_actions_by_observation_time']
    if any(type(data) is not list or len(data)!=H+1 for data in (values,chosen,args)):
        raise AppError('RESIDENCE_RECEIPT','time range incomplete')
    tables=[]
    for t in range(H+1):
        if any(type(table) is not list or len(table)!=n for table in (values[t],chosen[t],args[t])):
            raise AppError('RESIDENCE_RECEIPT','state rows incomplete')
        row=[]
        for i in range(n):
            if any(type(line) is not list or len(line)!=k for line in (values[t][i],chosen[t][i],args[t][i])):
                raise AppError('RESIDENCE_RECEIPT','monitor columns incomplete')
            row.append([exact_result(v,probability=True) for v in values[t][i]])
        tables.append(row)
    for t in range(H,-1,-1):
        for i,(s,x) in enumerate(pairs):
            for j,status in enumerate(st):
                given=tables[t][i][j]
                selection=chosen[t][i][j];optima=args[t][i][j]
                if t==H or status in ('success','failed'):
                    if given!=int(status=='success') or selection is not None or optima!=[]:
                        raise AppError('RESIDENCE_RECEIPT','terminal row or no-action convention wrong')
                    continue
                # Independently recompose transition atoms from P and U. Never use
                # controlled_transition or the Bellman solver's rows.
                scores=[]
                for a in m.feasible[s,x]:
                    probability=[m.P[s,x,a][m.world.index(xp)]*m.U[s,x,a,xp][m.strategic.index(sp)]
                                 for sp,xp in pairs]
                    if sum(probability,Fraction(0))!=1:raise AppError('RESIDENCE_RECEIPT','P/U row invalid')
                    score=Fraction(0)
                    for dest,atom in enumerate(probability):
                        following=p.observe(status,dest,t+1)
                        score+=atom*tables[t+1][dest][st.index(following)]
                    scores.append((a,score))
                maximum=max(z for _,z in scores)
                winners=[a for a,z in scores if z==maximum]
                if given!=maximum or selection not in winners or optima!=winners:
                    raise AppError('RESIDENCE_RECEIPT','wrong Bellman value or optimizing action')
    expected_initial=[p.observe('search',i,0) for i in range(n)]
    val=[tables[0][i][st.index(status)] for i,status in enumerate(expected_initial)]
    total=sum((a*b for a,b in zip(p.initial_law,val)),Fraction(0))
    if (receipt['initial_monitor_states']!=expected_initial or
        receipt['probability_by_initial_state']!=[rational_text(v) for v in val] or
        exact_result(receipt['optimal_success_probability'],probability=True)!=total):
        raise AppError('RESIDENCE_RECEIPT','initial-time event or success probability mismatch')
    return {'format':'Permansson.App.IndependentResidenceCheck.v1','status':'PASS',
            'checked_states':n,'checked_monitor_states':k,'checked_times':H+1,
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'FINITE_RESIDENCE_NUMERIC_ONLY'}
