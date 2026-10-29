"""Independent exact one-step occupancy/flow correspondence checker.

Rebuilds the LP coefficients from the *original* finite strategic-world P/U,
initial law, terminal reward and risk event, then validates an independent
primal/dual receipt. Does not import the occupancy LP producer/encoder or
assume a reference optimizer's selected primal vector is unique.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world,exact_ratio
from ..identity import canonical_bytes,semantic_identity,rational_text
from ..engines.lp_types import parse_lp
from .lp import check_lp_certificate

REQUEST='Permansson.App.OneStepRiskOccupancyRequest.v1'
RECEIPT='Permansson.App.OneStepRiskOccupancyReceipt.v1'


def _same(actual,expected,path='receipt'):
    if type(actual) is not type(expected):
        raise AppError('RISK_RECEIPT',path+' wrong JSON scalar/container type')
    if type(expected) is dict:
        if set(actual)!=set(expected):raise AppError('RISK_RECEIPT',path+' changed field set')
        for k in expected:_same(actual[k],expected[k],path+'.'+k)
    elif type(expected) is list:
        if len(actual)!=len(expected):raise AppError('RISK_RECEIPT',path+' changed list length')
        for i,(a,e) in enumerate(zip(actual,expected)):_same(a,e,path+'['+str(i)+']')
    elif actual!=expected:
        raise AppError('RISK_RECEIPT',path+' numerical or semantic mismatch')


def check_risk(raw:object,receipt:object)->dict:
    if type(raw) is not dict or set(raw)!={'format','model','initial_law','terminal_rewards','risk_states','risk_cap'} or raw['format']!=REQUEST:
        raise AppError('RISK_INPUT','unsupported risk occupancy input')
    m=parse_finite_world(raw['model'])
    states=tuple((s,x) for s in m.strategic for x in m.world)
    if len(states)>4:raise AppError('RISK_SCOPE','finite state bound')
    def state(row):
        if type(row) is not list or len(row)!=2 or any(type(v) is not str for v in row) or tuple(row) not in states:
            raise AppError('RISK_INPUT','untyped/unknown original state')
        return states.index(tuple(row))
    def read_map(key,field,prob=False):
        rows=raw[key]
        if type(rows) is not list or len(rows)!=len(states):
            raise AppError('RISK_INPUT','incomplete '+key)
        found={}
        for item in rows:
            if type(item) is not dict or set(item)!={'state',field}:raise AppError('RISK_INPUT','invalid '+key)
            i=state(item['state'])
            if i in found:raise AppError('RISK_INPUT','duplicate '+key)
            found[i]=exact_ratio(item[field],probability=prob)
        return tuple(found[i] for i in range(len(states)))
    law=read_map('initial_law','mass',True)
    if sum(law,Fraction(0))!=1:raise AppError('RISK_INPUT','initial mass is not one')
    terminal=read_map('terminal_rewards','value')
    target=raw['risk_states']
    if type(target) is not list or not 1<=len(target)<=len(states):
        raise AppError('RISK_INPUT','invalid risk event')
    risky=tuple(sorted({state(x) for x in target}))
    if len(risky)!=len(target):raise AppError('RISK_INPUT','duplicate risk event state')
    risk_cap=exact_ratio(raw['risk_cap'],probability=True)
    variables=[]; controlled=[];rewards=[];risks=[]
    for i,(s,x) in enumerate(states):
        for action in m.feasible[s,x]:
            variables.append((i,action))
            # Fully recompose each actual controlled state transition; an input
            # alpha distribution never substitutes for a controlled action.
            row=[]
            for sp,xp in states:
                mass=m.P[s,x,action][m.world.index(xp)]*m.U[s,x,action,xp][m.strategic.index(sp)]
                row.append(mass)
            if sum(row,Fraction(0))!=1:
                raise AppError('RISK_RECEIPT','P/U reification is not a stochastic row')
            controlled.append(tuple(row))
            rewards.append(sum((row[j]*terminal[j] for j in range(len(states))),Fraction(0)))
            risks.append(sum((row[j] for j in risky),Fraction(0)))
    if not 1<=len(variables)<=5:raise AppError('RISK_SCOPE','at most five occupancy variables')
    names=[f'q{i}a{m.feasible[states[i]].index(a)}' for i,a in variables]
    lp_data={'format':'Permansson.App.ExactLP.v1','variables':names,
        'objective':{'sense':'maximize','coefficients':{v:rational_text(rewards[j]) for j,v in enumerate(names)}},
        'bounds':{v:{'lower':'0','upper':rational_text(law[i])} for v,(i,_) in zip(names,variables)},
        'constraints':[{'id':f'mass{i}','coefficients':{v:'1' if j==i else '0' for v,(j,_) in zip(names,variables)},
                        'relation':'=','rhs':rational_text(law[i])} for i in range(len(states))]+
                      [{'id':'risk_cap','coefficients':{v:rational_text(r) for v,r in zip(names,risks)},
                        'relation':'<=','rhs':rational_text(risk_cap)}]}
    lp=parse_lp(lp_data)
    if type(receipt) is not dict or 'lp_certificate' not in receipt:
        raise AppError('RISK_RECEIPT','no checkable LP certificate supplied')
    lc=check_lp_certificate(lp,receipt['lp_certificate'])
    if lc['status']!='OPTIMAL_VERIFIED':raise AppError('RISK_RECEIPT','LP objective not independently optimal')
    flow=tuple(exact_ratio(v) for v in receipt['lp_certificate']['primal'])
    if len(flow)!=len(variables):raise AppError('RISK_RECEIPT','wrong occupancy vector dimension')
    new_law=[sum((flow[i]*controlled[i][j] for i in range(len(variables))),Fraction(0)) for j in range(len(states))]
    if sum(new_law,Fraction(0))!=1:
        raise AppError('RISK_RECEIPT','reconstructed actual next-state law not normalized')
    risk_mass=sum((new_law[i] for i in risky),Fraction(0))
    reward_value=sum((p*r for p,r in zip(new_law,terminal)),Fraction(0))
    if risk_mass>risk_cap or reward_value!=exact_ratio(receipt['lp_certificate']['objective_value']):
        raise AppError('RISK_RECEIPT','LP objective or risk bound disagrees with original actual transition')
    policy=[]
    for i,(s,x) in enumerate(states):
        µ=law[i]; allowed=m.feasible[s,x]
        action_weights={a:rational_text(flow[variables.index((i,a))]/µ if µ else Fraction(int(a==allowed[0]))) for a in allowed}
        probabilities=[exact_ratio(v,probability=True) for v in action_weights.values()]
        if sum(probabilities,Fraction(0))!=1:
            raise AppError('RISK_RECEIPT','reconstructed randomized policy not normalized')
        policy.append({'state':[s,x],'action_weights':action_weights,'zero_mass_default_used':µ==0})
    expected={
        'format':RECEIPT,
        'request_identity':semantic_identity('one-step-risk-occupancy',raw),
        'source_model_identity':m.semantic_id(),
        'lp_model_identity':lp.semantic_id(),
        'joint_states':[{'s':s,'x':x} for s,x in states],
        'risk_indices':list(risky),'risk_cap':rational_text(risk_cap),
        'initial_law':[rational_text(v) for v in law],
        'terminal_rewards':[rational_text(v) for v in terminal],
        'flow_variables':[{'name':name,'state_index':i,'action':a} for name,(i,a) in zip(names,variables)],
        'controlled_next_rows':[[rational_text(v) for v in row] for row in controlled],
        'objective_coefficients':[rational_text(v) for v in rewards],
        'risk_coefficients':[rational_text(v) for v in risks],
        'lp_certificate':receipt['lp_certificate'],
        'policy':policy,
        'next_state_law':[rational_text(v) for v in new_law],
        'expected_terminal_reward':rational_text(reward_value),
        'next_step_risk_probability':rational_text(risk_mass),
        'optimization_scope':'one_transition_fully_observed_randomized_Markov_from_declared_initial_law',
        'initial_zero_mass_policy':'first_declared_feasible_action_without_affecting_flow',
        'lp_vs_reference_solver':'any_independently_checked_primal_dual_optimum_not_reference_vector_identity',
        'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False,
    }
    _same(receipt,expected)
    return {'format':'Permansson.App.IndependentOneStepRiskCheck.v1','status':'PASS',
            'original_source_bound':True,'primal_dual_status':lc['status'],
            'checked_states':len(states),'checked_occupancy_variables':len(variables),
            'one_step_risk_bound':'VERIFIED',
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'ONE_TRANSITION_RANDOMIZED_NUMERIC_ONLY'}
