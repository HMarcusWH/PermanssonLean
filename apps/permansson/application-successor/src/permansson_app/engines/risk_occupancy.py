"""Exact one-transition occupancy/risk LP over an actual finite alpha/P/U model.

This deliberately bounded profile optimizes fully-observed randomized controls
for one transition only. Occupancy q(y,a)=mu(y)*pi(a|y) supplies a literal
finite LP encoding; an exact primal/dual certificate and independent flow-to-
policy reconstruction are required before any optimality status is exposed.
The numerical result is not a generalized multi-stage occupancy theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld, parse_finite_world, exact_ratio, exact_result
from ..identity import rational_text, semantic_identity
from .lp_types import LP,parse_lp
from .lp import propose_lp_optimum

FORMAT='Permansson.App.OneStepRiskOccupancyRequest.v1'
RECEIPT='Permansson.App.OneStepRiskOccupancyReceipt.v1'
MAX_VARIABLES=5
MAX_STATES=4
MAX_OUTPUT_BITS=8192

@dataclass(frozen=True)
class RiskProblem:
    model:FiniteWorld
    states:tuple[tuple[str,str],...]
    initial:tuple[Fraction,...]
    rewards:tuple[Fraction,...]
    risk_states:tuple[int,...]
    risk_cap:Fraction
    variables:tuple[tuple[int,str],...]
    rows:tuple[tuple[Fraction,...],...]
    reward_coeffs:tuple[Fraction,...]
    risk_coeffs:tuple[Fraction,...]
    lp:LP
    identity:dict


def parse_risk(raw:object)->RiskProblem:
    if type(raw) is not dict or set(raw)!={'format','model','initial_law','terminal_rewards','risk_states','risk_cap'} or raw['format']!=FORMAT:
        raise AppError('RISK_INPUT','wrong one-step occupancy/risk version or fields')
    m=parse_finite_world(raw['model'])
    states=tuple((s,x) for s in m.strategic for x in m.world)
    if len(states)>MAX_STATES:
        raise AppError('RISK_SCOPE','at most four finite joint states')
    def state(row):
        if type(row) is not list or len(row)!=2 or any(type(v) is not str for v in row) or tuple(row) not in states:
            raise AppError('RISK_INPUT','state must be the original [strategic,world] pair')
        return states.index(tuple(row))
    def rows(key,value_field,probability=False):
        entries=raw[key]
        if type(entries) is not list or len(entries)!=len(states):
            raise AppError('RISK_INPUT',key+' must cover the entire state space')
        seen={}
        for item in entries:
            if type(item) is not dict or set(item)!={'state',value_field}:
                raise AppError('RISK_INPUT','invalid '+key+' row')
            i=state(item['state'])
            if i in seen:raise AppError('RISK_INPUT','duplicate '+key+' state')
            seen[i]=exact_ratio(item[value_field],probability=probability)
        return tuple(seen[i] for i in range(len(states)))
    initial=rows('initial_law','mass',True)
    if sum(initial,Fraction(0))!=1:
        raise AppError('RISK_INPUT','initial law must be probability one')
    rewards=rows('terminal_rewards','value')
    risk=raw['risk_states']
    if type(risk) is not list or not 1<=len(risk)<=len(states):
        raise AppError('RISK_INPUT','risk set must be nonempty, finite and fully declared')
    indices=[]
    for pair in risk:
        i=state(pair)
        if i in indices:raise AppError('RISK_INPUT','duplicate risk state')
        indices.append(i)
    indices=tuple(sorted(indices))
    cap=exact_ratio(raw['risk_cap'],probability=True)
    flow=[];controlled=[];rc=[];kc=[]
    for i,(s,x) in enumerate(states):
        for action in m.feasible[s,x]:
            flow.append((i,action))
            K=tuple(m.P[s,x,action][m.world.index(xp)]*m.U[s,x,action,xp][m.strategic.index(sp)]
                    for sp,xp in states)
            if sum(K,Fraction(0))!=1:
                raise AppError('RISK_INPUT','actual controlled P/U atom row is not stochastic')
            controlled.append(K)
            rc.append(sum((p*r for p,r in zip(K,rewards)),Fraction(0)))
            kc.append(sum((K[j] for j in indices),Fraction(0)))
    if not 1<=len(flow)<=MAX_VARIABLES:
        raise AppError('RISK_SCOPE','bounded exact LP supports 1..5 state-action occupancy variables')
    names=[f'q{i}a{m.feasible[states[i]].index(a)}' for i,a in flow]
    C={v:rational_text(c) for v,c in zip(names,rc)}
    constraints=[]
    for state_i in range(len(states)):
        constraints.append({'id':f'mass{state_i}',
            'coefficients':{name:('1' if i==state_i else '0') for name,(i,_) in zip(names,flow)},
            'relation':'=','rhs':rational_text(initial[state_i])})
    constraints.append({'id':'risk_cap',
        'coefficients':{name:rational_text(c) for name,c in zip(names,kc)},
        'relation':'<=','rhs':rational_text(cap)})
    lp=parse_lp({'format':'Permansson.App.ExactLP.v1','variables':names,
        'objective':{'sense':'maximize','coefficients':C},
        'bounds':{name:{'lower':'0','upper':rational_text(initial[i])} for name,(i,_) in zip(names,flow)},
        'constraints':constraints})
    return RiskProblem(m,states,initial,rewards,indices,cap,tuple(flow),tuple(controlled),tuple(rc),tuple(kc),lp,
                       semantic_identity('one-step-risk-occupancy',raw))


def reconstruct_policy(q:RiskProblem,primal:tuple[Fraction,...])->tuple[list[dict],tuple[Fraction,...]]:
    if len(primal)!=len(q.variables) or any(v<0 for v in primal):
        raise AppError('RISK_RECEIPT','invalid occupancy primal')
    law=tuple(sum((primal[i]*row[j] for i,row in enumerate(q.rows)),Fraction(0)) for j in range(len(q.states)))
    if any(max(x.numerator.bit_length(),x.denominator.bit_length())>MAX_OUTPUT_BITS for x in law):
        raise AppError('RISK_RESOURCE','one-step rational state mass exceeds precision budget')
    result=[]
    for i,(s,x) in enumerate(q.states):
        allowed=q.model.feasible[s,x]
        mass=q.initial[i]
        weights={}
        for a in allowed:
            variable=q.variables.index((i,a))
            weight=primal[variable]/mass if mass else Fraction(int(a==allowed[0]))
            weights[a]=rational_text(weight)
        result.append({'state':[s,x],'action_weights':weights,'zero_mass_default_used':mass==0})
    return result,law


def propose_risk(raw:object)->dict:
    q=parse_risk(raw)
    proposal=propose_lp_optimum(q.lp,max_combinations=50000,seconds=8)
    if proposal['status']!='CHECKED_OPTIMAL_CANDIDATE':
        raise AppError('RISK_NO_CERTIFICATE',
                       'bounded LP generator produced '+proposal['status']+'; neither optimum nor infeasibility proved')
    cert=proposal['receipt']
    from ..receipts.lp import check_lp_certificate
    check_lp_certificate(q.lp,cert)
    primal=tuple(exact_result(v) for v in cert['primal'])
    policy,law=reconstruct_policy(q,primal)
    reward=sum((x*r for x,r in zip(law,q.rewards)),Fraction(0))
    exposure=sum((law[i] for i in q.risk_states),Fraction(0))
    if exposure>q.risk_cap or reward!=exact_result(cert['objective_value']) or sum(law,Fraction(0))!=1:
        raise AppError('RISK_INTERNAL','LP and actual next-state law disagree')
    return {'format':RECEIPT,'request_identity':q.identity,'source_model_identity':q.model.semantic_id(),
        'lp_model_identity':q.lp.semantic_id(),
        'joint_states':[{'s':s,'x':x} for s,x in q.states],
        'risk_indices':list(q.risk_states),'risk_cap':rational_text(q.risk_cap),
        'initial_law':[rational_text(v) for v in q.initial],
        'terminal_rewards':[rational_text(v) for v in q.rewards],
        'flow_variables':[{'name':name,'state_index':i,'action':a} for name,(i,a) in zip(q.lp.variables,q.variables)],
        'controlled_next_rows':[[rational_text(v) for v in row] for row in q.rows],
        'objective_coefficients':[rational_text(v) for v in q.reward_coeffs],
        'risk_coefficients':[rational_text(v) for v in q.risk_coeffs],
        'lp_certificate':cert,'policy':policy,
        'next_state_law':[rational_text(v) for v in law],
        'expected_terminal_reward':rational_text(reward),
        'next_step_risk_probability':rational_text(exposure),
        'optimization_scope':'one_transition_fully_observed_randomized_Markov_from_declared_initial_law',
        'initial_zero_mass_policy':'first_declared_feasible_action_without_affecting_flow',
        'lp_vs_reference_solver':'any_independently_checked_primal_dual_optimum_not_reference_vector_identity',
        'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False}
