"""Finite frozen-menu numeric optimization over fully declared strategic interventions.

Only optimum within the listed, validated, finite menu is claimed. The menu is
an analyst-supplied set, not the full space of possible policies. This code
has no Lean certificate or external causal identification.
"""
from __future__ import annotations
from fractions import Fraction
import re
from ..errors import AppError
from ..finite_world import parse_finite_world,compare_strategic_intervention,induced_kernel
from ..identity import semantic_identity,rational_text

FORMAT='Permansson.App.FrozenMenuRequest.v1'
RECEIPT='Permansson.App.FrozenMenuReceipt.v1'
_ID=re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')

def _get(raw):
    if type(raw) is not dict or set(raw)!={'format','baseline','region','start_state','horizon','value_type','direction','menu'} or raw['format']!=FORMAT:
        raise AppError('MENU_INPUT','frozen menu request requires exact versioned fields')
    base=parse_finite_world(raw['baseline'])
    states=tuple((s,x) for s in base.strategic for x in base.world)
    if len(states)>12:raise AppError('MENU_SCOPE','supports up to 12 joint states')
    if type(raw['region']) is not list or not raw['region'] or len(raw['region'])>len(states):
        raise AppError('MENU_REGION','invalid region')
    region=[]
    for pair in raw['region']:
        if type(pair) is not list or len(pair)!=2 or any(type(x) is not str for x in pair) or tuple(pair) not in states or tuple(pair) in region:
            raise AppError('MENU_REGION','foreign or repeated region state')
        region.append(tuple(pair))
    start=raw['start_state']
    if type(start) is not list or len(start)!=2 or tuple(start) not in region:
        raise AppError('MENU_START','start state must lie in region')
    h=raw['horizon']
    if type(h) is not int or not 0<=h<=16:raise AppError('MENU_HORIZON','supported horizon is 0..16')
    if raw['value_type'] not in ('survival_horizon','exit_by_horizon'):
        raise AppError('MENU_OBJECTIVE','unsupported event')
    if raw['direction'] not in ('max','min'):
        raise AppError('MENU_OBJECTIVE','direction must be max or min')
    if type(raw['menu']) is not list or not 1<=len(raw['menu'])<=8:
        raise AppError('MENU_SCOPE','frozen menu must contain 1..8 choices')
    choices=[]
    seen=set()
    for item in raw['menu']:
        if type(item) is not dict or set(item)!={'id','target','treated'}:
            raise AppError('MENU_INPUT','choice must specify id,target,treated')
        ident=item['id']
        if type(ident) is not str or not _ID.fullmatch(ident) or ident in seen:
            raise AppError('MENU_INPUT','choice identifier repeated or invalid')
        seen.add(ident)
        treat=parse_finite_world(item['treated'])
        compare_strategic_intervention(base,treat,item['target'])
        choices.append((ident,treat,item['target']))
    return base,states,tuple(region),tuple(start),h,tuple(choices)

def _survival(K,states,region,start,h):
    inside=set(region)
    values=tuple(Fraction(int(state in inside)) for state in states)
    for _ in range(h):
        values=tuple(sum((K[i][j]*values[j] for j,s in enumerate(states) if s in inside),Fraction(0)) if state in inside else Fraction(0)
                     for i,state in enumerate(states))
        for q in values:
            if max(q.numerator.bit_length(),q.denominator.bit_length())>8192:
                raise AppError('MENU_RESOURCE','exact rational exceeds bound')
    return values[states.index(start)]

def propose_menu(raw:object)->dict:
    base,states,region,start,h,menu=_get(raw)
    baseline=_survival(induced_kernel(base),states,region,start,h)
    values=[]
    for ident,treat,target in menu:
        survival=_survival(induced_kernel(treat),states,region,start,h)
        value=survival if raw['value_type']=='survival_horizon' else 1-survival
        values.append((ident,value,treat.semantic_id(),target))
    best=(max if raw['direction']=='max' else min)(v for _,v,_,_ in values)
    tied=sorted(ident for ident,val,_,_ in values if val==best)
    result={
        'format':RECEIPT,'request_identity':semantic_identity('finite-frozen-menu',raw),
        'baseline_identity':base.semantic_id(),
        'region':[list(x) for x in region],'start_state':list(start),
        'horizon':h,'value_type':raw['value_type'],'direction':raw['direction'],
        'baseline_survival':rational_text(baseline),
        'menu_values':[{'id':ident,'value':rational_text(val),'treated_identity':sid,'target':target}
                       for ident,val,sid,target in values],
        'optimum_value':rational_text(best),'attaining_ids':tied,
        'representative_id':tied[0],
        'scope_status':'FROZEN_DECLARED_MENU_ONLY',
        'exact_GR_or_PR_certified':False,'lean_status':'NOT_EXECUTED',
    }
    return result
