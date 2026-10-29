"""Independent exact evaluation of all frozen-menu alternatives.

Does not import the producer or its recurrence; checks the represented objective
and the selected maximizing/minimizing set against the actual typed input.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world,compare_strategic_intervention,exact_ratio
from ..identity import canonical_bytes,semantic_identity,rational_text

_FIELDS={'format','request_identity','baseline_identity','region','start_state','horizon','value_type','direction',
         'baseline_survival','menu_values','optimum_value','attaining_ids','representative_id',
         'scope_status','exact_GR_or_PR_certified','lean_status'}

def _direct_survival(model,states,region,start,h):
    # Expand all one-step alpha/P/U events, independent of producer's induced-kernel matrix.
    allowed=set(region)
    values={state:Fraction(int(state in allowed)) for state in states}
    for _ in range(h):
        nxt={}
        for s,x in states:
            if (s,x) not in allowed:
                nxt[(s,x)]=Fraction(0)
                continue
            prob=Fraction(0)
            for a in model.feasible[s,x]:
                pa=model.alpha[s,x][model.actions.index(a)]
                for xp,px in zip(model.world,model.P[s,x,a]):
                    for sp,pu in zip(model.strategic,model.U[s,x,a,xp]):
                        if (sp,xp) in allowed:
                            prob+=pa*px*pu*values[sp,xp]
            if not 0<=prob<=1 or max(prob.numerator.bit_length(),prob.denominator.bit_length())>8192:
                raise AppError('MENU_CERT','direct survival outside bounded probability')
            nxt[s,x]=prob
        values=nxt
    return values[start]

def check_menu(raw:object,receipt:object)->dict:
    if type(raw) is not dict or type(receipt) is not dict or set(receipt)!=_FIELDS:
        raise AppError('MENU_CERT','malformed request/receipt fields')
    if set(raw)!={'format','baseline','region','start_state','horizon','value_type','direction','menu'} or raw['format']!='Permansson.App.FrozenMenuRequest.v1':
        raise AppError('MENU_CERT','unsupported input')
    if (receipt['format']!='Permansson.App.FrozenMenuReceipt.v1'
            or receipt['scope_status']!='FROZEN_DECLARED_MENU_ONLY'
            or receipt['exact_GR_or_PR_certified'] is not False or receipt['lean_status']!='NOT_EXECUTED'):
        raise AppError('MENU_CERT','false scientific scope')
    baseline=parse_finite_world(raw['baseline'])
    states=tuple((s,x) for s in baseline.strategic for x in baseline.world)
    region=raw['region'];start=raw['start_state'];h=raw['horizon']
    if len(states)>12 or type(region) is not list or not region or len(region)>len(states):
        raise AppError('MENU_CERT','bad source domain')
    if any(type(pair) is not list or len(pair)!=2 or any(type(x) is not str for x in pair) or tuple(pair) not in states for pair in region):
        raise AppError('MENU_CERT','invalid region labels')
    inside=tuple(map(tuple,region))
    if len(set(inside))!=len(inside) or type(start) is not list or tuple(start) not in inside:
        raise AppError('MENU_CERT','region/start outside domain')
    if type(h) is not int or not 0<=h<=16 or raw['value_type'] not in ('survival_horizon','exit_by_horizon') or raw['direction'] not in ('max','min'):
        raise AppError('MENU_CERT','unsupported objective')
    menu=raw['menu']
    if type(menu) is not list or not 1<=len(menu)<=8:
        raise AppError('MENU_CERT','invalid frozen menu size')
    fixed=[('request_identity',semantic_identity('finite-frozen-menu',raw)),
            ('baseline_identity',baseline.semantic_id()),('region',region),('start_state',start),
            ('horizon',h),('value_type',raw['value_type']),('direction',raw['direction'])]
    for label,value in fixed:
        if receipt[label]!=value:raise AppError('MENU_CERT',f'{label} does not bind input')
    original=_direct_survival(baseline,states,inside,tuple(start),h)
    if receipt['baseline_survival']!=rational_text(original):
        raise AppError('MENU_CERT','false baseline value')
    entries=receipt['menu_values']
    if type(entries) is not list or len(entries)!=len(menu):raise AppError('MENU_CERT','missing/invented menu entry')
    values=[];seen=set()
    for supplied,claimed in zip(menu,entries):
        if type(supplied) is not dict or set(supplied)!={'id','target','treated'} or type(claimed) is not dict or set(claimed)!={'id','value','treated_identity','target'}:
            raise AppError('MENU_CERT','invalid item shape')
        ident=supplied['id']
        if type(ident) is not str or not ident or len(ident)>32 or ident in seen or not(ident[0].isascii() and ident[0].isalpha()) or any(not(c.isascii() and (c.isalnum() or c in '_-')) for c in ident):
            raise AppError('MENU_CERT','repeated/invalid menu ID')
        seen.add(ident)
        alt=parse_finite_world(supplied['treated'])
        compare_strategic_intervention(baseline,alt,supplied['target'])
        if claimed['id']!=ident or claimed['target']!=supplied['target'] or claimed['treated_identity']!=alt.semantic_id():
            raise AppError('MENU_CERT','menu binding mismatch')
        survival=_direct_survival(alt,states,inside,tuple(start),h)
        value=survival if raw['value_type']=='survival_horizon' else 1-survival
        if claimed['value']!=rational_text(value):raise AppError('MENU_CERT','incorrect menu objective value')
        values.append((ident,value))
    optimum=(max if raw['direction']=='max' else min)(v for _,v in values)
    tied=sorted(i for i,v in values if v==optimum)
    if receipt['optimum_value']!=rational_text(optimum) or receipt['attaining_ids']!=tied or receipt['representative_id']!=tied[0]:
        raise AppError('MENU_CERT','false optimum or incomplete tie set')
    return {'format':'Permansson.App.MenuIndependentCheck.v1','status':'FROZEN_MENU_OPTIMUM_VERIFIED',
        'request_identity':receipt['request_identity'],
        'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
        'scope':'DECLARED_MENU_ONLY','lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED'}
