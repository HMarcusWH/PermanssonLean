"""Independent full-table killed-kernel survival receipt verifier (no producer import)."""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world,compare_strategic_intervention,exact_result
from ..identity import canonical_bytes,semantic_identity,rational_text


def check_survival_receipt(raw:object,receipt:object)->dict:
    if type(raw) is not dict or set(raw)!={'format','baseline','treated','target','region','comparison_states','horizon'} or raw['format']!='Permansson.App.FiniteSurvivalComparison.v1':
        raise AppError('SURVIVAL_INPUT','wrong comparison input')
    if type(receipt) is not dict or set(receipt)!={
        'format','baseline_id','treated_id','comparison_identity','states','region','comparison_states',
        'horizon','baseline_survival','treated_survival','minimum_abs_effect','finite_effect_signs',
        'finite_scope_status','exact_GR_or_PR_certified','lean_status'}:
        raise AppError('SURVIVAL_CERT','receipt has wrong fields')
    if receipt['format']!='Permansson.App.FiniteSurvivalReceipt.v1' or receipt['exact_GR_or_PR_certified'] is not False or receipt['lean_status']!='NOT_EXECUTED':
        raise AppError('SURVIVAL_CERT','forged scientific status')
    b=parse_finite_world(raw['baseline']);t=parse_finite_world(raw['treated']);compare_strategic_intervention(b,t,raw['target'])
    states=tuple((s,x) for s in b.strategic for x in b.world)
    n=len(states);h=raw['horizon']
    if n>12 or type(h) is not int or not 0<=h<=32:
        raise AppError('SURVIVAL_CERT','out of supported finite scope')
    def subset(name):
        seq=raw[name]
        if type(seq) is not list or not seq or len(seq)>n:
            raise AppError('SURVIVAL_CERT','empty or oversized region/comparison')
        names=[]
        for item in seq:
            if type(item) is not list or len(item)!=2 or any(type(x) is not str for x in item):
                raise AppError('SURVIVAL_CERT','invalid state pair')
            k=tuple(item)
            if k not in states or k in names:raise AppError('SURVIVAL_CERT','unknown/duplicate state')
            names.append(k)
        return tuple(names)
    region=subset('region');comparison=subset('comparison_states')
    if not set(comparison)<=set(region):raise AppError('SURVIVAL_CERT','comparison set must be subset of B')
    for fld,expected in [('baseline_id',b.semantic_id()),('treated_id',t.semantic_id()),
                         ('comparison_identity',semantic_identity('finite-survival-comparison',raw)),
                         ('region',raw['region']),('comparison_states',raw['comparison_states']),
                         ('states',[list(x) for x in states]),('horizon',h)]:
        if receipt[fld]!=expected:raise AppError('SURVIVAL_CERT',f'{fld} does not match typed input')
    def independently_composed_kernel(model):
        # Nested atom enumeration independent of the producer's matrix routine.
        atoms=[]
        for s,x in states:
            row=[]
            for sp,xp in states:
                total=Fraction(0)
                for action in model.feasible[s,x]:
                    total+=(model.alpha[s,x][model.actions.index(action)]
                            *model.P[s,x,action][model.world.index(xp)]
                            *model.U[s,x,action,xp][model.strategic.index(sp)])
                row.append(total)
            if sum(row,Fraction(0))!=1:raise AppError('SURVIVAL_CERT','induced model row not stochastic')
            atoms.append(tuple(row))
        return tuple(atoms)
    final=[]
    for label,model in [('baseline',b),('treated',t)]:
        rows=receipt[label+'_survival']
        if type(rows) is not list or len(rows)!=h+1:
            raise AppError('SURVIVAL_CERT','wrong horizon table size')
        K=independently_composed_kernel(model);values=tuple(Fraction(int(s in region)) for s in states)
        for i,row in enumerate(rows):
            if type(row) is not list or len(row)!=n or any(type(x) is not str for x in row):
                raise AppError('SURVIVAL_CERT','row count/shape mismatch')
            candidate=tuple(exact_result(x,probability=True) for x in row)
            if candidate!=values:
                raise AppError('SURVIVAL_CERT',f'{label} survival recurrence false at horizon {i}')
            if i<h:
                values=tuple(sum((K[a][j]*candidate[j] for j,s in enumerate(states) if s in region),Fraction(0))
                             if s in region else Fraction(0) for a,s in enumerate(states))
        final.append(candidate)
    a,z=final
    diffs=[a[states.index(s)]-z[states.index(s)] for s in comparison]
    gap=min(map(abs,diffs))
    signs=['positive' if d>0 else 'negative' if d<0 else 'zero' for d in diffs]
    status='ALL_DECLARED_STARTS_SEPARATED' if gap>0 else 'NO_UNIFORM_FINITE_SEPARATION'
    if receipt['minimum_abs_effect']!=rational_text(gap) or receipt['finite_effect_signs']!=signs or receipt['finite_scope_status']!=status:
        raise AppError('SURVIVAL_CERT','incorrect finite comparison or margin')
    return {'format':'Permansson.App.SurvivalIndependentCheck.v1',
            'status':'FINITE_SURVIVAL_TABLE_VERIFIED','comparison_identity':receipt['comparison_identity'],
            'certificate_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'exact_regime_established':False,'lean_status':'NOT_EXECUTED'}
