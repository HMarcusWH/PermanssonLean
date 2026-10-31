"""Exact affine normalization for a bounded, finite rational LP class.

The supported original problem has finite lower bounds, optional upper bounds,
nonnegative transformed variables, and <=, >= or = linear rows. This is NOT a
universal solver or certificate for unrestricted controls/real dynamics.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
import re
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import rational_text, semantic_identity

_NAME=re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')

@dataclass(frozen=True)
class LP:
    variables:tuple[str,...]
    maximize:bool
    coeffs:tuple[Fraction,...]
    lower:tuple[Fraction,...]
    upper:tuple[Fraction|None,...]
    original_rows:tuple[tuple[str,tuple[Fraction,...],str,Fraction],...]
    A:tuple[tuple[Fraction,...],...]
    b:tuple[Fraction,...]
    c:tuple[Fraction,...]
    offset:Fraction
    row_labels:tuple[str,...]

    def normalized_payload(self)->dict:
        return {'format':'Permansson.App.ExactLP.v1',
            'variables':list(self.variables),
            'objective':{'sense':'maximize' if self.maximize else 'minimize',
                         'coefficients':{v:rational_text(c) for v,c in zip(self.variables,self.coeffs)}},
            'bounds':{v:{'lower':rational_text(l), 'upper':rational_text(u) if u is not None else None}
                      for v,l,u in zip(self.variables,self.lower,self.upper)},
            'constraints':[{'id':label,'coefficients':{v:rational_text(a) for v,a in zip(self.variables,coeffs)},
                            'relation':sense,'rhs':rational_text(rhs)}
                           for label,coeffs,sense,rhs in self.original_rows]}

    def semantic_id(self)->dict:
        return semantic_identity('exact-rational-linear-program',self.normalized_payload())


def parse_lp(raw:object)->LP:
    if type(raw) is not dict or set(raw)!={'format','variables','objective','bounds','constraints'} or raw['format']!='Permansson.App.ExactLP.v1':
        raise AppError('LP_INPUT','wrong LP envelope')
    names=raw['variables']
    if type(names) is not list or not 1<=len(names)<=6 or any(type(v) is not str or not _NAME.fullmatch(v) for v in names) or len(set(names))!=len(names):
        raise AppError('LP_INPUT','declare 1..6 distinct variables')
    names=tuple(names)
    obj=raw['objective']
    if type(obj) is not dict or set(obj)!={'sense','coefficients'} or obj['sense'] not in ('maximize','minimize'):
        raise AppError('LP_INPUT','objective malformed')
    if type(obj['coefficients']) is not dict or set(obj['coefficients'])!=set(names):
        raise AppError('LP_INPUT','objective coefficients incomplete')
    coeffs=tuple(exact_ratio(obj['coefficients'][v]) for v in names)
    bounds=raw['bounds']
    if type(bounds) is not dict or set(bounds)!=set(names):
        raise AppError('LP_INPUT','bounds incomplete')
    lower=[];upper=[]
    for v in names:
        bound=bounds[v]
        if type(bound) is not dict or set(bound)!={'lower','upper'}:
            raise AppError('LP_INPUT','bound malformed')
        lo=exact_ratio(bound['lower']);up=None if bound['upper'] is None else exact_ratio(bound['upper'])
        if up is not None and up<lo:
            raise AppError('LP_INPUT','upper bound less than lower')
        lower.append(lo);upper.append(up)
    lower=tuple(lower);upper=tuple(upper)
    rows=raw['constraints']
    if type(rows) is not list or len(rows)>16:
        raise AppError('LP_INPUT','exceeds 16 constraint rows')
    original=[];A=[];b=[];tags=[];ids=set()
    for row in rows:
        if type(row) is not dict or set(row)!={'id','coefficients','relation','rhs'}:
            raise AppError('LP_INPUT','constraint malformed')
        label=row['id'];sense=row['relation']
        if type(label) is not str or not _NAME.fullmatch(label) or label in ids or sense not in ('<=','>=','='):
            raise AppError('LP_INPUT','constraint name/relation invalid')
        ids.add(label)
        if type(row['coefficients']) is not dict or set(row['coefficients'])!=set(names):
            raise AppError('LP_INPUT','constraint coefficients incomplete')
        coeff=tuple(exact_ratio(row['coefficients'][v]) for v in names)
        rhs=exact_ratio(row['rhs'])
        original.append((label,coeff,sense,rhs))
        shifted=rhs-sum((a*l for a,l in zip(coeff,lower)),Fraction(0))
        for sign,which in ((1,'le'),(-1,'ge')):
            if (sense=='<=' and sign==-1) or (sense=='>=' and sign==1):continue
            A.append(tuple(sign*a for a in coeff));b.append(sign*shifted);tags.append(label+':'+which)
    for i,(v,lo,up) in enumerate(zip(names,lower,upper)):
        if up is not None:
            coeff=tuple(Fraction(int(j==i)) for j in range(len(names)))
            A.append(coeff);b.append(up-lo);tags.append('bound:'+v)
    c=tuple((a if obj['sense']=='maximize' else -a) for a in coeffs)
    offset=sum((a*l for a,l in zip(c,lower)),Fraction(0))
    if len(A)>32:raise AppError('LP_INPUT','transformed constraint budget exceeded')
    return LP(names,obj['sense']=='maximize',coeffs,lower,upper,tuple(original),tuple(A),tuple(b),c,offset,tuple(tags))
