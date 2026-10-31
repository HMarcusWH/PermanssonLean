"""Exact finite strategic-world α/P/U model and held-fixed interventions.

This is numeric reification, not a mathematical or causal identification receipt.
The induced law follows the paper's ordering: alpha(s,x,a), P(s,x,a,x'),
then U(s,x,a,x',s'). No inference about an external factorization is made.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from types import MappingProxyType
from typing import Mapping
import re
from .errors import AppError
from .identity import rational_text, semantic_identity

_TOKEN=re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')
_RAT=re.compile(r'^(?:0|[1-9][0-9]*|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?$')
MAX_DIM=6
MAX_BITS=256


def exact_ratio(text: object, *, probability: bool=False) -> Fraction:
    if type(text) is not str or len(text)>160 or not _RAT.fullmatch(text):
        raise AppError('RATIONAL_FORMAT','exact rational must be canonical signed decimal or numerator/positive denominator')
    try: value=Fraction(text)
    except (ValueError,ZeroDivisionError) as exc: raise AppError('RATIONAL_FORMAT','malformed rational') from exc
    if max(value.numerator.bit_length(),value.denominator.bit_length())>MAX_BITS:
        raise AppError('RATIONAL_SIZE','rational precision exceeds supported bound')
    if probability and not (0 <= value <= 1):
        raise AppError('PROBABILITY','probability outside [0,1]')
    return value


def _strict_map(value: object, names: tuple[str,...], scope: str) -> tuple[Fraction,...]:
    if type(value) is not dict or set(value)!=set(names):
        raise AppError('KERNEL_ROW',f'{scope}: must supply exactly the declared output support')
    result=tuple(exact_ratio(value[name],probability=True) for name in names)
    if sum(result,Fraction(0))!=1:
        raise AppError('KERNEL_SUM',f'{scope}: stochastic row does not sum to 1')
    return result


def _tokens(value: object, scope: str) -> tuple[str,...]:
    if type(value) is not list or not 1<=len(value)<=MAX_DIM or any(type(s) is not str or not _TOKEN.fullmatch(s) for s in value) or len(set(value))!=len(value):
        raise AppError('MODEL_DIMENSIONS',f'{scope}: expected 1..{MAX_DIM} distinct identifiers')
    return tuple(value)


def _read_rows(rows: object, keys: tuple[str,...], label: str) -> dict[tuple[str,...],dict]:
    if type(rows) is not list:
        raise AppError('MODEL_STRUCTURE',f'{label} must be a JSON array')
    out={}
    for row in rows:
        if type(row) is not dict or set(row)!=set(keys)|{'weights'}:
            # Feasibility has a different structure and is handled separately.
            raise AppError('MODEL_STRUCTURE',f'{label} row has wrong fields')
        key=tuple(row[k] for k in keys)
        if any(type(k) is not str for k in key) or key in out:
            raise AppError('MODEL_STRUCTURE',f'{label} duplicate/invalid row key')
        out[key]=row['weights']
    return out


@dataclass(frozen=True)
class FiniteWorld:
    strategic: tuple[str,...]
    world: tuple[str,...]
    actions: tuple[str,...]
    feasible: Mapping[tuple[str,str],tuple[str,...]]
    alpha: Mapping[tuple[str,str],tuple[Fraction,...]]
    P: Mapping[tuple[str,str,str],tuple[Fraction,...]]
    U: Mapping[tuple[str,str,str,str],tuple[Fraction,...]]

    def canonical_data(self) -> dict:
        return {
            'format':'Permansson.App.FiniteStrategicWorld.v1',
            'states':{'strategic':list(self.strategic),'world':list(self.world),'actions':list(self.actions)},
            'feasible':[{'s':s,'x':x,'actions':list(self.feasible[s,x])} for s in self.strategic for x in self.world],
            'alpha':[{'s':s,'x':x,'weights':{a:rational_text(p) for a,p in zip(self.actions,self.alpha[s,x])}}
                     for s in self.strategic for x in self.world],
            'P':[{'s':s,'x':x,'a':a,'weights':{xp:rational_text(p) for xp,p in zip(self.world,self.P[s,x,a])}}
                 for s in self.strategic for x in self.world for a in self.feasible[s,x]],
            'U':[{'s':s,'x':x,'a':a,'xp':xp,'weights':{sp:rational_text(p) for sp,p in zip(self.strategic,self.U[s,x,a,xp])}}
                 for s in self.strategic for x in self.world for a in self.feasible[s,x] for xp in self.world],
        }

    def semantic_id(self) -> dict:
        return semantic_identity('finite-strategic-world',self.canonical_data())


def parse_finite_world(raw: object) -> FiniteWorld:
    if type(raw) is not dict or set(raw)!={'format','states','feasible','alpha','P','U'} or raw['format']!='Permansson.App.FiniteStrategicWorld.v1':
        raise AppError('MODEL_STRUCTURE','unsupported finite model format or keys')
    st=raw['states']
    if type(st) is not dict or set(st)!={'strategic','world','actions'}:
        raise AppError('MODEL_STRUCTURE','state inventory must declare strategic/world/actions')
    S,X,A=[_tokens(st[k],k) for k in ('strategic','world','actions')]
    pairs={(s,x) for s in S for x in X}
    feasible={}
    if type(raw['feasible']) is not list:
        raise AppError('FEASIBILITY','feasible must be array')
    for row in raw['feasible']:
        if type(row) is not dict or set(row)!={'s','x','actions'}:
            raise AppError('FEASIBILITY','feasible row malformed')
        k=(row['s'],row['x'])
        if any(type(val) is not str for val in k):
            raise AppError('FEASIBILITY','invalid state identifier type')
        if k not in pairs or k in feasible or type(row['actions']) is not list or not row['actions'] or any(type(a) is not str or a not in A for a in row['actions']) or len(set(row['actions']))!=len(row['actions']):
            raise AppError('FEASIBILITY','invalid, repeated or empty feasible action set')
        feasible[k]=tuple(a for a in A if a in row['actions'])
    if set(feasible)!=pairs:
        raise AppError('FEASIBILITY','missing state-specific action set')
    ar=_read_rows(raw['alpha'],('s','x'),'alpha')
    if set(ar)!=pairs: raise AppError('MODEL_STRUCTURE','alpha support incomplete or foreign')
    alpha={}
    for s,x in pairs:
        v=_strict_map(ar[s,x],A,'alpha')
        if any(v[i] and a not in feasible[s,x] for i,a in enumerate(A)):
            raise AppError('FEASIBILITY','alpha assigns mass to an infeasible action')
        alpha[s,x]=v
    pkeys={(s,x,a) for s,x in pairs for a in feasible[s,x]}
    pr=_read_rows(raw['P'],('s','x','a'),'P')
    if set(pr)!=pkeys: raise AppError('MODEL_STRUCTURE','P support incomplete or foreign')
    P={k:_strict_map(v,X,'P') for k,v in pr.items()}
    ukeys={(s,x,a,xp) for s,x,a in pkeys for xp in X}
    ur=_read_rows(raw['U'],('s','x','a','xp'),'U')
    if set(ur)!=ukeys:raise AppError('MODEL_STRUCTURE','U support incomplete or foreign')
    U={k:_strict_map(v,S,'U') for k,v in ur.items()}
    return FiniteWorld(S,X,A,MappingProxyType(feasible),MappingProxyType(alpha),MappingProxyType(P),MappingProxyType(U))


def induced_kernel(model:FiniteWorld) -> tuple[tuple[Fraction,...],...]:
    """Ordered joint states (s,x) -> (s',x'). Exact mathematical composition."""
    states=[(s,x) for s in model.strategic for x in model.world]
    rows=[]
    for s,x in states:
        row=[]
        for sp,xp in states:
            k=Fraction(0)
            for a,ap in zip(model.actions,model.alpha[s,x]):
                if a not in model.feasible[s,x]: continue
                k+=ap*model.P[s,x,a][model.world.index(xp)]*model.U[s,x,a,xp][model.strategic.index(sp)]
            row.append(k)
        assert sum(row,Fraction(0))==1
        rows.append(tuple(row))
    return tuple(rows)


def compare_strategic_intervention(baseline:FiniteWorld, treated:FiniteWorld, changed: str)->dict:
    """Held-fixed inventory gate; never concludes that an effect is constitutive."""
    if changed not in ('alpha','U','alpha+U'):
        raise AppError('INTERVENTION_TYPE','only strategic generator alpha/U interventions supported')
    for k in ('strategic','world','actions','feasible','P'):
        if getattr(baseline,k)!=getattr(treated,k):
            raise AppError('HELD_FIXED',f'{k} changed across strategic intervention')
    if 'alpha' not in changed and baseline.alpha!=treated.alpha:
        raise AppError('HELD_FIXED','alpha changed without declaration')
    if 'U' not in changed and baseline.U!=treated.U:
        raise AppError('HELD_FIXED','U changed without declaration')
    return {'format':'Permansson.App.StrategicInterventionCheck.v1','target':changed,
            'baseline_semantic_identity':baseline.semantic_id(),'treated_semantic_identity':treated.semantic_id(),
            'held_fixed':['states','actions','feasible','P']}
