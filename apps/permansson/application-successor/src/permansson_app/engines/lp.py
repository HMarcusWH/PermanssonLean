"""Bounded exact rational LP candidate generator, not an infeasibility oracle.

The independent certificate checker lives in receipts.lp and never imports this
module. No approximate solver output is promoted without a checked dual gap.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
import math
import time
from ..errors import AppError
from ..identity import rational_text
from .lp_types import LP


def solve_equalities(A:tuple[tuple[Fraction,...],...],b:tuple[Fraction,...]):
    """Unique exact rational solution of n square equations; singular -> None."""
    n=len(b)
    if len(A)!=n or any(len(row)!=n for row in A): raise ValueError('square system required')
    t=[list(row)+[b[i]] for i,row in enumerate(A)]
    for k in range(n):
        pivot=next((i for i in range(k,n) if t[i][k]),None)
        if pivot is None:return None
        t[k],t[pivot]=t[pivot],t[k]
        a=t[k][k]
        t[k]=[v/a for v in t[k]]
        for j in range(n):
            if j==k:continue
            a=t[j][k]
            if a:
                t[j]=[v-a*w for v,w in zip(t[j],t[k])]
    return tuple(t[i][-1] for i in range(n))


def _vertex_best(A,b,c,*,max_combinations:int,deadline:float):
    n=len(c)
    if n==0:return tuple()
    if math.comb(len(A)+n,n)>max_combinations:
        raise AppError('LP_RESOURCE','vertex enumeration exceeds combination budget')
    I=[tuple(Fraction(int(i==j)) for j in range(n)) for i in range(n)]
    faces=list(A)+[tuple(-a for a in row) for row in I]
    limits=list(b)+[Fraction(0)]*n
    best=None;best_value=None
    for idx in combinations(range(len(faces)),n):
        if time.monotonic()>deadline:
            raise AppError('LP_RESOURCE','candidate enumeration deadline exceeded')
        x=solve_equalities(tuple(faces[i] for i in idx),tuple(limits[i] for i in idx))
        if x is None or any(sum((a*t for a,t in zip(row,x)),Fraction(0))>rhs for row,rhs in zip(faces,limits)):
            continue
        value=sum((a*t for a,t in zip(c,x)),Fraction(0))
        if best_value is None or value>best_value:
            best,best_value=x,value
    return best


def propose_lp_optimum(lp:LP,*,max_combinations:int=50000,seconds:float=4.0)->dict:
    """Return an independently checkable candidate, or an inconclusive status.

    Even if no vertex was found, never assert infeasibility: a Farkas witness
    must be explicitly supplied and independently checked for that conclusion.
    """
    if type(max_combinations) is not int or not 1<=max_combinations<=100000 or seconds<=0 or seconds>30:
        raise AppError('LP_RESOURCE','invalid resource budget')
    deadline=time.monotonic()+seconds
    try:
        x=_vertex_best(lp.A,lp.b,lp.c,max_combinations=max_combinations,deadline=deadline)
        if x is None:
            return {'status':'NO_CERTIFICATE_FOUND','reason':'no primal vertex located; infeasibility NOT established'}
        # Dual min b^T y s.t. A^T y>=c and y>=0. Treat as max -b^T y.
        m=len(lp.A)
        dual_A=tuple(tuple(-row[j] for row in lp.A) for j in range(len(lp.variables)))
        dual_b=tuple(-v for v in lp.c)
        y=_vertex_best(dual_A,dual_b,tuple(-v for v in lp.b),max_combinations=max_combinations,deadline=deadline)
        if y is None:return {'status':'NO_CERTIFICATE_FOUND','reason':'no feasible exact dual vertex'}
        objective=sum((a*(t+l) for a,t,l in zip(lp.coeffs,x,lp.lower)),Fraction(0))
        receipt={'format':'Permansson.App.LPOptimalReceipt.v1','model_semantic_identity':lp.semantic_id(),
                 'primal':[rational_text(t+l) for t,l in zip(x,lp.lower)],
                 'dual':[rational_text(v) for v in y], 'objective_value':rational_text(objective)}
        from ..receipts.lp import check_lp_certificate
        check_lp_certificate(lp,receipt)
        return {'status':'CHECKED_OPTIMAL_CANDIDATE','receipt':receipt}
    except AppError as exc:
        if exc.code=='LP_RESOURCE':
            return {'status':'RESOURCE_LIMIT','reason':str(exc)}
        raise
