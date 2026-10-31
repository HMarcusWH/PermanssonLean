"""Independent exact primal/dual and Farkas verifier; never imports LP solver.

Certificates apply only to the actual affine-normalized original LP. They do not
infer equality with any separate solver's chosen controller or policy.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..engines.lp_types import LP

OPTIMAL='Permansson.App.LPOptimalReceipt.v1'
INFEASIBLE='Permansson.App.LPFarkasReceipt.v1'


def _sum(values):return sum(values,Fraction(0))


def check_lp_certificate(lp:LP,receipt:object)->dict:
    if type(receipt) is not dict or set(receipt)!={'format','model_semantic_identity','primal','dual','objective_value'}:
        raise AppError('LP_CERT','malformed optimal certificate')
    if receipt['format']!=OPTIMAL or receipt['model_semantic_identity']!=lp.semantic_id():
        raise AppError('LP_CERT','foreign LP or wrong receipt type')
    x=receipt['primal'];y=receipt['dual']
    if type(x) is not list or type(y) is not list or len(x)!=len(lp.variables) or len(y)!=len(lp.A):
        raise AppError('LP_CERT','wrong primal/dual dimensions')
    x=tuple(exact_result(v) for v in x)
    z=tuple(a-l for a,l in zip(x,lp.lower))
    y=tuple(exact_result(v) for v in y)
    if any(v<0 for v in z) or any(v<0 for v in y):
        raise AppError('LP_CERT','primal or dual sign violation')
    if any(_sum(a*t for a,t in zip(row,z))>b for row,b in zip(lp.A,lp.b)):
        raise AppError('LP_CERT','primal inequality violation')
    if any(_sum(row[j]*t for row,t in zip(lp.A,y))<lp.c[j] for j in range(len(z))):
        raise AppError('LP_CERT','dual inequality violation')
    primal=_sum(a*t for a,t in zip(lp.c,z))
    dual=_sum(b*t for b,t in zip(lp.b,y))
    if primal!=dual:
        raise AppError('LP_CERT','nonzero primal-dual gap')
    claimed=exact_result(receipt['objective_value'])
    actual=(_sum(a*t for a,t in zip(lp.coeffs,x)))
    if claimed!=actual or claimed!=(primal+lp.offset)*(1 if lp.maximize else -1):
        raise AppError('LP_CERT','objective / affine inverse mapping disagreement')
    return {'format':'Permansson.App.LPIndependentCheck.v1','status':'OPTIMAL_VERIFIED',
            'certificate_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'original_objective':receipt['objective_value'],'proof_status':'NOT_EXECUTED'}


def check_farkas_certificate(lp:LP,receipt:object)->dict:
    if type(receipt) is not dict or set(receipt)!={'format','model_semantic_identity','multiplier'}:
        raise AppError('LP_FARKAS','malformed Farkas certificate')
    if receipt['format']!=INFEASIBLE or receipt['model_semantic_identity']!=lp.semantic_id():
        raise AppError('LP_FARKAS','wrong LP identity')
    y=receipt['multiplier']
    if type(y) is not list or len(y)!=len(lp.A):
        raise AppError('LP_FARKAS','wrong multiplier dimensions')
    y=tuple(exact_result(v) for v in y)
    if any(v<0 for v in y):
        raise AppError('LP_FARKAS','negative multiplier')
    if any(_sum(row[j]*yi for row,yi in zip(lp.A,y)) < 0 for j in range(len(lp.variables))):
        raise AppError('LP_FARKAS','Farkas coefficient nonnegativity fails')
    if _sum(yi*b for yi,b in zip(y,lp.b)) >=0:
        raise AppError('LP_FARKAS','Farkas right-hand side must be strictly negative')
    return {'format':'Permansson.App.LPIndependentCheck.v1', 'status':'INFEASIBILITY_VERIFIED',
            'certificate_sha256':sha256(canonical_bytes(receipt)).hexdigest(),'proof_status':'NOT_EXECUTED'}
