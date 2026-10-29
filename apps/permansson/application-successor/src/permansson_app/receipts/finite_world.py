"""Consumer-side finite-world equality checker; no producer algorithm import."""
from __future__ import annotations
from hashlib import sha256
from fractions import Fraction
from ..errors import AppError
from ..identity import canonical_bytes, rational_text
from ..finite_world import FiniteWorld, exact_ratio

FORMAT='Permansson.App.InducedKernelReceipt.v1'


def emit_finite_receipt(model:FiniteWorld)->dict:
    # Producer-only import remains inside producer function (checker does not use it).
    from ..finite_world import induced_kernel
    return {'format':FORMAT,
            'model_semantic_identity':model.semantic_id(),
            'states':[{'strategic':s,'world':x} for s in model.strategic for x in model.world],
            'kernel':[[rational_text(p) for p in row] for row in induced_kernel(model)],
            'scientific_claims_verified':False,
            'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED'}


def check_finite_receipt(model:FiniteWorld, receipt:object)->dict:
    if type(receipt) is not dict or set(receipt)!={'format','model_semantic_identity','states','kernel','scientific_claims_verified','lean_status','empirical_identification'}:
        raise AppError('FINITE_RECEIPT','wrong receipt fields')
    if receipt['format']!=FORMAT or receipt['model_semantic_identity']!=model.semantic_id():
        raise AppError('FINITE_RECEIPT','wrong format or bound model identity')
    if receipt['scientific_claims_verified'] is not False or receipt['lean_status']!='NOT_EXECUTED' or receipt['empirical_identification']!='NOT_IDENTIFIED':
        raise AppError('FINITE_RECEIPT','unauthorized proof or empirical promotion')
    states=[(s,x) for s in model.strategic for x in model.world]
    if receipt['states']!=[{'strategic':s,'world':x} for s,x in states]:
        raise AppError('FINITE_RECEIPT','state ordering differs')
    rows=receipt['kernel']
    n=len(states)
    if type(rows) is not list or len(rows)!=n or any(type(row) is not list or len(row)!=n for row in rows):
        raise AppError('FINITE_RECEIPT','matrix dimensions differ')
    for i,(s,x) in enumerate(states):
        for j,(sp,xp) in enumerate(states):
            supplied=exact_ratio(rows[i][j],probability=True)
            # Completely separate nested index path from the producer's matrix builder.
            total=Fraction(0)
            for a in model.feasible[s,x]:
                ai=model.actions.index(a)
                xi=model.world.index(xp)
                si=model.strategic.index(sp)
                total+=model.alpha[s,x][ai] * model.P[s,x,a][xi] * model.U[s,x,a,xp][si]
            if total != supplied:
                raise AppError('FINITE_RECEIPT',f'false induced-kernel atom at [{i},{j}]')
        if sum((exact_ratio(v,probability=True) for v in rows[i]),Fraction(0))!=1:
            raise AppError('FINITE_RECEIPT',f'nonstochastic induced row {i}')
    return {'format':'Permansson.App.IndependentNumericCheck.v1',
            'status':'PASS','checked_atoms':n*n,
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED', 'claim_status':'NUMERIC_EQUALITY_ONLY'}
