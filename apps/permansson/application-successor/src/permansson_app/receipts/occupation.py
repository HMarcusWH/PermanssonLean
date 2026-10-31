"""Independent finite-class certificate consumer (no occupation producer import)."""
from __future__ import annotations
from hashlib import sha256
from fractions import Fraction
from ..finite_world import FiniteWorld,exact_ratio
from ..identity import canonical_bytes
from ..errors import AppError

_FORMAT='Permansson.App.FiniteOccupationReceipt.v1'
_KEYS={'format','model_semantic_identity','joint_states','bottom_classes','stationary_laws',
       'absorption_weights','expected_limit_laws','limit_interpretation','lean_status',
       'empirical_identification','scientific_claims_verified'}


def _actual_matrix(model):
    pairs=[(s,x) for s in model.strategic for x in model.world]
    result=[]
    # Independent reification; no access to producer's induced_kernel implementation.
    for s,x in pairs:
        row=[]
        for sp,xp in pairs:
            total=Fraction(0)
            for a in model.feasible[s,x]:
                total += model.alpha[s,x][model.actions.index(a)] * model.P[s,x,a][model.world.index(xp)] * model.U[s,x,a,xp][model.strategic.index(sp)]
            row.append(total)
        if sum(row)!=1:raise AppError('OCCUPATION_SOURCE','induced matrix row not stochastic')
        result.append(row)
    return result


def _closed_communicating(K):
    n=len(K)
    reach=[[i==j or K[i][j]>0 for j in range(n)] for i in range(n)]
    for mid in range(n):
        for i in range(n):
            if reach[i][mid]:
                for j in range(n):reach[i][j] |= reach[mid][j]
    assigned=set();closed=[]
    for i in range(n):
        if i in assigned:continue
        group={j for j in range(n) if reach[i][j] and reach[j][i]}
        assigned |= group
        if all(K[j][k]==0 for j in group for k in range(n) if k not in group):
            closed.append(tuple(sorted(group)))
    return sorted(closed)


def check_occupation(model:FiniteWorld, receipt:object):
    if type(receipt) is not dict or set(receipt)!=_KEYS or receipt.get('format')!=_FORMAT:
        raise AppError('OCCUPATION_RECEIPT','wrong receipt shape')
    if receipt['model_semantic_identity']!=model.semantic_id():
        raise AppError('OCCUPATION_RECEIPT','foreign model identity')
    if receipt['lean_status']!='NOT_EXECUTED' or receipt['empirical_identification']!='NOT_IDENTIFIED' or receipt['scientific_claims_verified'] is not False:
        raise AppError('OCCUPATION_RECEIPT','unsupported certification claim')
    if receipt['limit_interpretation']!='RANDOM_CLASS_STATIONARY_LAW_NOT_ITS_MEAN':
        raise AppError('OCCUPATION_RECEIPT','realized random law was confused with mean')
    pairs=[(s,x) for s in model.strategic for x in model.world]
    if receipt['joint_states'] != [{'strategic':s,'world':x} for s,x in pairs]:
        raise AppError('OCCUPATION_RECEIPT','wrong joint state order')
    K=_actual_matrix(model)
    n=len(K)
    expected=_closed_communicating(K)
    classes=receipt['bottom_classes']
    if classes!=[list(c) for c in expected]:
        raise AppError('OCCUPATION_RECEIPT','bottom classes incomplete/incorrect')
    c=len(classes)
    raw_laws=receipt['stationary_laws'];raw_weights=receipt['absorption_weights'];raw_mean=receipt['expected_limit_laws']
    if type(raw_laws) is not list or len(raw_laws)!=c or type(raw_weights) is not list or len(raw_weights)!=n or type(raw_mean) is not list or len(raw_mean)!=n:
        raise AppError('OCCUPATION_RECEIPT','dimension mismatch')
    laws=[]
    for group,raw in zip(classes,raw_laws):
        if type(raw) is not list or len(raw)!=len(group):raise AppError('OCCUPATION_RECEIPT','stationary length mismatch')
        vals=[exact_ratio(v,probability=True) for v in raw]
        if sum(vals)!=1 or any(v<=0 for v in vals):raise AppError('OCCUPATION_RECEIPT','stationary distribution invalid')
        if any(sum(vals[k]*K[group[k]][state] for k in range(len(group)))!=vals[j] for j,state in enumerate(group)):
            raise AppError('OCCUPATION_RECEIPT','stationarity fails')
        laws.append(vals)
    weights=[]
    for i,raw in enumerate(raw_weights):
        if type(raw) is not list or len(raw)!=c:raise AppError('OCCUPATION_RECEIPT','absorption length mismatch')
        v=[exact_ratio(x,probability=True) for x in raw]
        if sum(v)!=1:raise AppError('OCCUPATION_RECEIPT','absorption not normalized')
        for j,group in enumerate(classes):
            if i in group and v[j]!=1:raise AppError('OCCUPATION_RECEIPT','closed class boundary wrong')
            if i not in group and any(i in other for other in classes) and v[j]!=0:
                raise AppError('OCCUPATION_RECEIPT','foreign class boundary wrong')
        weights.append(v)
    for i in range(n):
        for j in range(c):
            if weights[i][j]!=sum(K[i][k]*weights[k][j] for k in range(n)):
                raise AppError('OCCUPATION_RECEIPT','absorption harmonic equation fails')
        raw=raw_mean[i]
        if type(raw) is not list or len(raw)!=n:raise AppError('OCCUPATION_RECEIPT','expected law dimensions wrong')
        mean=[exact_ratio(v,probability=True) for v in raw]
        if sum(mean)!=1:raise AppError('OCCUPATION_RECEIPT','expected law mass invalid')
        for k in range(n):
            expected_p=sum((weights[i][j]*laws[j][group.index(k)] for j,group in enumerate(classes) if k in group),Fraction(0))
            if mean[k]!=expected_p:
                raise AppError('OCCUPATION_RECEIPT','expected law not mixture of random class laws')
    return {'format':'Permansson.App.IndependentOccupationCheck.v1','status':'PASS',
            'checked_states':n,'bottom_classes':c,'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'EXACT_FINITE_CHAIN_NUMERIC_ONLY'}
