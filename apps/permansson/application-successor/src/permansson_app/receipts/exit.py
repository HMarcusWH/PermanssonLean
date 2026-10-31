"""Independent, exact first-exit and never-exit certificate checker."""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import FiniteWorld,exact_result
from ..identity import canonical_bytes
from ..engines.exit import Region
from .occupation import _actual_matrix,_closed_communicating

_KEYS={'format','model_semantic_identity','region_semantic_identity','region_indices',
       'outside_indices','horizon','initial_inside_only','rows','lean_status',
       'empirical_identification','scientific_claims_verified'}


def check_exit(model:FiniteWorld,region:Region,receipt:object):
    if type(receipt) is not dict or set(receipt)!=_KEYS or receipt.get('format')!='Permansson.App.FiniteExitReceipt.v1':
        raise AppError('EXIT_RECEIPT','invalid first-exit receipt shape')
    if receipt['model_semantic_identity']!=model.semantic_id() or receipt['region_semantic_identity']!=region.semantic_id:
        raise AppError('EXIT_RECEIPT','foreign model or region identity')
    if receipt['lean_status']!='NOT_EXECUTED' or receipt['empirical_identification']!='NOT_IDENTIFIED' or receipt['scientific_claims_verified'] is not False:
        raise AppError('EXIT_RECEIPT','unsupported formal or empirical claim')
    K=_actual_matrix(model);n=len(K)
    B=region.joint_indices;outside=[i for i in range(n) if i not in B]
    if receipt['region_indices']!=list(B) or receipt['outside_indices']!=outside or type(receipt['horizon']) is not int or receipt['horizon']!=region.horizon or receipt['initial_inside_only'] is not True:
        raise AppError('EXIT_RECEIPT','scope and horizon mismatch')
    rows=receipt['rows']
    if type(rows) is not list or len(rows)!=len(B):raise AppError('EXIT_RECEIPT','row set incomplete')
    validated={}
    for index,source in enumerate(B):
        row=rows[index]
        if type(row) is not dict or set(row)!={'start_index','survival_through','first_exit_by_step_and_destination','eventual_exit_by_destination','never_exit'} or type(row['start_index']) is not int or row['start_index']!=source:
            raise AppError('EXIT_RECEIPT','missing or duplicated source state')
        survival=row['survival_through'];exits=row['first_exit_by_step_and_destination']
        if type(survival) is not list or len(survival)!=region.horizon+1 or type(exits) is not list or len(exits)!=region.horizon:
            raise AppError('EXIT_RECEIPT','finite horizon dimensions do not match')
        p={i:Fraction(int(i==source)) for i in B}
        if exact_result(survival[0],probability=True)!=1:
            raise AppError('EXIT_RECEIPT','zero-step survival must equal one')
        exit_totals=[Fraction(0) for _ in outside]
        for t in range(region.horizon):
            if type(exits[t]) is not list or len(exits[t])!=len(outside):
                raise AppError('EXIT_RECEIPT','finite exit destination dimensions wrong')
            exit_step=[sum((p[i]*K[i][j] for i in B),Fraction(0)) for j in outside]
            if [exact_result(q,probability=True) for q in exits[t]]!=exit_step:
                raise AppError('EXIT_RECEIPT','first-exit time/destination equation false')
            exit_totals=[v+w for v,w in zip(exit_totals,exit_step)]
            p={j:sum((p[i]*K[i][j] for i in B),Fraction(0)) for j in B}
            v=sum(p.values(),Fraction(0))
            if exact_result(survival[t+1],probability=True)!=v:
                raise AppError('EXIT_RECEIPT','killed-kernel survival recurrence false')
            if v+sum(exit_totals)!=1:
                raise AppError('EXIT_RECEIPT','leakage mass not accounted for')
        raw_ever=row['eventual_exit_by_destination']
        if type(raw_ever) is not list or len(raw_ever)!=len(outside):raise AppError('EXIT_RECEIPT','eventual exit destinations incomplete')
        ever=[exact_result(q,probability=True) for q in raw_ever]
        never=exact_result(row['never_exit'],probability=True)
        if sum(ever,Fraction(0))+never!=1 or any(ever[j]<exit_totals[j] for j in range(len(outside))):
            raise AppError('EXIT_RECEIPT','eventual exit/never mass wrong')
        validated[source]=ever+[never]
    # Exact harmonic boundary equations for eventual exit and non-exit. Uniqueness
    # follows from all non-absorbing states being transient in a *finite* chain.
    all_bottom=_closed_communicating(K)
    safe_closed={i for c in all_bottom if set(c)<=set(B) for i in c}
    for j in safe_closed:
        if validated[j]!=[Fraction(0)]*len(outside)+[Fraction(1)]:
            raise AppError('EXIT_RECEIPT','inside recurrent boundary must never exit')
    for i in B:
        if i in safe_closed:continue
        # For outside j, eventual first exit from that state is immediate by definition.
        for c in range(len(outside)+1):
            expected = sum((K[i][j]*(Fraction(int(outside.index(j)==c)) if c<len(outside) else Fraction(0)) for j in outside),Fraction(0))
            expected += sum((K[i][j]*validated[j][c] for j in B),Fraction(0))
            if validated[i][c]!=expected:
                raise AppError('EXIT_RECEIPT','eventual first-step harmonic equation false')
    return {'format':'Permansson.App.IndependentExitCheck.v1','status':'PASS',
            'checked_starts':len(B),'steps':region.horizon,
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'EXACT_FINITE_CHAIN_NUMERIC_ONLY'}
