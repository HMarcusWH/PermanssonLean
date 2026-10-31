"""Independent original-atom and finite-horizon checker for quotient receipts.

Do not import the quotient producer's Markov matrix, projected-kernel or
finite-event computation functions. Reject a result not grounded in ALL fibers.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..identity import canonical_bytes, rational_text
from ..engines.quotients import parse_quotient, RECEIPT, MAX_RESULT_BITS


def _bound(values):
    if any(max(v.numerator.bit_length(),v.denominator.bit_length())>MAX_RESULT_BITS for v in values):
        raise AppError('QUOTIENT_RESOURCE','independent rational bit limit exceeded')


def _direct_joint(model,states):
    matrix=[]
    for s,x in states:
        probs=[]
        for sp,xp in states:
            out=Fraction(0)
            for a in model.feasible[s,x]:
                ai=model.actions.index(a)
                out+=model.alpha[s,x][ai]*model.P[s,x,a][model.world.index(xp)]*model.U[s,x,a,xp][model.strategic.index(sp)]
            probs.append(out)
        if sum(probs,Fraction(0)) != 1:
            raise AppError('QUOTIENT_RECEIPT','nonstochastic original atom rows')
        _bound(probs)
        matrix.append(tuple(probs))
    return tuple(matrix)


def _independently_project(fine,groups):
    result=[]
    for source_group in groups:
        all_rows=[]
        for i in source_group:
            all_rows.append(tuple(sum((fine[i][j] for j in dest),Fraction(0)) for dest in groups))
        if any(row != all_rows[0] for row in all_rows[1:]):
            raise AppError('QUOTIENT_RECEIPT','intervention not strongly lumpable')
        if sum(all_rows[0],Fraction(0))!=1:
            raise AppError('QUOTIENT_RECEIPT','invalid quotient probability row')
        result.append(all_rows[0])
    return tuple(result)


def _independent_survival(matrix,inside,indices,horizon,typ):
    allowed=set(inside)
    vec=[Fraction(int(j in allowed)) for j in range(len(matrix))]
    for _ in range(horizon):
        new=[]
        for i in range(len(matrix)):
            total=Fraction(0)
            if i in allowed:
                for j in range(len(matrix)):
                    if j in allowed:total+=matrix[i][j]*vec[j]
            new.append(total)
        vec=new
        _bound(vec)
    return tuple(vec[i] if typ=='survival_horizon' else 1-vec[i] for i in indices)


def check_quotient(raw:object,receipt:object)->dict:
    q=parse_quotient(raw)
    if type(receipt) is not dict or receipt.get('format') != RECEIPT:
        raise AppError('QUOTIENT_RECEIPT','foreign receipt format')
    expected_profiles=[]
    for name,target,model in [('baseline','baseline',q.baseline),*q.interventions]:
        matrix=_direct_joint(model,q.fine_states)
        projected=_independently_project(matrix,q.fibers)
        vals=_independent_survival(matrix,q.region,q.comparison,q.horizon,q.value_type)
        coarse_vals=_independent_survival(projected,q.coarse_region,q.coarse_comparison,q.horizon,q.value_type)
        for i,f in enumerate(q.comparison):
            if vals[i]!=coarse_vals[q.coarse_comparison.index(q.coarse_index[f])]:
                raise AppError('QUOTIENT_RECEIPT','original and coarse finite-event properties disagree')
        expected_profiles.append({'id':name,'target':target,'source_identity':model.semantic_id(),
            'coarse_kernel':[[rational_text(v) for v in row] for row in projected],
            'fine_values':[rational_text(v) for v in vals],
            'coarse_values':[rational_text(v) for v in coarse_vals]})
    zero_f=tuple(Fraction(x) for x in expected_profiles[0]['fine_values'])
    zero_c=tuple(Fraction(x) for x in expected_profiles[0]['coarse_values'])
    effects=[{'id':row['id'],
              'fine_differences':[rational_text(Fraction(x)-v) for x,v in zip(row['fine_values'],zero_f)],
              'coarse_differences':[rational_text(Fraction(x)-v) for x,v in zip(row['coarse_values'],zero_c)]}
             for row in expected_profiles[1:]]
    expected={'format':RECEIPT,'request_identity':q.identity,'baseline_identity':q.baseline.semantic_id(),
        'fine_state_order':[list(p) for p in q.fine_states],
        'coarse_state_order':[list(p) for p in q.coarse_states],
        'fine_to_coarse_indices':list(q.coarse_index),
        'region_fine_indices':list(q.region),'region_coarse_indices':list(q.coarse_region),
        'comparison_fine_indices':list(q.comparison),'comparison_coarse_indices':list(q.coarse_comparison),
        'horizon':q.horizon,'value_type':q.value_type,'profiles':expected_profiles,'effects':effects,
        'verified_law_scope':'TYPE_RESPECTING_INDUCED_MARKOV_QUOTIENT_NOT_COARSE_ALPHA_P_U',
        'comparison_scope':'FULL_FIBERS_ALL_DECLARED_INTERVENTIONS',
        'claim_scope':'FINITE_NUMERIC_TRANSPORT_ONLY_NOT_EXACT_GR_PR',
        'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False}
    try:
        if canonical_bytes(receipt)!=canonical_bytes(expected):
            raise AppError('QUOTIENT_RECEIPT','source, all fibers, kernel, effects or scientific status changed')
    except (ValueError,TypeError,UnicodeError) as e:
        raise AppError('QUOTIENT_RECEIPT','invalid JSON receipt') from e
    return {'format':'Permansson.App.IndependentQuotientCheck.v1','status':'PASS',
            'verified_profiles':len(expected_profiles), 'checked_fibers':len(q.fibers),
            'comparison_fine_states':len(q.comparison),
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'FINITE_INDUCED_LAW_NUMERIC_ONLY'}
