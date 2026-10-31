"""Independent nonlinear policy-class checker; never calls the nonlinear producer."""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from itertools import product
from types import MappingProxyType
from ..errors import AppError
from ..finite_world import FiniteWorld,exact_result
from ..identity import canonical_bytes,semantic_identity
from ..engines.nonlinear import (parse_nonlinear,FUNCTIONAL,POLICY_CLASS,RECEIPT)
from .occupation import check_occupation

_KEYS={'format','request_identity','baseline_identity','functional_id','policy_class',
       'initial_law','descriptor_true_states','policies','policy_count',
       'optimum_value','attaining_policy_indices','representative_index',
       'aggregation_order','comparison_scope','lean_status',
       'empirical_identification','scientific_claims_verified'}


def check_nonlinear(raw:object,receipt:object)->dict:
    base,pairs,truth,initial=parse_nonlinear(raw)
    if type(receipt) is not dict or set(receipt)!=_KEYS or receipt['format']!=RECEIPT:
        raise AppError('NONLINEAR_RECEIPT','incorrect envelope or missing field')
    fixed={
        'request_identity':semantic_identity('finite-nonlinear-stationary',raw),
        'baseline_identity':base.semantic_id(),
        'functional_id':FUNCTIONAL,'policy_class':POLICY_CLASS,
        'initial_law':[str(v.numerator) + ('/'+str(v.denominator) if v.denominator!=1 else '') for v in initial],
        'descriptor_true_states':[list(p) for p in truth],
        'aggregation_order':'EXPECTATION_OF_CLASSWISE_FUNCTIONAL',
        'comparison_scope':'COMPLETE_BOUNDED_FEASIBLE_DETERMINISTIC_STATIONARY_CLASS',
        'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False}
    for key,value in fixed.items():
        if type(value) is bool:
            if receipt[key] is not value:raise AppError('NONLINEAR_RECEIPT',f'{key} must not claim success')
        elif receipt[key]!=value:raise AppError('NONLINEAR_RECEIPT',f'{key} mismatch')
    policies=receipt['policies']
    all_selections=list(product(*(base.feasible[state] for state in pairs)))
    if type(policies) is not list or len(policies)!=len(all_selections) or type(receipt['policy_count']) is not int or receipt['policy_count']!=len(all_selections):
        raise AppError('NONLINEAR_RECEIPT','complete policy-class enumeration missing')
    scores=[]
    for index,(entry,selected) in enumerate(zip(policies,all_selections)):
        keys={'index','selected_actions','model_semantic_identity','occupation_receipt',
              'class_descriptor_masses','class_functional_values',
              'initial_class_weights','expected_classwise_score','functional_of_expected_descriptor'}
        if type(entry) is not dict or set(entry)!=keys or type(entry['index']) is not int or entry['index']!=index or entry['selected_actions']!=list(selected):
            raise AppError('NONLINEAR_RECEIPT','policy order or complete entry mismatch')
        # Independent policy reification: do not call the producer's
        # policy_world or induced transition calculator.
        independently_selected={}
        for state,chosen in zip(pairs,selected):
            independently_selected[state]=tuple(Fraction(int(a==chosen)) for a in base.actions)
        world=FiniteWorld(base.strategic,base.world,base.actions,base.feasible,
                          MappingProxyType(independently_selected),base.P,base.U)
        if entry['model_semantic_identity']!=world.semantic_id():
            raise AppError('NONLINEAR_RECEIPT','policy-controlled model identity mismatch')
        occ=entry['occupation_receipt']
        check_occupation(world,occ) # independent harmonic/stationary checks of source P/U
        c=occ['bottom_classes'];weights=[];ps=[];fs=[]
        if any(type(entry[k]) is not list or len(entry[k])!=len(c) for k in ('class_descriptor_masses','class_functional_values','initial_class_weights')):
            raise AppError('NONLINEAR_RECEIPT','classwise data incomplete')
        for j,group in enumerate(c):
            w=sum((initial[i]*exact_result(row[j],probability=True) for i,row in enumerate(occ['absorption_weights'])),Fraction(0))
            p=sum((exact_result(mass,probability=True) for idx,mass in zip(group,occ['stationary_laws'][j]) if pairs[idx] in truth),Fraction(0))
            value=1-abs(p-Fraction(2,3))
            if (exact_result(entry['initial_class_weights'][j],probability=True)!=w or
                exact_result(entry['class_descriptor_masses'][j],probability=True)!=p or
                exact_result(entry['class_functional_values'][j],probability=True)!=value):
                raise AppError('NONLINEAR_RECEIPT','wrong absorption/classwise functional data')
            weights.append(w);ps.append(p);fs.append(value)
        total=sum((w*f for w,f in zip(weights,fs)),Fraction(0))
        bary=1-abs(sum((w*p for w,p in zip(weights,ps)),Fraction(0))-Fraction(2,3))
        if exact_result(entry['expected_classwise_score'],probability=True)!=total or exact_result(entry['functional_of_expected_descriptor'],probability=True)!=bary:
            raise AppError('NONLINEAR_RECEIPT','functional order or expected score mismatch')
        scores.append(total)
    best=max(scores)
    tied=[i for i,v in enumerate(scores) if v==best]
    if (exact_result(receipt['optimum_value'],probability=True)!=best or receipt['attaining_policy_indices']!=tied or
        type(receipt['representative_index']) is not int or receipt['representative_index']!=tied[0]):
        raise AppError('NONLINEAR_RECEIPT','optimizer/tied policy set not complete')
    return {'format':'Permansson.App.IndependentNonlinearCheck.v1','status':'PASS',
            'policies_checked':len(scores),'classes_checked':sum(len(p['occupation_receipt']['bottom_classes']) for p in policies),
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'BOUNDED_STATIONARY_CLASS_NUMERIC_ONLY'}
