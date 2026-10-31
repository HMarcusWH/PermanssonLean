"""Exact classwise nonlinear occupation objective for a bounded stationary-policy class.

The objective is E[F(nu_infinity)] = sum_C Pr(reach C) F(nu_C), NOT
F(E[nu_infinity]). The strategic selection policy is enumerated over every
feasible deterministic stationary action map. P and U stay fixed.

This implementation supplies a numeric certificate, not a Lean theorem,
structural identification, or an unrestricted policy optimum.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from math import prod
from types import MappingProxyType
from ..errors import AppError
from ..finite_world import FiniteWorld,parse_finite_world,exact_ratio,exact_result
from ..identity import rational_text,semantic_identity
from .occupation import compute_occupation

FORMAT='Permansson.App.NonlinearStationaryRequest.v1'
RECEIPT='Permansson.App.NonlinearStationaryReceipt.v1'
FUNCTIONAL='boolean_one_minus_abs_p_minus_two_thirds.v1'
POLICY_CLASS='all_feasible_deterministic_stationary_selectors'
MAX_POLICIES=64
MAX_JOINT_STATES=8


def parse_nonlinear(raw:object):
    if type(raw) is not dict or set(raw)!={'format','model','descriptor_true_states','initial_law','functional_id','policy_class'} or raw['format']!=FORMAT:
        raise AppError('NONLINEAR_INPUT','unsupported nonlinear request envelope')
    if raw['functional_id']!=FUNCTIONAL or raw['policy_class']!=POLICY_CLASS:
        raise AppError('NONLINEAR_SCOPE','only the frozen Boolean functional and deterministic stationary policy class are supported')
    model=parse_finite_world(raw['model'])
    pairs=tuple((s,x) for s in model.strategic for x in model.world)
    if len(pairs)>MAX_JOINT_STATES:
        raise AppError('NONLINEAR_SCOPE','too many joint states')
    pred=raw['descriptor_true_states']
    if type(pred) is not list or not pred or len(pred)>len(pairs):
        raise AppError('NONLINEAR_DESCRIPTOR','descriptor states must be nonempty and bounded')
    truth=[]
    for pair in pred:
        if type(pair) is not list or len(pair)!=2 or any(type(a) is not str for a in pair) or tuple(pair) not in pairs or tuple(pair) in truth:
            raise AppError('NONLINEAR_DESCRIPTOR','descriptor includes foreign or repeated joint state')
        truth.append(tuple(pair))
    initial=raw['initial_law']
    if type(initial) is not list or len(initial)!=len(pairs):
        raise AppError('NONLINEAR_INITIAL','initial law must have exactly one entry per joint state')
    masses=[]
    for entry,expected in zip(initial,pairs):
        if type(entry) is not dict or set(entry)!={'state','mass'} or entry['state']!=list(expected):
            raise AppError('NONLINEAR_INITIAL','initial law states out of order or incomplete')
        masses.append(exact_ratio(entry['mass'],probability=True))
    if sum(masses,Fraction(0))!=1:raise AppError('NONLINEAR_INITIAL','initial law must sum to one')
    policies=prod(len(model.feasible[state]) for state in pairs)
    if policies>MAX_POLICIES:
        raise AppError('NONLINEAR_POLICY_RESOURCE','all feasible policies exceed exact enumeration budget')
    return model,pairs,tuple(truth),tuple(masses)


def boolean_target_score(p:Fraction)->Fraction:
    if not 0<=p<=1:raise AppError('NONLINEAR_SCORE','Boolean descriptor mass outside [0,1]')
    return Fraction(1)-abs(p-Fraction(2,3))


def policy_world(model:FiniteWorld,pairs,selected):
    alpha={}
    for state,action in zip(pairs,selected):
        if action not in model.feasible[state]:raise AppError('NONLINEAR_POLICY','selected action infeasible')
        alpha[state]=tuple(Fraction(int(a==action)) for a in model.actions)
    return FiniteWorld(model.strategic,model.world,model.actions,model.feasible,
                       MappingProxyType(alpha),model.P,model.U)


def propose_nonlinear(raw:object)->dict:
    m,pairs,truth,initial=parse_nonlinear(raw)
    output=[]
    for selected in product(*(m.feasible[pair] for pair in pairs)):
        world=policy_world(m,pairs,selected)
        occ=compute_occupation(world)
        class_probs=[];class_scores=[]
        for c,law in zip(occ['bottom_classes'],occ['stationary_laws']):
            p=sum((exact_result(mass) for idx,mass in zip(c,law) if pairs[idx] in truth),Fraction(0))
            class_probs.append(p)
            class_scores.append(boolean_target_score(p))
        weights=[sum((initial[i]*exact_result(row[j]) for i,row in enumerate(occ['absorption_weights'])),Fraction(0))
                 for j in range(len(class_scores))]
        score=sum((w*v for w,v in zip(weights,class_scores)),Fraction(0))
        # For diagnostics only. Not the optimization functional.
        barycenter_p=sum((w*p for w,p in zip(weights,class_probs)),Fraction(0))
        output.append({'index':len(output),'selected_actions':list(selected),
                       'model_semantic_identity':world.semantic_id(),
                       'occupation_receipt':occ,
                       'class_descriptor_masses':[rational_text(p) for p in class_probs],
                       'class_functional_values':[rational_text(v) for v in class_scores],
                       'initial_class_weights':[rational_text(w) for w in weights],
                       'expected_classwise_score':rational_text(score),
                       'functional_of_expected_descriptor':rational_text(boolean_target_score(barycenter_p))})
    best=max(exact_result(row['expected_classwise_score']) for row in output)
    ties=[row['index'] for row in output if exact_result(row['expected_classwise_score'])==best]
    return {'format':RECEIPT,'request_identity':semantic_identity('finite-nonlinear-stationary',raw),
            'baseline_identity':m.semantic_id(),'functional_id':FUNCTIONAL,
            'policy_class':POLICY_CLASS,'initial_law':[rational_text(v) for v in initial],
            'descriptor_true_states':[list(pair) for pair in truth],
            'policies':output,'policy_count':len(output),
            'optimum_value':rational_text(best),'attaining_policy_indices':ties,
            'representative_index':ties[0],
            'aggregation_order':'EXPECTATION_OF_CLASSWISE_FUNCTIONAL',
            'comparison_scope':'COMPLETE_BOUNDED_FEASIBLE_DETERMINISTIC_STATIONARY_CLASS',
            'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
