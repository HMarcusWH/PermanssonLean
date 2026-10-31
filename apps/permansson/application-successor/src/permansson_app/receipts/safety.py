"""Independent exact checker for finite controlled-invariant pruning receipts.

Deliberately does not import the producer's pruning/support routines.
"""
from __future__ import annotations
from hashlib import sha256
from ..errors import AppError
from ..identity import canonical_bytes
from ..engines.safety import SafetyProblem, RECEIPT

_FIELDS = {'format','problem_semantic_identity','model_semantic_identity','joint_states',
           'initial_safe_indices','descending_pruning_chain','core_indices',
           'stationary_witness_actions','scope','outside_core',
           'baseline_alpha_policy_optimized_over','lean_status','empirical_identification',
           'scientific_claims_verified'}


def check_safety_core(problem: SafetyProblem, receipt: object) -> dict:
    if type(receipt) is not dict or set(receipt) != _FIELDS or receipt['format'] != RECEIPT:
        raise AppError('SAFETY_RECEIPT','incomplete/foreign safety certificate')
    m = problem.model
    states = [(s,x) for s in m.strategic for x in m.world]
    expected = {
      'problem_semantic_identity':problem.identity,
      'model_semantic_identity':m.semantic_id(),
      'joint_states':[{'strategic':s,'world':x} for s,x in states],
      'initial_safe_indices':list(problem.safe_indices),
      'scope':'GREATEST_ALMOST_SURE_CONTROLLED_INVARIANT_SUBSET',
      'outside_core':'NOT_ALMOST_SURE_SAFE_NO_ZERO_SURVIVAL_PROBABILITY_INFERRED',
      'baseline_alpha_policy_optimized_over':True,
      'lean_status':'NOT_EXECUTED',
      'empirical_identification':'NOT_IDENTIFIED',
      'scientific_claims_verified':False,
    }
    for key,val in expected.items():
        if type(val) is bool:
            if receipt[key] is not val:
                raise AppError('SAFETY_RECEIPT',f'{key}: scientific status/flag mismatch')
        elif receipt[key] != val:
            raise AppError('SAFETY_RECEIPT',f'{key}: source or scope mismatch')
    chain = receipt['descending_pruning_chain']
    if type(chain) is not list or not 2 <= len(chain) <= len(problem.safe_indices) + 2:
        raise AppError('SAFETY_RECEIPT','invalid pruning-chain length')
    core = set(problem.safe_indices)
    if chain[0] != sorted(core):
        raise AppError('SAFETY_RECEIPT','wrong starting region')
    for step in range(1,len(chain)):
        keep=set()
        for i in core:
            s,x = states[i]
            for a in m.feasible[s,x]:
                # Compute full P/U product rather than relying on producer support.
                excluded_mass = sum((m.P[s,x,a][m.world.index(xp)] *
                      m.U[s,x,a,xp][m.strategic.index(sp)] for j,(sp,xp) in enumerate(states)
                      if j not in core),start=0)
                if excluded_mass == 0:
                    keep.add(i)
                    break
        if type(chain[step]) is not list or chain[step] != sorted(keep):
            raise AppError('SAFETY_RECEIPT',f'pruning step {step} is not maximal/exact')
        if core == keep and step != len(chain) - 1:
            raise AppError('SAFETY_RECEIPT','extraneous iterations after stabilization')
        core=keep
    if chain[-1] != chain[-2] or receipt['core_indices'] != sorted(core):
        raise AppError('SAFETY_RECEIPT','missing final fixed-point witness')
    witness = receipt['stationary_witness_actions']
    if type(witness) is not list or len(witness) != len(core):
        raise AppError('SAFETY_RECEIPT','wrong number of stationary witnesses')
    seen=set()
    for w in witness:
        if type(w) is not dict or set(w) != {'state_index','action'} or type(w['state_index']) is not int:
            raise AppError('SAFETY_RECEIPT','malformed policy witness')
        i,a = w['state_index'],w['action']
        if i not in core or i in seen or type(a) is not str:
            raise AppError('SAFETY_RECEIPT','foreign/duplicate policy witness')
        seen.add(i)
        s,x=states[i]
        if a not in m.feasible[s,x]:
            raise AppError('SAFETY_RECEIPT','inadmissible witness action')
        mass = sum((m.P[s,x,a][m.world.index(xp)] * m.U[s,x,a,xp][m.strategic.index(sp)]
             for j,(sp,xp) in enumerate(states) if j not in core),start=0)
        if mass != 0:
            raise AppError('SAFETY_RECEIPT','witness has positive leakage probability')
    return {'format':'Permansson.App.IndependentSafetyCoreCheck.v1','status':'PASS',
            'joint_states':len(states),'pruning_steps':len(chain)-1,
            'core_states':len(core),'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'ALMOST_SURE_CONTROLLED_INVARIANT_NUMERIC_ONLY'}
