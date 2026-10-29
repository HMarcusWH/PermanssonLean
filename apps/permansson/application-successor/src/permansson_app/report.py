"""Scientific application status is orthogonal to numerical receipt verification."""
from __future__ import annotations
from hashlib import sha256
from .errors import AppError
from .identity import canonical_bytes

DIMENSIONS=('validity','epistemic_mode','selection_status','identification_status',
            'statistical_status','provenance_status','substantive_pr_status',
            'direction_status','uniform_gap_status')


def unassessed_scientific_dimensions() -> dict:
    """None means not evaluated in the *new* report; not a legacy enum extension."""
    return {field:None for field in DIMENSIONS}


def numeric_application_report(*, capability:str, model_semantic_identity:dict,
                               computation_receipt:dict, independent_check:dict,
                               source_ref:str|None=None)->dict:
    if type(capability) is not str or type(model_semantic_identity) is not dict:
        raise AppError('REPORT_SCOPE','missing bound capability and model')
    if type(independent_check) is not dict or independent_check.get('status') not in ('PASS','OPTIMAL_VERIFIED','INFEASIBILITY_VERIFIED','FINITE_SURVIVAL_TABLE_VERIFIED'):
        raise AppError('REPORT_EVIDENCE','independent numeric check is mandatory')
    if type(computation_receipt) is not dict:
        raise AppError('REPORT_EVIDENCE','actual receipt required')
    return {'format':'Permansson.App.ScientificReport.v2',
            'capability':capability,'model_semantic_identity':model_semantic_identity,
            'computation_receipt_sha256':sha256(canonical_bytes(computation_receipt)).hexdigest(),
            'independent_checker_receipt_sha256':sha256(canonical_bytes(independent_check)).hexdigest(),
            'source_commit':source_ref,'mathematical_implementation':'NUMERIC_ONLY',
            'numerical_verification':independent_check['status'],'kernel_checked_proof':'NOT_EXECUTED',
            'independent_mathematical_certification':'NOT_ASSESSED',
            'application_release_acceptance':'NOT_ASSESSED',
            'empirical_identification':'NOT_IDENTIFIED','publication_approval':'NOT_ASSESSED',
            'scientific_certificate_dimensions':unassessed_scientific_dimensions(),
            'scientific_claims_verified':False,
            'limitations':['Numerical results do not establish Exact GR or constitutive PR.',
                           'No Lean replay, independent mathematical certification or empirical identification.']}
