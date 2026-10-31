"""Nine-axis evidence report, disallowing implicit scientific promotion."""
from __future__ import annotations
from dataclasses import dataclass
from .errors import AppError
from .versioning import SourcePin
from .identity import semantic_identity

DIMENSIONS=('scope','source','model','premises','numeric','lean','independent_review','empirical','publication')
STATES={'UNASSESSED','SUPPORTED','CONTRADICTED','BLOCKED','NOT_APPLICABLE'}


def scientific_report(source:SourcePin,capability:str,scope_identity:dict,assessments:dict|None=None)->dict:
    if type(source) is not SourcePin or type(capability) is not str or not capability:
        raise AppError('REPORT_INPUT','typed source and capability required')
    if type(scope_identity) is not dict or set(scope_identity)!={'profile','sha256'}:
        raise AppError('REPORT_INPUT','typed scope semantic identity required')
    if assessments is not None and type(assessments) is not dict:
        raise AppError('REPORT_INPUT','assessment dimensions must be an object')
    findings=dict(assessments or {})
    if not set(findings).issubset(DIMENSIONS) or any(v not in STATES for v in findings.values()):
        raise AppError('REPORT_STATUS','unknown scientific certificate dimension')
    # The report is an evidence index; even all nine SUPPORTED are not release authorization.
    result={d:findings.get(d,'UNASSESSED') for d in DIMENSIONS}
    return {'format':'Permansson.App.ScientificEvidenceReport.v1',
            'source':source.to_dict(),'capability':capability,'scope_identity':scope_identity,
            'scientific_certificate_dimensions':result,'scientific_claims_verified':False,
            'lean_receipt_verified':False,'independent_math_certified':False,
            'application_release_authorized':False,'empirical_identification':False,
            'status':'ASSESSMENT_ONLY_NOT_RELEASE'}
