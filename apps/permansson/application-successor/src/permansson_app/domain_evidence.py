"""Source-first, non-executing research evidence import.

This import preserves observation and knowledge time; it NEVER infers an
identified strategic generator, a stochastic transition kernel, or a GR/PR proof.
"""
from __future__ import annotations
from datetime import datetime,timezone
from .errors import AppError
from .identity import canonical_bytes,semantic_identity

CASE_IDS=frozenset({'hormuz','russia-ukraine','iran-transition','iran-persistence','midr',
                    'brown-mackay','cross-conflict-geometry','gscrd-retrospective','gscrd-prospective'})
DATA_ROLES=frozenset({'observed_event','observability_only','source_claim','institutional_action',
                      'support_matrix','structural_assumption','parameter_draw','counterfactual_simulation',
                      'descriptive_measurement','documentary_source','outcome_observation'})
DEFAULT_STATUS='NOT_IDENTIFIED'


def _utc(value:object,scope:str)->datetime:
    if type(value) is not str or len(value)>48:
        raise AppError('DOMAIN_CHRONOLOGY',f'{scope}: timestamp must be ISO8601 UTC')
    try:dt=datetime.fromisoformat(value.replace('Z','+00:00'))
    except ValueError as exc:raise AppError('DOMAIN_CHRONOLOGY',f'{scope}: invalid ISO8601') from exc
    if dt.tzinfo is None or dt.utcoffset()!=timezone.utc.utcoffset(dt):
        raise AppError('DOMAIN_CHRONOLOGY',f'{scope}: UTC offset required')
    return dt


def _source(source:object)->dict:
    if type(source) is not dict or set(source)!={'source_id','sha256','published_at','source_role'}:
        raise AppError('DOMAIN_SOURCE','source has malformed metadata')
    if type(source['source_id']) is not str or not (1<=len(source['source_id'])<=128):
        raise AppError('DOMAIN_SOURCE','source_id required')
    val=source['sha256']
    if type(val) is not str or len(val)!=64 or any(c not in '0123456789abcdef' for c in val):
        raise AppError('DOMAIN_SOURCE','raw source SHA-256 required')
    _utc(source['published_at'],'published_at')
    if type(source['source_role']) is not str or source['source_role'] not in ('primary','secondary','research_derived','user_supplied','assumption'):
        raise AppError('DOMAIN_SOURCE','undeclared source role')
    return source


def validate_domain_evidence(input_document:object)->dict:
    if type(input_document) is not dict or set(input_document)!={'format','case_id','lane','freeze_at','evidence'} or input_document['format']!='Permansson.App.DomainEvidenceImport.v1':
        raise AppError('DOMAIN_FORMAT','unsupported evidence import format')
    if type(input_document['case_id']) is not str or input_document['case_id'] not in CASE_IDS:
        raise AppError('DOMAIN_CASE','unknown case identifier')
    if type(input_document['lane']) is not str or input_document['lane'] not in ('retrospective','prospective','assumption_conditional'):
        raise AppError('DOMAIN_LANE','unknown epistemic lane')
    freeze=_utc(input_document['freeze_at'],'freeze_at')
    entries=input_document['evidence']
    if type(entries) is not list or len(entries)>10000:raise AppError('DOMAIN_LIMIT','evidence record count exceeds limit')
    seen=set();accepted=[];late=0
    for row in entries:
        fields={'record_id','data_role','event_at','known_at','source','measurement_status','uncertainty','payload_sha256'}
        if type(row) is not dict or set(row)!=fields:
            raise AppError('DOMAIN_RECORD','evidence record must have exact fields')
        rid=row['record_id']
        if type(rid) is not str or not 1<=len(rid)<=128 or rid in seen:
            raise AppError('DOMAIN_RECORD','missing or duplicate record identity')
        seen.add(rid)
        if type(row['data_role']) is not str or row['data_role'] not in DATA_ROLES:raise AppError('DOMAIN_ROLE','unknown evidence role')
        event=_utc(row['event_at'],'event_at');known=_utc(row['known_at'],'known_at')
        source=_source(row['source']); published=_utc(source['published_at'],'published_at')
        if known<event or known<published:
            raise AppError('DOMAIN_CHRONOLOGY','knowledge time precedes event or publication')
        if input_document['lane']=='prospective' and known>freeze:late+=1
        if type(row['measurement_status']) is not str or row['measurement_status'] not in ('IN_B','OUTSIDE_B','UNEVALUABLE','NOT_APPLICABLE','UNDETERMINED'):
            raise AppError('DOMAIN_STATUS','unknown measurement status')
        unc=row['uncertainty']
        if type(unc) is not dict or set(unc)!={'status','notes'} or type(unc['status']) is not str or unc['status'] not in ('known','partial','unresolved','assumed') or type(unc['notes']) is not str or len(unc['notes'])>2000:
            raise AppError('DOMAIN_UNCERTAINTY','uncertainty must be explicit')
        payload=row['payload_sha256']
        if type(payload) is not str or len(payload)!=64 or any(c not in '0123456789abcdef' for c in payload):
            raise AppError('DOMAIN_RECORD','raw payload identity required')
        if row['data_role'] in ('parameter_draw','counterfactual_simulation') and input_document['lane']=='prospective':
            # Simulations may be included as assumptions in other lanes only.
            raise AppError('DOMAIN_ROLE','prospective evidence lane cannot relabel simulations as observations')
        accepted.append((rid,known.isoformat(),row['data_role']))
    digest=semantic_identity('domain-evidence',input_document)
    return {'format':'Permansson.App.DomainImportCheck.v1','status':'STRUCTURAL_EVIDENCE_VALID',
            'case_id':input_document['case_id'],'lane':input_document['lane'],
            'records_checked':len(entries),'records_after_freeze':late,
            'prospective_evidence_eligible_at_freeze':late==0 if input_document['lane']=='prospective' else None,
            'retained_data_roles':sorted({item[2] for item in accepted}),
            'source_identity_semantic_digest':digest,
            'estimated_transition_kernel':False,'equilibrium_policy_identified':False,
            'exact_regime_established':False,'constitutive_intervention_identified':False,
            'empirical_identification':DEFAULT_STATUS,'scientific_claims_verified':False}
