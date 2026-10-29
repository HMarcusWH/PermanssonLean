"""Governed claim scope resolution. Calculations cannot accept mathematical claims."""
from __future__ import annotations
from dataclasses import dataclass
from .errors import AppError
from .evidence import EvidenceSet

@dataclass(frozen=True)
class ClaimDefinition:
    claim_id:str
    source_commit:str
    theorem:str|None
    capability:str|None
    required_hypotheses:tuple[str,...]
    required_starts:tuple[str,...]
    classification:str
    original_accepted:bool

@dataclass(frozen=True)
class ClaimAssessment:
    claim_id:str
    status:str
    missing_hypotheses:tuple[str,...]
    missing_starts:tuple[str,...]
    mathematical_acceptance:bool=False

@dataclass(frozen=True)
class ClaimRegistry:
    claims:tuple[ClaimDefinition,...]

    @classmethod
    def parse(cls,raw:object)->'ClaimRegistry':
        if type(raw) is not dict or set(raw)!={'format','claims'} or raw['format']!='Permansson.App.ClaimRegistry.v1' or type(raw['claims']) is not list:
            raise AppError('CLAIM_REGISTRY','unexpected claim registry format')
        if len(raw['claims'])>5000:raise AppError('CLAIM_REGISTRY','too many claim definitions')
        out=[];ids=set()
        from .versioning import sha40
        for x in raw['claims']:
            if type(x) is not dict or set(x)!={'id','source_commit','theorem','capability','required_hypotheses','required_starts','classification','original_accepted'}:
                raise AppError('CLAIM_REGISTRY','malformed claim definition')
            id=x['id']
            if type(id) is not str or not id or id in ids or len(id)>128:raise AppError('CLAIM_REGISTRY','duplicate/invalid claim ID')
            ids.add(id)
            if type(x['classification']) is not str or x['classification'] not in ('historical_case','later_claim','numeric_profile','not_runtime'):
                raise AppError('CLAIM_REGISTRY','unsupported classification')
            if type(x['original_accepted']) is not bool:raise AppError('CLAIM_REGISTRY','accepted flag must be boolean')
            for k in ('theorem','capability'):
                if x[k] is not None and (type(x[k]) is not str or not x[k]):raise AppError('CLAIM_REGISTRY','invalid theorem/capability')
            def values(name):
                v=x[name]
                if type(v) is not list or len(v)>1000 or any(type(y) is not str or not y for y in v) or len(set(v))!=len(v):
                    raise AppError('CLAIM_REGISTRY','invalid '+name)
                return tuple(v)
            out.append(ClaimDefinition(id,sha40(x['source_commit']),x['theorem'],x['capability'],
                values('required_hypotheses'),values('required_starts'),x['classification'],x['original_accepted']))
        return cls(tuple(out))


def resolve_claim(claim_id:str, registry:ClaimRegistry)->ClaimDefinition:
    matches=[c for c in registry.claims if c.claim_id==claim_id]
    if len(matches)!=1:raise AppError('CLAIM_UNKNOWN','unknown claim id')
    return matches[0]


def evaluate_claim_scope(claim:ClaimDefinition,evidence:EvidenceSet,*,
                         verified_hypotheses:tuple[str,...]=(),verified_starts:tuple[str,...]=())->ClaimAssessment:
    """Only a scope report. No source-only input can independently CERT a claim."""
    missing_h=tuple(sorted(set(claim.required_hypotheses)-set(verified_hypotheses)))
    missing_s=tuple(sorted(set(claim.required_starts)-set(verified_starts)))
    if not isinstance(evidence,EvidenceSet):raise AppError('CLAIM_EVIDENCE','authenticated evidence set required')
    if missing_h or missing_s:return ClaimAssessment(claim.claim_id,'PREMISES_INCOMPLETE',missing_h,missing_s)
    if claim.classification=='not_runtime' or claim.capability is None:
        return ClaimAssessment(claim.claim_id,'NOT_RUNTIME_CAPABILITY',(),())
    return ClaimAssessment(claim.claim_id,'SCOPED_FOR_REVIEW_NOT_CERTIFIED',(),())
