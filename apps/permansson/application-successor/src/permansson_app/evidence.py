"""Evidence source/type checking with external-hash authentication boundary.

Self-asserted PASS, CI run numbers or reviewer flags are never trusted by this
module. A consumer must provide expected digests from an independent channel.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256 as hash256
from .errors import AppError
from .identity import canonical_bytes
from .versioning import sha40, sha256

FORM='Permansson.App.EvidenceRecord.v1'
TYPES={'numeric_test','source_build','lean_compiler','axiom_audit','negative_mutation',
       'provenance','package','cross_platform','security_review','research_review','owner_approval'}
STATUSES={'PASS','FAIL','ERROR','SKIPPED','NOT_EXECUTED'}

@dataclass(frozen=True)
class EvidenceRecord:
    evidence_id:str
    kind:str
    subject_sha256:str
    source_commit:str
    source_tree:str
    capability:str
    execution_profile:str
    platform:str
    method_ids:tuple[str,...]
    status:str
    artifact_sha256:str
    producer:str
    reviewer:str|None

    @classmethod
    def parse(cls,raw:object)->'EvidenceRecord':
        keys={'format','evidence_id','kind','subject_sha256','source_commit','source_tree','capability',
              'execution_profile','platform','method_ids','status','artifact_sha256','producer','reviewer'}
        if type(raw) is not dict or set(raw)!=keys or raw['format']!=FORM:
            raise AppError('EVIDENCE_FORMAT','unsupported evidence record format')
        def string(name,maxsize=160):
            v=raw[name]
            if type(v) is not str or not v or len(v)>maxsize:
                raise AppError('EVIDENCE_FIELD','invalid '+name)
            return v
        if type(raw['kind']) is not str or raw['kind'] not in TYPES:raise AppError('EVIDENCE_TYPE','unsupported evidence type')
        if type(raw['status']) is not str or raw['status'] not in STATUSES:raise AppError('EVIDENCE_STATUS','unsupported status')
        ids=raw['method_ids']
        if type(ids) is not list or not ids or len(ids)>10000 or any(type(s) is not str or not s or len(s)>160 for s in ids) or len(set(ids))!=len(ids):
            raise AppError('EVIDENCE_METHODS','empty, invalid or repeated method identifiers')
        reviewer=raw['reviewer']
        if reviewer is not None and (type(reviewer) is not str or not reviewer or len(reviewer)>120):
            raise AppError('EVIDENCE_REVIEW','invalid reviewer identifier')
        return cls(string('evidence_id'),string('kind'),sha256(raw['subject_sha256'],'subject'),
                   sha40(raw['source_commit']),sha40(raw['source_tree'],'source_tree'),
                   string('capability'),string('execution_profile'),string('platform'),tuple(ids),
                   string('status'),sha256(raw['artifact_sha256'],'artifact'),string('producer'),reviewer)


def record_digest(raw:object)->str:
    EvidenceRecord.parse(raw)
    return hash256(canonical_bytes(raw)).hexdigest()


@dataclass(frozen=True)
class EvidenceSet:
    """Preauthenticated records, pinned by a separate source of expected SHA256.

    The expected-digest mapping must be owned by the consumer, not the evidence
    archive being assessed. A mapping alone does NOT authenticate reviewer identity.
    """
    records:tuple[EvidenceRecord,...]
    authenticated_digests:tuple[str,...]

    @classmethod
    def from_external_hashes(cls,records:object,*,trusted_expected_digests:object)->'EvidenceSet':
        if type(records) is not list or type(trusted_expected_digests) is not dict or len(records)>10000:
            raise AppError('EVIDENCE_SET','bounded evidence array and independent pins required')
        seen=set();parsed=[];digs=[]
        for item in records:
            obj=EvidenceRecord.parse(item)
            if obj.evidence_id in seen:raise AppError('EVIDENCE_DUPLICATE','duplicate receipt id')
            seen.add(obj.evidence_id)
            expected=trusted_expected_digests.get(obj.evidence_id)
            if expected is None:raise AppError('EVIDENCE_UNAUTHENTICATED','no independent hash for '+obj.evidence_id)
            digest=record_digest(item)
            if sha256(expected)!=digest:raise AppError('EVIDENCE_TAMPER','receipt not equal independently pinned bytes')
            parsed.append(obj);digs.append(digest)
        if set(trusted_expected_digests)!=seen:
            raise AppError('EVIDENCE_SET','unused or missing externally pinned evidence')
        return cls(tuple(parsed),tuple(digs))

    def matching(self,*,subject_sha256:str,source_commit:str,source_tree:str,
                 capability:str,execution_profile:str,platform:str,kind:str):
        return tuple(r for r in self.records if r.subject_sha256==subject_sha256
            and r.source_commit==source_commit and r.source_tree==source_tree
            and r.capability==capability and r.execution_profile==execution_profile
            and r.platform==platform and r.kind==kind)
