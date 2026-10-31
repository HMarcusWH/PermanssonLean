"""Common immutable domain evidence types with no causal-identity promotion."""
from __future__ import annotations
from dataclasses import dataclass

@dataclass(frozen=True)
class ObservationRecord:
    record_id:str
    event_at:str|None
    known_at:str|None
    frozen_spec_at:str|None=None
    evaluation_start:str|None=None
    lane:str='retrospective'

@dataclass(frozen=True)
class DomainImportResult:
    case:str
    bundle_sha256:str|None
    artifact_digests:dict[str,str]
    artifact_roles:dict[str,str]
    selected_artifacts:tuple[str,...]
    missing_required:tuple[str,...]
    chronology:dict
    status:str='EVIDENCE_ONLY_NOT_CAUSALLY_IDENTIFIED'
    def to_dict(self):
        return {'format':'Permansson.App.DomainImport.v1','case':self.case,
                'bundle_sha256':self.bundle_sha256,'artifact_digests':self.artifact_digests,
                'artifact_roles':self.artifact_roles,'selected_artifacts':list(self.selected_artifacts),
                'missing_required':list(self.missing_required),'chronology':self.chronology,
                'status':self.status,'causal_alpha_P_U_identified':False,
                'empirical_exact_GR_PR_certified':False,'lean_status':'NOT_EXECUTED'}
