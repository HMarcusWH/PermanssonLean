"""Selected-scope evidence completeness, not self-issued release authorization.

The result is eligible-for-review-and-activation at most. A reviewer identity
or an owner activation cannot be obtained from a supplied JSON flag.

Policy formats:

- v1: required evidence per capability, plus review and activation flags.
- v2: adds the selected scope, platforms and execution profile, and the test
  sources each capability's method list is checked against.
- v3: adds `release_authority`, which names who approves a release. Its only
  kind so far is `OWNER_ENGINEERING_POLICY`: the owner approves and activates
  the release; no independent security review is claimed, so
  `security_review_required` must be false.
"""
from __future__ import annotations
import re
from dataclasses import dataclass
from .errors import AppError
from .versioning import SourcePin,sha256
from .evidence import EvidenceSet, EvidenceRecord
from .identity import semantic_identity

@dataclass(frozen=True)
class AcceptanceTarget:
    source: SourcePin
    subject_sha256: str
    wheel_sha256: str
    sdist_sha256: str
    capabilities: tuple[str,...]
    platforms: tuple[str,...]
    execution_profile: str

    @classmethod
    def parse(cls,raw:object)->'AcceptanceTarget':
        keys={'source','subject_sha256','wheel_sha256','sdist_sha256','capabilities','platforms','execution_profile'}
        if type(raw) is not dict or set(raw)!=keys:raise AppError('ACCEPTANCE_TARGET','missing or extra target fields')
        def names(key):
            items=raw[key]
            if type(items) is not list or not items or len(items)>128 or any(type(v) is not str or not v or len(v)>120 for v in items) or len(set(items))!=len(items):
                raise AppError('ACCEPTANCE_TARGET','invalid '+key)
            return tuple(items)
        if raw['execution_profile'] not in ('numeric','lean_replay','empirical'):
            raise AppError('ACCEPTANCE_TARGET','unsupported execution profile')
        return cls(SourcePin.parse(raw['source']),sha256(raw['subject_sha256']),
                   sha256(raw['wheel_sha256']),sha256(raw['sdist_sha256']),
                   names('capabilities'),names('platforms'),raw['execution_profile'])

    def identity(self):
        return semantic_identity('application-release-subject',
             {'source':self.source.to_dict(),'subject_sha256':self.subject_sha256,
              'wheel_sha256':self.wheel_sha256,'sdist_sha256':self.sdist_sha256,
              'capabilities':list(self.capabilities),'platforms':list(self.platforms),
              'execution_profile':self.execution_profile})

_LOGIN=re.compile(r'^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$')


@dataclass(frozen=True)
class ReleaseAuthority:
    kind: str
    owner: str
    independent_security_review: bool
    activation: str

    @classmethod
    def parse(cls, raw: object) -> 'ReleaseAuthority':
        keys = {'kind', 'owner', 'independent_security_review', 'activation'}
        if type(raw) is not dict or set(raw) != keys:
            raise AppError('ACCEPTANCE_POLICY', 'release authority needs kind, owner, independent_security_review and activation')
        if raw['kind'] != 'OWNER_ENGINEERING_POLICY' or raw['independent_security_review'] is not False:
            raise AppError('ACCEPTANCE_POLICY', 'an owner-engineering authority never claims independent security review')
        if type(raw['owner']) is not str or not _LOGIN.fullmatch(raw['owner']):
            raise AppError('ACCEPTANCE_POLICY', 'release authority owner must be a GitHub login')
        if type(raw['activation']) is not str or not raw['activation']:
            raise AppError('ACCEPTANCE_POLICY', 'release authority must say how the owner activates a release')
        return cls(raw['kind'], raw['owner'], False, raw['activation'])

    def to_dict(self) -> dict:
        return {'kind': self.kind, 'owner': self.owner, 'independent_security_review': False,
                'activation': self.activation}


@dataclass(frozen=True)
class AcceptancePolicy:
    """Explicit minimum selected method IDs, keyed by capability and platform.

    Assumed trusted by an independent consumer, NOT from the tested artifact.
    A v2 policy also names its scope, the only selected platforms and the only
    selected execution profile; anything else is reported missing, never covered.
    """
    required:dict
    require_security_review:bool=True
    require_owner_activation:bool=True
    scope:str|None=None
    platforms:tuple[str,...]|None=None
    execution_profile:str|None=None
    release_authority:ReleaseAuthority|None=None

    @classmethod
    def parse(cls,raw:object)->'AcceptancePolicy':
        v1={'format','required','security_review_required','owner_activation_required'}
        v2=v1|{'scope','description','platforms','execution_profile','method_sources'}
        v3=v2|{'release_authority'}
        if type(raw) is not dict or not ((raw.get('format')=='Permansson.App.AcceptancePolicy.v1' and set(raw)==v1)
                                         or (raw.get('format')=='Permansson.App.AcceptancePolicy.v2' and set(raw)==v2)
                                         or (raw.get('format')=='Permansson.App.AcceptancePolicy.v3' and set(raw)==v3)):
            raise AppError('ACCEPTANCE_POLICY','unknown or incomplete selected release policy')
        extra={}
        if not raw['format'].endswith('.v1'):
            platforms=raw['platforms']
            if (type(raw['scope']) is not str or not raw['scope'] or type(raw['description']) is not str
                    or type(platforms) is not list or not platforms or len(set(platforms))!=len(platforms)
                    or any(type(p) is not str or not p for p in platforms)
                    or raw['execution_profile'] not in ('numeric','lean_replay','empirical')):
                raise AppError('ACCEPTANCE_POLICY','invalid v2 scope, platforms or execution profile')
            sources=raw['method_sources']
            if (type(sources) is not dict or type(raw['required']) is not dict or set(sources)!=set(raw['required'])
                    or any(type(v) is not list or not v or any(type(s) is not str or not s for s in v)
                           for v in sources.values())):
                raise AppError('ACCEPTANCE_POLICY','every selected capability needs its test-method sources')
            extra={'scope':raw['scope'],'platforms':tuple(platforms),'execution_profile':raw['execution_profile']}
        if raw['format'].endswith('.v3'):
            extra['release_authority']=ReleaseAuthority.parse(raw['release_authority'])
            if raw['security_review_required'] is not False or raw['owner_activation_required'] is not True:
                raise AppError('ACCEPTANCE_POLICY','an owner-engineering policy requires owner activation and no independent review')
        if type(raw['required']) is not dict or not raw['required']:
            raise AppError('ACCEPTANCE_POLICY','missing selected capability contracts')
        if type(raw['security_review_required']) is not bool or type(raw['owner_activation_required']) is not bool:
            raise AppError('ACCEPTANCE_POLICY','invalid review requirement flags')
        verified={}
        for cap,profile in raw['required'].items():
            if type(cap) is not str or type(profile) is not dict or not profile:
                raise AppError('ACCEPTANCE_POLICY','invalid capability evidence map')
            verified[cap]={}
            for kind,methods in profile.items():
                if type(kind) is not str or type(methods) is not list or not methods or len(methods)>1000 or any(type(m) is not str or not m for m in methods) or len(set(methods))!=len(methods):
                    raise AppError('ACCEPTANCE_POLICY','required method list missing or duplicate')
                verified[cap][kind]=tuple(methods)
        return cls(verified,raw['security_review_required'],raw['owner_activation_required'],**extra)

@dataclass(frozen=True)
class AcceptanceAssessment:
    status:str
    target_identity:dict
    missing:tuple[str,...]
    failing:tuple[str,...]
    covered:tuple[str,...]
    authorized_release:bool=False
    scientific_claims_verified:bool=False
    empirical_identification:bool=False

    def to_dict(self):
        return {'format':'Permansson.App.AcceptanceAssessment.v1','status':self.status,
                'target_identity':self.target_identity,'missing':list(self.missing),
                'failing':list(self.failing),'covered':list(self.covered),
                'authorized_release':False,'scientific_claims_verified':False,
                'empirical_identification':False}


def assess_acceptance(target:AcceptanceTarget,evidence:EvidenceSet,
                      policy:AcceptancePolicy)->AcceptanceAssessment:
    if type(target) is not AcceptanceTarget or type(evidence) is not EvidenceSet or type(policy) is not AcceptancePolicy:
        raise AppError('ACCEPTANCE_INPUT','independently pinned target/evidence/policy required')
    missing=[];failed=[];covered=[]
    if policy.execution_profile is not None and target.execution_profile!=policy.execution_profile:
        missing.append('execution-profile-not-selected:'+target.execution_profile)
    for cap in target.capabilities:
        requirements=policy.required.get(cap)
        if requirements is None:
            missing.append('capability-not-declared:'+cap);continue
        for platform in target.platforms:
            if policy.platforms is not None and platform not in policy.platforms:
                missing.append('platform-not-selected:'+platform);continue
            for kind,caseids in requirements.items():
                # Strong modes require actual specific proof evidence even if
                # a numeric policy happens to list fewer requirements.
                extra={}
                if target.execution_profile=='lean_replay':extra={'lean_compiler':('exact-instance',),'axiom_audit':('transitive',),'negative_mutation':('semantic',)}
                if target.execution_profile=='empirical':extra={'provenance':('identified-primitive-source',)}
                for category,needed in ((kind,caseids),*extra.items()):
                    records=evidence.matching(subject_sha256=target.subject_sha256,
                        source_commit=target.source.commit,source_tree=target.source.tree,
                        capability=cap,execution_profile=target.execution_profile,
                        platform=platform,kind=category)
                    found={case for r in records if r.status=='PASS' for case in r.method_ids}
                    bad={case for r in records if r.status!='PASS' for case in r.method_ids}
                    for method in needed:
                        key=f'{cap}/{platform}/{category}/{method}'
                        if method in bad:failed.append(key)
                        elif method not in found:missing.append(key)
                        else:covered.append(key)
            # All selected platforms must have both matching build artifacts.
            package=evidence.matching(subject_sha256=target.subject_sha256,
                 source_commit=target.source.commit,source_tree=target.source.tree,
                 capability=cap,execution_profile=target.execution_profile,
                 platform=platform,kind='package')
            valid={r.artifact_sha256 for r in package if r.status=='PASS'}
            for required in (target.wheel_sha256,target.sdist_sha256):
                if required not in valid:missing.append(f'{cap}/{platform}/package/{required}')
    # Independent owner and reviewer authorization is deliberately out of band.
    # A receipt or flag in a tested source archive never creates authority.
    if policy.require_security_review:missing.append('EXTERNAL_INDEPENDENT_SECURITY_REVIEW')
    if policy.require_owner_activation:missing.append('EXTERNAL_OWNER_RELEASE_ACTIVATION')
    # Under an owner-engineering authority the owner's activation is also the
    # release approval; it is checked outside this function (release gate).
    # The external decisions are always listed as missing; they never make the
    # evidence itself incomplete.
    evidence_missing=[m for m in missing if not m.startswith('EXTERNAL_')]
    status='BLOCKED_FAILED_EVIDENCE' if failed else ('BLOCKED_MISSING_EVIDENCE' if evidence_missing
                                                      else 'EVIDENCE_COMPLETE_REVIEW_REQUIRED')
    return AcceptanceAssessment(status,target.identity(),tuple(sorted(set(missing))),
                                  tuple(sorted(set(failed))),tuple(sorted(set(covered))))
