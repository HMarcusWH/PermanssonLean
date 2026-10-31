"""Check source-bound compiler/audit evidence; never execute untrusted Lean code.

This is a consumer gate. The trusted builder must separately run pinned Lean
inside reviewed isolation, then publish an independently authenticated log.
"""
from __future__ import annotations
from dataclasses import dataclass
from .errors import AppError
from .evidence import EvidenceSet
from .versioning import sha256,sha40

_ALLOWED={'propext','Classical.choice','Quot.sound'}

@dataclass(frozen=True)
class ReplayTarget:
    source_commit:str
    source_tree:str
    subject_sha256:str
    emitted_sha256:str
    theorem_type_sha256:str
    declaration:str
    toolchain:str

    @classmethod
    def parse(cls,raw:object):
        keys={'source_commit','source_tree','subject_sha256','emitted_sha256','theorem_type_sha256','declaration','toolchain'}
        if type(raw) is not dict or set(raw)!=keys:raise AppError('REPLAY_TARGET','incomplete/extra replay target')
        for k in ('declaration','toolchain'):
            if type(raw[k]) is not str or not raw[k] or len(raw[k])>240:raise AppError('REPLAY_TARGET','invalid '+k)
        return cls(sha40(raw['source_commit']),sha40(raw['source_tree'],'source_tree'),
                   sha256(raw['subject_sha256']),sha256(raw['emitted_sha256']),
                   sha256(raw['theorem_type_sha256']),raw['declaration'],raw['toolchain'])


def evaluate_replay(target:ReplayTarget,transcript:object,evidence:EvidenceSet)->dict:
    if type(target) is not ReplayTarget or type(evidence) is not EvidenceSet or type(transcript) is not dict:
        raise AppError('REPLAY_INPUT','typed target/transcript/authenticated evidence required')
    keys={'format','source_commit','source_tree','subject_sha256','emitted_sha256',
          'theorem_type_sha256','declaration','toolchain','compiler_exit','axiom_audit_exit',
          'transitive_axioms','compiler_evidence_id','audit_evidence_id','negative_evidence_id'}
    if set(transcript)!=keys or transcript['format']!='Permansson.App.LeanReplayTranscript.v1':
        raise AppError('REPLAY_FORMAT','invalid replay transcript')
    for k in ('source_commit','source_tree','subject_sha256','emitted_sha256','theorem_type_sha256','declaration','toolchain'):
        if transcript[k]!=getattr(target,k):raise AppError('REPLAY_BINDING','replay differs at '+k)
    if type(transcript['compiler_exit']) is not int or type(transcript['axiom_audit_exit']) is not int:
        raise AppError('REPLAY_EXIT','invalid compiler exits')
    if transcript['compiler_exit']!=0 or transcript['axiom_audit_exit']!=0:
        raise AppError('REPLAY_COMPILER','nonzero proof or axiom audit exit')
    axioms=transcript['transitive_axioms']
    if type(axioms) is not list or len(axioms)!=len(set(axioms)) or any(type(x) is not str or x not in _ALLOWED for x in axioms):
        raise AppError('REPLAY_AXIOMS','unauthorized or malformed transitive axiom set')
    for k,kind,method in [('compiler_evidence_id','lean_compiler',target.declaration),
                          ('audit_evidence_id','axiom_audit',target.declaration),
                          ('negative_evidence_id','negative_mutation',target.declaration)]:
        ref=transcript[k]
        if type(ref) is not str or not ref:raise AppError('REPLAY_EVIDENCE','missing evidence reference')
        found=[x for x in evidence.records if x.evidence_id==ref and x.kind==kind and x.status=='PASS'
               and x.source_commit==target.source_commit and x.source_tree==target.source_tree
               and x.subject_sha256==target.subject_sha256 and method in x.method_ids]
        if len(found)!=1:raise AppError('REPLAY_EVIDENCE','missing external pinned '+kind)
    # This gate intentionally DOES NOT infer that external independent review
    # and product release acceptance have been granted.
    return {'format':'Permansson.App.ReplayEvidenceAssessment.v1',
            'status':'INSTANCE_COMPILER_EVIDENCE_MATCHED_REVIEW_REQUIRED',
            'exact_declaration':target.declaration,'source_commit':target.source_commit,
            'input_bound':True,'independent_math_certification':False,
            'application_release_authorized':False,'empirical_identification':False}
