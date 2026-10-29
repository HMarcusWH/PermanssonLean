"""Bounded acyclic provenance graph with separate event, known and freeze clocks.

A valid DAG proves internal consistency, never origin authentication.
"""
from __future__ import annotations
from datetime import datetime
from dataclasses import dataclass
from .versioning import sha256
from .errors import AppError
from .identity import semantic_identity

KINDS={'source','observation','measurement','classification','hypothesis','transformation','model','result','review'}


def instant(value:object,name:str)->datetime:
    if type(value) is not str or not 20<=len(value)<=45 or (not (value.endswith('Z') or ('+' in value[10:] or '-' in value[10:]))):
        raise AppError('CLOCK_FORMAT',name+' must have a full timezone offset')
    try:
        d=datetime.fromisoformat(value.replace('Z','+00:00'))
    except (ValueError, OverflowError) as e:
        raise AppError('CLOCK_FORMAT',name+' must be valid ISO8601') from e
    if d.tzinfo is None or d.utcoffset() is None:
        raise AppError('CLOCK_FORMAT',name+' must be timezone aware')
    return d

@dataclass(frozen=True)
class ProvenanceNode:
    identifier: str
    kind: str
    digest: str
    parents: tuple[str,...]
    event_at: str|None
    known_at: str|None
    frozen_at: str|None

    @classmethod
    def parse(cls,obj:object)->'ProvenanceNode':
        if type(obj) is not dict or set(obj)!={'id','kind','sha256','parents','event_at','known_at','frozen_at'}:
            raise AppError('PROVENANCE_SHAPE','node has missing/extra fields')
        name=obj['id']
        if type(name) is not str or not name or len(name)>96 or not name.replace('_','').replace('-','').replace('.','').isalnum():
            raise AppError('PROVENANCE_ID','invalid node identifier')
        if type(obj['kind']) is not str or obj['kind'] not in KINDS:raise AppError('PROVENANCE_KIND','unknown evidence kind')
        parents=obj['parents']
        if type(parents) is not list or len(parents)>64 or any(type(x) is not str or not x for x in parents) or len(set(parents))!=len(parents):
            raise AppError('PROVENANCE_PARENTS','duplicate or invalid parents')
        for field in ('event_at','known_at','frozen_at'):
            if obj[field] is not None:instant(obj[field],field)
        return cls(name,obj['kind'],sha256(obj['sha256']),tuple(parents),obj['event_at'],obj['known_at'],obj['frozen_at'])

    def to_dict(self):
        return {'id':self.identifier,'kind':self.kind,'sha256':self.digest,'parents':list(self.parents),
                'event_at':self.event_at,'known_at':self.known_at,'frozen_at':self.frozen_at}


def check_provenance(nodes:object,*,evaluation_start:str|None=None,
                     cutoff:str|None=None)->dict:
    if type(nodes) is not list or len(nodes)>4096:
        raise AppError('PROVENANCE_LIMIT','bounded provenance node list required')
    parsed=[ProvenanceNode.parse(x) for x in nodes]
    byid={n.identifier:n for n in parsed}
    if len(byid)!=len(parsed):raise AppError('PROVENANCE_ID','duplicate node ID')
    if any(n.identifier in n.parents or set(n.parents)-set(byid) for n in parsed):
        raise AppError('PROVENANCE_PARENTS','missing or self parent')
    # Kahn topological traversal avoids recursion limits on deep provenance DAGs.
    indegree={key:len(node.parents) for key,node in byid.items()}
    children={key:[] for key in byid}
    for node in parsed:
        for parent in node.parents:children[parent].append(node.identifier)
    frontier=sorted(key for key,count in indegree.items() if count==0)
    order=[]
    while frontier:
        key=frontier.pop(0)
        order.append(key)
        for child in sorted(children[key]):
            indegree[child]-=1
            if indegree[child]==0:
                frontier.append(child);frontier.sort()
    if len(order)!=len(parsed):
        raise AppError('PROVENANCE_CYCLE','provenance dependency cycle')
    now=instant(cutoff,'cutoff') if cutoff is not None else None
    start=instant(evaluation_start,'evaluation_start') if evaluation_start is not None else None
    missing=[];future=[];late=[]
    for node in parsed:
        if node.known_at is None:missing.append(node.identifier)
        elif now is not None and instant(node.known_at,'known_at')>now:future.append(node.identifier)
        if node.frozen_at is not None and start is not None and instant(node.frozen_at,'frozen_at')>start:
            late.append(node.identifier)
        # A transformation cannot be known earlier than the data used to produce it.
        if node.known_at is not None:
            for parentid in node.parents:
                parent=byid[parentid]
                if parent.known_at is not None and instant(node.known_at,'known_at')<instant(parent.known_at,'parent_known_at'):
                    raise AppError('PROVENANCE_CHRONOLOGY','derived object known before dependency')
    digest=semantic_identity('provenance-dag',{'nodes':[byid[i].to_dict() for i in sorted(byid)]})
    return {'format':'Permansson.App.ProvenanceAssessment.v1','status':'CONSISTENT_UNAUTHENTICATED',
            'node_count':len(parsed),'topological_order':order,'identity':digest,
            'missing_known_at':missing,'excluded_future_knowledge':future,
            'late_freezes':late,'eligible_for_prospective_use':not(missing or future or late),
            'origin_authenticated':False,'scientific_claims_verified':False}
