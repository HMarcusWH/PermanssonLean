"""Read source-grade companion *artifact inventories*, never causal primitives.

Only declared artifacts are parsed, with byte-bound CSV/JSON inspection and
status explicitly limited to descriptive evidence; executable archive files
are not run. Missing source clocks remain unresolved rather than inferred.
"""
from __future__ import annotations
from datetime import datetime
from csv import DictReader
from decimal import Decimal
import json
from io import StringIO
from .bundle import BundleIndex,read_member
from .types import DomainImportResult
from .registry import DomainProfile,resolve_profile
from .roles import inferred_role
from ..errors import AppError
from ..strict_json import _pairs
from ..provenance import instant


def _matches(members, suffix):
    return [x for x in members if x.endswith('/'+suffix) or x==suffix]


def inspect_artifact(raw:bytes,name:str,*,cutoff:datetime|None=None)->dict:
    """Metadata and conservative known_at count for one small CSV/JSON member."""
    if len(raw)>2_000_000:raise AppError('DOMAIN_ARTIFACT_LIMIT','selected tabular file exceeds 2 MiB parse bound')
    if name.endswith('.json'):
        # Empirical data may contain JSON decimals. Parse them as Decimal
        # solely for structural metadata, never as causal probabilities.
        def invalid(value):raise ValueError('nonfinite JSON numeric constant')
        try:
            obj=json.loads(raw.decode('utf-8'),object_pairs_hook=_pairs,
                           parse_float=Decimal,parse_constant=invalid)
        except (ValueError,UnicodeError) as exc:
            raise AppError('DOMAIN_ARTIFACT','malformed empirical JSON') from exc
        if type(obj) not in (dict,list):raise AppError('DOMAIN_ARTIFACT','JSON metadata must be an object/list')
        return {'kind':'json','top_level_keys':sorted(obj) if type(obj) is dict else [],
                'item_count':len(obj),'known_at_scope':'NOT_EVALUATED_JSON'}
    if name.endswith('.csv'):
        try:text=raw.decode('utf-8-sig')
        except UnicodeDecodeError as e:raise AppError('DOMAIN_ARTIFACT','CSV not UTF-8') from e
        r=DictReader(StringIO(text))
        columns=r.fieldnames
        if not columns or len(columns)>512 or len(set(columns))!=len(columns) or any((not x and i != 0) or len(x)>160 for i,x in enumerate(columns)):
            raise AppError('DOMAIN_ARTIFACT','invalid CSV header')
        count=0;available=0;future=0;unresolved=0
        for row in r:
            count+=1
            if count>100000:raise AppError('DOMAIN_ARTIFACT_LIMIT','too many CSV rows')
            if None in row or any(v is None for v in row.values()):
                raise AppError('DOMAIN_ARTIFACT','ragged CSV row')
            if cutoff is not None:
                if 'known_at' not in columns or not row.get('known_at'):
                    unresolved+=1;continue
                try:d=instant(row['known_at'],'known_at')
                except AppError:unresolved+=1;continue
                if d<=cutoff:available+=1
                else:future+=1
        return {'kind':'csv','columns':columns,'row_count':count,
                'known_at_scope':('FILTERED' if cutoff is not None else 'NOT_EVALUATED'),
                'known_at_available':available,'known_at_future':future,'known_at_unresolved':unresolved}
    return {'kind':'opaque','status':'BYTE_HASH_ONLY'}


def import_domain(index:BundleIndex,profile:DomainProfile|str,*,cutoff:datetime|None=None)->DomainImportResult:
    if type(index) is not BundleIndex:raise AppError('DOMAIN_BUNDLE','indexed bounded bundle required')
    p=resolve_profile(profile) if type(profile) is str else profile
    if type(p) is not DomainProfile:raise AppError('DOMAIN_PROFILE','typed domain profile required')
    if cutoff is not None and (type(cutoff) is not datetime or cutoff.tzinfo is None):
        raise AppError('DOMAIN_CLOCK','timezone-aware cutoff required')
    selected=[];missing=[];artifacts={};roles={};inspection={}
    for suffix in (*p.required_suffixes,*p.optional_suffixes):
        matched=_matches(index.members,suffix)
        # Reject ambiguity; nested source packages may have copies of the
        # same named file, and choosing the first silently corrupts provenance.
        if len(matched)>1:raise AppError('DOMAIN_AMBIGUOUS','multiple candidates for '+suffix)
        if not matched:
            if suffix in p.required_suffixes:missing.append(suffix)
            continue
        name=matched[0];raw=read_member(index,name)
        selected.append(name);artifacts[name]=index.sha256_by_member[name]
        roles[name]=inferred_role(name)
        inspection[name]=inspect_artifact(raw,name,cutoff=cutoff)
    # Attach detailed inspection in the chronology field, distinct from causal
    # or statistical identification; no arbitrary source code is executed.
    status='INCOMPLETE_EVIDENCE_BUNDLE' if missing else 'EVIDENCE_ONLY_NOT_CAUSALLY_IDENTIFIED'
    return DomainImportResult(p.name,index.original_bundle_sha256,artifacts,roles,
            tuple(selected),tuple(missing),{'cutoff':cutoff.isoformat() if cutoff else None,
                                          'inspected_artifacts':inspection},status)
