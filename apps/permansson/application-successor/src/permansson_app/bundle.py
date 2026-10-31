"""Detached SHA-256 application bundle inventory and independent offline check.

This is integrity against a separately trusted manifest, not an origin signature.
Never imports or executes code from a bundle and never accepts embedded proofs as authority.
"""
from __future__ import annotations
from pathlib import Path, PurePosixPath
from hashlib import sha256
import json, os
from .errors import AppError
from .identity import canonical_bytes

FORMAT='Permansson.App.DetachedBundleManifest.v1'
MAX_FILES=128
MAX_FILE_BYTES=4*1024*1024
MAX_TOTAL_BYTES=32*1024*1024


def _safe_rel(name: object)->str:
    if type(name) is not str or not name or len(name)>180 or '\\' in name or '\x00' in name:
        raise AppError('BUNDLE_PATH','invalid bundle path')
    p=PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or str(p)!=name or any(s in ('.','') for s in name.split('/')):
        raise AppError('BUNDLE_PATH','bundle path escapes resource root')
    return name


def _read(root:Path,name:str)->bytes:
    name=_safe_rel(name)
    cursor=root
    if root.is_symlink():raise AppError('BUNDLE_PATH','resource root may not be symlink')
    for part in name.split('/'):
        cursor=cursor/part
        if cursor.is_symlink():raise AppError('BUNDLE_PATH','symlink input prohibited')
    if not cursor.is_file():raise AppError('BUNDLE_FILE','missing listed file')
    if cursor.stat().st_size>MAX_FILE_BYTES:raise AppError('BUNDLE_LIMIT','single file too large')
    with cursor.open('rb') as f:
        data=f.read(MAX_FILE_BYTES+1)
    if len(data)>MAX_FILE_BYTES:raise AppError('BUNDLE_LIMIT','single file too large')
    return data


def _names(root:Path)->list[str]:
    if not root.is_dir() or root.is_symlink():raise AppError('BUNDLE_PATH','root must be a real directory')
    out=[]
    for parent,dirs,files in os.walk(root,topdown=True,followlinks=False):
        for d in dirs:
            if (Path(parent)/d).is_symlink():raise AppError('BUNDLE_PATH','symlink directory prohibited')
        for f in files:
            path=Path(parent)/f
            if path.is_symlink():raise AppError('BUNDLE_PATH','symlink file prohibited')
            out.append(_safe_rel(path.relative_to(root).as_posix()))
            if len(out)>MAX_FILES:raise AppError('BUNDLE_LIMIT','file count exceeds limit')
    return sorted(out)


def _validated_policy(claimed:object)->list[tuple[str,int,str]]:
    if type(claimed) is not dict or set(claimed)!={'format','files','declared_source','scope'} or claimed['format']!=FORMAT:
        raise AppError('BUNDLE_MANIFEST','wrong manifest format')
    if type(claimed['scope']) is not str or not claimed['scope'] or len(claimed['scope'])>128:
        raise AppError('BUNDLE_MANIFEST','scope label required')
    if type(claimed['declared_source']) is not dict or set(claimed['declared_source'])!={'source_commit','source_tree'}:
        raise AppError('BUNDLE_MANIFEST','source identity must be explicit')
    # The source strings are claimed, never authenticated by this tool.
    for key in ('source_commit','source_tree'):
        val=claimed['declared_source'][key]
        if type(val) is not str or len(val)!=40 or any(c not in '0123456789abcdef' for c in val):
            raise AppError('BUNDLE_MANIFEST','source identity format invalid')
    files=claimed['files']
    if type(files) is not list or len(files)>MAX_FILES:raise AppError('BUNDLE_MANIFEST','invalid file entries')
    data=[]
    for entry in files:
        if type(entry) is not dict or set(entry)!={'path','size_bytes','sha256'}:
            raise AppError('BUNDLE_MANIFEST','file entry must be exact')
        path=_safe_rel(entry['path']); size=entry['size_bytes'];digest=entry['sha256']
        if type(size) is not int or size<0 or size>MAX_FILE_BYTES or type(digest) is not str or len(digest)!=64 or any(c not in '0123456789abcdef' for c in digest):
            raise AppError('BUNDLE_MANIFEST','invalid size or digest')
        data.append((path,size,digest))
    if [item[0] for item in data]!=sorted(set(item[0] for item in data)):
        raise AppError('BUNDLE_MANIFEST','path entries must be distinct and sorted')
    if sum(v[1] for v in data)>MAX_TOTAL_BYTES:raise AppError('BUNDLE_LIMIT','manifest total exceeds limit')
    return data


def create_detached_manifest(root:Path, *,scope:str,source_commit:str,source_tree:str)->dict:
    """Producer convenience; store manifest *outside* root in a trusted location."""
    root=Path(root)
    names=_names(root)
    items=[]; total=0
    for name in names:
        data=_read(root,name);total+=len(data)
        if total>MAX_TOTAL_BYTES:raise AppError('BUNDLE_LIMIT','bundle exceeds byte limit')
        items.append({'path':name,'size_bytes':len(data),'sha256':sha256(data).hexdigest()})
    obj={'format':FORMAT,'scope':scope,'declared_source':{'source_commit':source_commit,'source_tree':source_tree},'files':items}
    _validated_policy(obj)
    return obj


def verify_detached_bundle(root:Path,manifest:object,*,expected_manifest_sha256:str|None=None,require_exact_inventory:bool=True)->dict:
    """Consumer verification against a separate manifest and optional trusted hash."""
    rows=_validated_policy(manifest)
    digest=sha256(canonical_bytes(manifest)).hexdigest()
    if expected_manifest_sha256 is not None:
        if type(expected_manifest_sha256) is not str or len(expected_manifest_sha256)!=64 or digest!=expected_manifest_sha256:
            raise AppError('BUNDLE_TRUST','detached manifest hash not trusted')
    root=Path(root)
    if require_exact_inventory and _names(root)!=[r[0] for r in rows]:
        raise AppError('BUNDLE_INVENTORY','unlisted or missing bundle files')
    total=0
    for name,size,claimed_hash in rows:
        blob=_read(root,name);total+=len(blob)
        if total>MAX_TOTAL_BYTES:raise AppError('BUNDLE_LIMIT','bundle exceeds total byte limit')
        if len(blob)!=size or sha256(blob).hexdigest()!=claimed_hash:
            raise AppError('BUNDLE_INTEGRITY',f'file content differs: {name}')
    return {'format':'Permansson.App.BundleIndependentCheck.v1','status':'HASH_INTEGRITY_VERIFIED',
            'files_checked':len(rows),'total_bytes_checked':total,'manifest_sha256':digest,
            'trusted_manifest_hash_supplied':expected_manifest_sha256 is not None,
            'origin_authenticated':False,'mathematical_claims_verified':False,
            'declared_source':manifest['declared_source']}
