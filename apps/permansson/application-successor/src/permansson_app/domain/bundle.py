"""Bounded ZIP/directory evidence reader. Never executes source programs.

Symlinks, traversal, duplicates, Unicode/case collisions, oversized members and
zip compression bombs fail closed before a member becomes usable.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path,PurePosixPath
import os,stat,unicodedata,zipfile
from ..errors import AppError

@dataclass(frozen=True)
class BundleLimits:
    max_members:int=4096
    max_member_bytes:int=16_777_216
    max_total_bytes:int=134_217_728
    max_compression_ratio:int=100
    def __post_init__(self):
        for key in ('max_members','max_member_bytes','max_total_bytes','max_compression_ratio'):
            value=getattr(self,key)
            if type(value) is not int or value<1 or value>2**31:
                raise AppError('BUNDLE_LIMITS','invalid '+key)

@dataclass(frozen=True)
class BundleIndex:
    path:Path
    is_zip:bool
    members:tuple[str,...]
    sizes:dict[str,int]
    sha256_by_member:dict[str,str]
    original_bundle_sha256:str|None
    limits:BundleLimits


def safe_member(name:str)->str:
    if type(name) is not str or not name or '\\' in name or '\x00' in name or name.startswith('/') or ':' in name.split('/')[0] or len(name)>512:
        raise AppError('BUNDLE_PATH','invalid member name')
    parts=name.split('/')
    if any(p in ('','.','..') or any(ord(x)<32 for x in p) for p in parts):
        raise AppError('BUNDLE_PATH','traversal/empty/control component')
    if unicodedata.normalize('NFC',name)!=name:
        raise AppError('BUNDLE_PATH','noncanonical Unicode member')
    return name


def _hash_file(path:Path,cap:int)->tuple[str,int]:
    h=sha256();total=0
    with path.open('rb') as stream:
        while True:
            part=stream.read(min(131072,cap-total+1))
            if not part:break
            total+=len(part)
            if total>cap:raise AppError('BUNDLE_LIMIT','individual file too large')
            h.update(part)
    return h.hexdigest(),total


def _consider(name,found,folded):
    name=safe_member(name)
    fold=name.casefold()
    if name in found or fold in folded:raise AppError('BUNDLE_DUPLICATE','duplicate or portability-colliding member')
    found.add(name);folded.add(fold)
    return name


def open_bundle(path:Path,limits:BundleLimits|None=None)->BundleIndex:
    path=Path(path)
    limits=limits or BundleLimits()
    if path.is_symlink() or not path.exists():raise AppError('BUNDLE_PATH','missing or linked input')
    sizes={};digs={};seen=set();folded=set();total=0
    if path.is_dir():
        base=path.resolve()
        for root,dirs,files in os.walk(path,followlinks=False):
            for d in dirs:
                if (Path(root)/d).is_symlink():raise AppError('BUNDLE_LINK','symlink directory')
            for filename in files:
                f=Path(root)/filename
                if f.is_symlink() or not f.is_file() or not stat.S_ISREG(f.stat().st_mode):
                    raise AppError('BUNDLE_LINK','source is not a regular file')
                rel=f.relative_to(path).as_posix();_consider(rel,seen,folded)
                digest,n=_hash_file(f,limits.max_member_bytes)
                sizes[rel]=n;digs[rel]=digest;total+=n
                if len(seen)>limits.max_members or total>limits.max_total_bytes:
                    raise AppError('BUNDLE_LIMIT','expanded source exceeds global limits')
        return BundleIndex(path,False,tuple(sorted(seen)),sizes,digs,None,limits)
    if not path.is_file():raise AppError('BUNDLE_PATH','not file/directory')
    if path.suffix.lower()!='.zip':raise AppError('BUNDLE_TYPE','only data directories or ZIP supported')
    if not zipfile.is_zipfile(path):raise AppError('BUNDLE_UNSAFE','ZIP directory/header cannot be read')
    original,_=_hash_file(path,limits.max_total_bytes)
    with zipfile.ZipFile(path) as z:
        selected=[]
        for info in z.infolist():
            if info.is_dir():continue
            mode=(info.external_attr>>16)&0xffff
            if (stat.S_IFMT(mode) not in (0,stat.S_IFREG) or info.flag_bits&1 or info.file_size<0 or
                info.file_size>limits.max_member_bytes or
                info.file_size>limits.max_compression_ratio*max(1,info.compress_size)):
                raise AppError('BUNDLE_UNSAFE','encrypted, symlinked or oversized ZIP member')
            name=_consider(info.filename,seen,folded)
            total+=info.file_size
            if len(seen)>limits.max_members or total>limits.max_total_bytes:
                raise AppError('BUNDLE_LIMIT','expanded ZIP exceeds global limits')
            selected.append((name,info))
        for name,info in selected:
            digest=sha256();n=0
            with z.open(info) as stream:
                while True:
                    chunk=stream.read(131072)
                    if not chunk:break
                    n+=len(chunk)
                    if n>limits.max_member_bytes or n>info.file_size:raise AppError('BUNDLE_LIMIT','ZIP member expanded beyond declaration')
                    digest.update(chunk)
            if n!=info.file_size:raise AppError('BUNDLE_TAMPER','ZIP size mismatch')
            sizes[name]=n;digs[name]=digest.hexdigest()
    return BundleIndex(path,True,tuple(sorted(seen)),sizes,digs,original,limits)


def read_member(index:BundleIndex,member:str)->bytes:
    if type(index) is not BundleIndex:raise AppError('BUNDLE_INPUT','bundle index required')
    name=safe_member(member)
    if name not in index.sha256_by_member:raise AppError('BUNDLE_MEMBER','unindexed member')
    if index.path.is_symlink():raise AppError('BUNDLE_TAMPER','source replaced with symlink')
    if index.is_zip:
        digest,size=_hash_file(index.path,index.limits.max_total_bytes)
        if digest!=index.original_bundle_sha256:raise AppError('BUNDLE_TAMPER','ZIP bytes changed since index')
        with zipfile.ZipFile(index.path) as z:
            with z.open(name) as f:data=f.read(index.limits.max_member_bytes+1)
    else:
        path=index.path/name
        if path.is_symlink() or not path.is_file():raise AppError('BUNDLE_TAMPER','member replaced')
        with path.open('rb') as f:data=f.read(index.limits.max_member_bytes+1)
    if len(data)!=index.sizes[name] or sha256(data).hexdigest()!=index.sha256_by_member[name]:
        raise AppError('BUNDLE_TAMPER','member bytes changed since index')
    return data
