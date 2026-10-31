"""Separate immutable identities for source, application, paper and execution.

A syntactically valid commit hash is never treated as an authenticated commit.
"""
from __future__ import annotations
from dataclasses import dataclass
import re
from .errors import AppError
from .identity import semantic_identity

_SHA40=re.compile(r"[a-f0-9]{40}\Z")
_SHA256=re.compile(r"[a-f0-9]{64}\Z")
_VERSION=re.compile(r"[A-Za-z0-9][A-Za-z0-9._+-]{0,79}\Z")


def sha40(value:object,label:str='source') -> str:
    if type(value) is not str or not _SHA40.fullmatch(value):
        raise AppError('VERSION_SOURCE',label+' must be an exact lowercase 40-digit Git SHA')
    return value


def sha256(value:object,label:str='digest') -> str:
    if type(value) is not str or not _SHA256.fullmatch(value):
        raise AppError('VERSION_DIGEST',label+' must be an exact lowercase SHA-256')
    return value


def version(value:object,label:str='version') -> str:
    if type(value) is not str or not _VERSION.fullmatch(value):
        raise AppError('VERSION_FORMAT',label+' has an invalid version identifier')
    return value


@dataclass(frozen=True)
class SourcePin:
    repository: str
    commit: str
    tree: str
    application: str
    research: str
    paper: str

    @classmethod
    def parse(cls,data:object) -> 'SourcePin':
        if type(data) is not dict or set(data)!={'repository','commit','tree','application','research','paper'}:
            raise AppError('VERSION_INPUT','source pin requires six exact fields')
        if data['repository']!='HMarcusWH/PermanssonLean':
            raise AppError('VERSION_REPOSITORY','unknown source repository')
        return cls(data['repository'],sha40(data['commit'],'commit'),sha40(data['tree'],'tree'),
                   version(data['application'],'application'),version(data['research'],'research'),version(data['paper'],'paper'))

    def identity(self) -> dict:
        return semantic_identity('versioned-source-pin',self.to_dict())

    def to_dict(self) -> dict:
        return {'repository':self.repository,'commit':self.commit,'tree':self.tree,
                'application':self.application,'research':self.research,'paper':self.paper}


def matching_source(expected:SourcePin,claimed:SourcePin)->bool:
    """Exact match; never proves a remote commit or bundle is authentic."""
    return type(expected) is SourcePin and type(claimed) is SourcePin and expected==claimed
