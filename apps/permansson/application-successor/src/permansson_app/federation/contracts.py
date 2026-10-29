"""Versioned federation scope with exact source and capability pins."""
from __future__ import annotations
from dataclasses import dataclass
from ..versioning import SourcePin,sha256
from ..errors import AppError

@dataclass(frozen=True)
class ExchangeContract:
    source:SourcePin
    capability:str
    mode:str
    subject_sha256:str
    artifact_sha256:str
    origin_authenticated:bool=False

    @classmethod
    def parse(cls,raw:object)->'ExchangeContract':
        keys={'format','source','capability','mode','subject_sha256','artifact_sha256'}
        if type(raw) is not dict or set(raw)!=keys or raw['format']!='Permansson.App.FederationContract.v1':
            raise AppError('FEDERATION_FORMAT','unrecognized exchange contract')
        if type(raw['capability']) is not str or not raw['capability'] or len(raw['capability'])>160:
            raise AppError('FEDERATION_CAPABILITY','missing declared capability')
        if raw['mode'] not in ('numeric','evidence_only'):
            raise AppError('FEDERATION_MODE','unapproved exchange mode')
        return cls(SourcePin.parse(raw['source']),raw['capability'],raw['mode'],
                   sha256(raw['subject_sha256']),sha256(raw['artifact_sha256']))
