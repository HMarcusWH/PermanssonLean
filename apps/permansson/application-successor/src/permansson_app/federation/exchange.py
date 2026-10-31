"""Detached exact-set evidence exchange; caller-supplied digest is not trust."""
from __future__ import annotations
from pathlib import Path
from .contracts import ExchangeContract
from ..bundle import verify_detached_bundle
from ..errors import AppError


def verify_exchange(root:Path,manifest:dict,contract:ExchangeContract,*,trusted_manifest_sha256:str)->dict:
    if type(contract) is not ExchangeContract:
        raise AppError('FEDERATION_CONTRACT','typed contract required')
    if type(trusted_manifest_sha256) is not str or len(trusted_manifest_sha256)!=64:
        raise AppError('FEDERATION_TRUST','independently sourced manifest digest required')
    checked=verify_detached_bundle(Path(root),manifest,expected_manifest_sha256=trusted_manifest_sha256)
    source=manifest['declared_source']
    if source!={'source_commit':contract.source.commit,'source_tree':contract.source.tree}:
        raise AppError('FEDERATION_SOURCE','declared source does not match contract')
    if checked['manifest_sha256']!=contract.artifact_sha256:
        raise AppError('FEDERATION_ARTIFACT','artifact identity differs from contract')
    return {'format':'Permansson.App.FederationExchangeCheck.v1','status':'DETACHED_BYTES_MATCH_PIN',
            'files_checked':checked['files_checked'],'source_authentication':'EXTERNAL_PROVENANCE_REQUIRED',
            'permission_to_execute':False,'mathematical_certification':False,
            'scientific_claims_verified':False}
