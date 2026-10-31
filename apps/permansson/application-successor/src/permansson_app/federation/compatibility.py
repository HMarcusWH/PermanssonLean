"""Consumer controls all allowed endpoints, versions and case scopes."""
from __future__ import annotations
from .contracts import ExchangeContract
from ..errors import AppError


def verify_compatibility(claim:ExchangeContract, expected:ExchangeContract,*,
                         approved_capabilities:frozenset[str])->dict:
    if type(claim) is not ExchangeContract or type(expected) is not ExchangeContract:
        raise AppError('FEDERATION_INPUT','typed contracts required')
    if type(approved_capabilities) is not frozenset or claim.capability not in approved_capabilities:
        raise AppError('FEDERATION_CAPABILITY','capability not explicitly approved')
    if (claim.source!=expected.source or claim.mode!=expected.mode or
        claim.subject_sha256!=expected.subject_sha256 or claim.artifact_sha256!=expected.artifact_sha256 or
        claim.capability!=expected.capability):
        raise AppError('FEDERATION_MISMATCH','cross-source/capability/mode version mismatch')
    return {'status':'CONTRACT_FIELDS_MATCH','origin_authenticated':False,
            'permission_to_execute':False,'scientific_claims_verified':False}
