"""Read-only local engine access. No remote commands, eval or dynamic imports."""
from __future__ import annotations
from ..capabilities import registry
from ..errors import AppError


def offer_numeric_capabilities(allowlist:frozenset[str])->dict:
    if type(allowlist) is not frozenset or any(type(k) is not str for k in allowlist):
        raise AppError('FEDERATION_INPUT','immutable capability allowlist required')
    available=registry()
    supported=set(available['capabilities'])|set(available['exact_profiles'])
    if not allowlist.issubset(supported):
        raise AppError('FEDERATION_CAPABILITY','unknown or unapproved local numeric operation')
    return {'format':'Permansson.App.LocalEngineOffer.v1','capabilities':sorted(allowlist),
            'mode':'read_only_metadata','permission_to_execute':False,
            'lean_status':'NOT_EXECUTED','scientific_claims_verified':False}
