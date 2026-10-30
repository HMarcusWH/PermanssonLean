"""Domain-separated RFC 8785 semantic and execution digests (versioned profile).

`semantic_digest = SHA256(ASCII(SEMANTIC_TAG) || 0x00 || RFC8785(value))` and
`execution_digest` uses its own tag over the semantic digest and the wrapper,
registry, provider, runtime, mode and resource identities.

This is a NEW profile. Historical identities (`identity.PROFILE`), raw
artifact hashes, prototype/native canonical hashes and pipeline digests are
unchanged and are not recomputed here.

Values must already be schema-normalized: reduced rational strings, safe
integers, Unicode scalar strings, string keys and explicit arrays. Encoding
uses the pinned `rfc8785` implementation, and every encoding must agree
byte-for-byte with the independent restricted encoder in `identity`; a
disagreement is an error, never a fallback. Floats and other values outside
the restricted profile are rejected; full JCS number support is not claimed.
"""
from __future__ import annotations
import hashlib
import re

import rfc8785

from .errors import AppError
from .identity import canonical_bytes as restricted_canonical_bytes

PROFILE='Permansson.App.SemanticsJCS.v1'
SEMANTIC_TAG=b'PERMANSSON_APP_SEMANTICS_JCS_V1'
EXECUTION_TAG=b'PERMANSSON_APP_EXECUTION_JCS_V1'
EXECUTION_FIELDS=frozenset({'semantic_digest','wrapper','registry','provider','runtime',
                            'mode','resource_profile'})
_HEX64=re.compile(r'[0-9a-f]{64}')


def canonical_semantics(value)->bytes:
    """RFC 8785 bytes of a schema-normalized value in the restricted profile."""
    restricted=restricted_canonical_bytes(value)
    try:
        encoded=rfc8785.dumps(value)
    except rfc8785.CanonicalizationError as exc:
        raise AppError('DIGEST_CANONICALIZATION',f'value outside RFC 8785 profile: {exc}') from exc
    if encoded!=restricted:
        raise AppError('DIGEST_IMPLEMENTATION_DISAGREEMENT',
                       'independent canonical encoders disagree; no digest issued')
    return encoded


def _tagged(tag:bytes,value)->str:
    return hashlib.sha256(tag+b'\x00'+canonical_semantics(value)).hexdigest()


def semantic_digest(value)->str:
    return _tagged(SEMANTIC_TAG,value)


def execution_digest(identity:dict)->str:
    if type(identity) is not dict or set(identity)!=EXECUTION_FIELDS:
        raise AppError('DIGEST_EXECUTION','execution identity requires exactly '
                       +', '.join(sorted(EXECUTION_FIELDS)))
    if type(identity['semantic_digest']) is not str or not _HEX64.fullmatch(identity['semantic_digest']):
        raise AppError('DIGEST_EXECUTION','semantic_digest must be 64 lowercase hex digits')
    return _tagged(EXECUTION_TAG,identity)
