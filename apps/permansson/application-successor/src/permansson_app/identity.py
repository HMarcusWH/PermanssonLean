"""Opt-in typed-rational JSON canonicalization. Historical digests remain unchanged.

Only JSON exact integers in the IEEE-754 safe range, strings, booleans and null are
accepted. All mathematically rational fields must be normalized *by the owning
schema* before reaching this function. This is a deliberately versioned strict
subset of RFC 8785/JCS, not a floating-point implementation of JCS.
"""
from __future__ import annotations
import hashlib
import json
from fractions import Fraction
from .errors import AppError

PROFILE = "Permansson.App.TypedRationalJCS.v1"
MAX_SAFE_INT = 2**53 - 1


def rational_text(value: Fraction) -> str:
    if type(value) is not Fraction:
        raise AppError("IDENTITY_TYPE", "rational value must be exact Fraction")
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def _ordered_json(value) -> str:
    t = type(value)
    if value is None: return 'null'
    if t is bool: return 'true' if value else 'false'
    if t is int:
        if abs(value)>MAX_SAFE_INT:
            raise AppError("IDENTITY_NUMBER", "unsafe JSON integer; normalize to a typed decimal string")
        return str(value)
    if t is str:
        if any(0xD800 <= ord(c) <= 0xDFFF for c in value):
            raise AppError("IDENTITY_UNICODE", "unpaired surrogate")
        return json.dumps(value,ensure_ascii=False,separators=(',',':'))
    if t is list or t is tuple:
        return '['+','.join(_ordered_json(v) for v in value)+']'
    if t is dict:
        if any(type(k) is not str for k in value):
            raise AppError("IDENTITY_TYPE", "JSON keys must be strings")
        keys = sorted(value, key=lambda k:k.encode('utf-16-be','strict'))
        return '{'+','.join(_ordered_json(k)+':'+_ordered_json(value[k]) for k in keys)+'}'
    raise AppError("IDENTITY_TYPE", "float, Fraction and unsupported objects cannot be canonicalized implicitly")


def canonical_bytes(value) -> bytes:
    return _ordered_json(value).encode('utf-8')


def semantic_identity(kind: str, normalized_payload: dict) -> dict:
    if type(kind) is not str or not kind or type(normalized_payload) is not dict:
        raise AppError("IDENTITY_TYPE", "kind and schema-normalized object required")
    payload = {"profile":PROFILE,"kind":kind,"payload":normalized_payload}
    return {"profile":PROFILE,"sha256":hashlib.sha256(canonical_bytes(payload)).hexdigest()}
