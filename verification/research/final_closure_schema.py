"""Validate the exact bounded detached-receipt v2 schema without optional packages.

Only the schema keywords in this repository's v2 dialect are supported.
Unknown keywords fail closed. Passing this validator does not authenticate CI,
Lean proofs, Git objects, or independent reviews.
"""
from __future__ import annotations

import json
from pathlib import Path
import re

from final_closure_case_receipts import EvidenceError, ROOT

SCHEMA = ROOT / "research/paper_closures/post_merge_112/detached_receipts_v2.schema.json"
KEYWORDS = frozenset({
    "$schema", "$id", "title", "description", "type", "properties",
    "additionalProperties", "required", "items", "prefixItems", "const",
    "enum", "pattern", "minimum", "minLength", "minItems", "maxItems",
    "uniqueItems", "oneOf", "allOf", "if", "then",
})


def _check_spec(schema, where="$"):
    if not isinstance(schema, dict):
        raise EvidenceError(f"malformed receipt schema at {where}")
    unknown = set(schema) - KEYWORDS
    if unknown:
        raise EvidenceError(f"unsupported receipt schema keyword at {where}: {sorted(unknown)}")
    for key, value in schema.get("properties", {}).items():
        _check_spec(value, where + "." + key)
    for key in ("items", "if", "then"):
        if key in schema:
            _check_spec(schema[key], where + "." + key)
    for key in ("prefixItems", "oneOf", "allOf"):
        for idx, item in enumerate(schema.get(key, [])):
            _check_spec(item, f"{where}.{key}[{idx}]")


def _type_matches(value, kind):
    checks = {
        "object": type(value) is dict,
        "array": type(value) is list,
        "string": type(value) is str,
        "integer": type(value) is int,
        "number": type(value) in (int, float),
        "boolean": type(value) is bool,
        "null": value is None,
    }
    if kind not in checks:
        raise EvidenceError("unsupported receipt schema type: " + str(kind))
    return checks[kind]


def _matches(value, schema):
    try:
        _validate(value, schema)
        return True
    except EvidenceError:
        return False


def _validate(value, schema, where="$"):
    if "type" in schema and not _type_matches(value, schema["type"]):
        raise EvidenceError(f"{where}: invalid JSON type")
    if "const" in schema and (
            type(value) is not type(schema["const"]) or value != schema["const"]):
        raise EvidenceError(f"{where}: wrong required value")
    if "enum" in schema and not any(
            type(value) is type(x) and value == x for x in schema["enum"]):
        raise EvidenceError(f"{where}: unexpected enum value")
    if "oneOf" in schema and sum(_matches(value, s) for s in schema["oneOf"]) != 1:
        raise EvidenceError(f"{where}: ambiguous or missing variant")
    for sub in schema.get("allOf", []):
        _validate(value, sub, where)
    if "if" in schema and _matches(value, schema["if"]) and "then" in schema:
        _validate(value, schema["then"], where)
    if type(value) is str:
        if len(value) < schema.get("minLength", 0):
            raise EvidenceError(f"{where}: short string")
        if "pattern" in schema and re.search(schema["pattern"], value) is None:
            raise EvidenceError(f"{where}: invalid string")
    if type(value) in (int, float) and "minimum" in schema:
        if value < schema["minimum"]:
            raise EvidenceError(f"{where}: below minimum")
    if type(value) is dict:
        if any(x not in value for x in schema.get("required", [])):
            raise EvidenceError(f"{where}: required property missing")
        allowed = schema.get("properties", {})
        if schema.get("additionalProperties") is False and set(value) - set(allowed):
            raise EvidenceError(f"{where}: unknown property")
        for key, sub in allowed.items():
            if key in value:
                _validate(value[key], sub, where + "." + key)
    if type(value) is list:
        if len(value) < schema.get("minItems", 0) or (
                "maxItems" in schema and len(value) > schema["maxItems"]):
            raise EvidenceError(f"{where}: wrong array length")
        if schema.get("uniqueItems"):
            encoded = [json.dumps(x, sort_keys=True, ensure_ascii=False)
                       for x in value]
            if len(encoded) != len(set(encoded)):
                raise EvidenceError(f"{where}: duplicate item")
        for i, sub in enumerate(schema.get("prefixItems", [])):
            if i < len(value):
                _validate(value[i], sub, f"{where}[{i}]")
        if "items" in schema:
            for i, item in enumerate(value):
                _validate(item, schema["items"], f"{where}[{i}]")


def validate_overlay(payload):
    """Schema gate for input/output; never converts candidates into approvals."""
    try:
        schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise EvidenceError("canonical detached receipt schema unavailable") from exc
    _check_spec(schema)
    _validate(payload, schema)
    for family in ("compiler_axiom_receipts", "positive_test_receipts",
                   "semantic_negative_receipts"):
        for receipt in payload[family]:
            if not receipt["case_ids"] and not receipt["claim_ids"]:
                raise EvidenceError(
                    "unowned proof/test receipt in " + family)
    return payload
