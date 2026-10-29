"""Exact-H case route and authentic original-capture binding for legacy negatives.

A replay is not independently meaningful merely because a Lean false mutant
failed. Its source test, theorem provider, named method and *particular*
compiler observation must belong to the same original case, and the retained
original observation must come from the genuine authenticated 8-shard legacy
GitHub source artifact.

This is source provenance, NOT a mathematical relevance decision, migration
approval or release certificate.
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import PurePosixPath
import re

CASE_METHOD = re.compile(r"^test_[A-Za-z0-9_]+$")
EVENT = re.compile(r"^event-[0-9]+-[0-9]{6}$")
SHA256 = re.compile(r"^[a-f0-9]{64}$")


class LegacyRouteError(ValueError):
    pass


def demand(ok, reason):
    if not ok:
        raise LegacyRouteError(reason)


def digest(raw):
    demand(type(raw) is bytes, "source bytes must be raw original bytes")
    return hashlib.sha256(raw).hexdigest()


def json_record(raw):
    demand(type(raw) is bytes and 0 < len(raw) <= 4*1024*1024,
           "historical original manifest has no bounded raw bytes")
    try:
        obj = json.loads(raw)
    except (ValueError, UnicodeError, TypeError) as exc:
        raise LegacyRouteError("historical original manifest invalid") from exc
    demand(isinstance(obj, dict), "historical manifest is not a JSON object")
    return obj


def single_test_class(raw, method):
    """An actual class method, not a filename/owner string or nested fixture."""
    try:
        parsed = ast.parse(raw.decode("utf-8"))
    except (UnicodeError, SyntaxError) as exc:
        raise LegacyRouteError("selected original Python source is not parseable") from exc
    matches = [
        n.name for n in parsed.body
        if isinstance(n, ast.ClassDef)
        and sum(
            isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))
            and m.name == method
            for m in n.body) == 1
    ]
    demand(len(matches) == 1, "original negative test method not uniquely defined")
    return matches[0]


def bind_legacy(head, owner_id, original_receipt, mutation, wrapper,
                original_lean, appended_false, *, source,
                authenticated_original):
    """Verify route, theorem bytes, exact-H method and original GH observation."""
    demand(source is not None and getattr(source, "head", None) == head,
           "legacy original route requires committed exact-H canonical maps")
    case = source.cases.get(owner_id)
    demand(isinstance(case, dict) and case.get("effective_accepted") is False,
           "legacy negative is not an unaccepted original criterion")
    test_path = original_receipt.get("selected_test_path")
    method = original_receipt.get("selected_method")
    provider = original_receipt.get("original_provider_path")
    event = original_receipt.get("original_observation_id")
    demand(isinstance(test_path, str)
           and test_path.startswith("verification/research/test_")
           and test_path.endswith(".py")
           and ".." not in PurePosixPath(test_path).parts
           and isinstance(method, str) and CASE_METHOD.fullmatch(method)
           and isinstance(provider, str)
           and provider.startswith("PermanssonResearch/")
           and provider.endswith(".lean")
           and ".." not in PurePosixPath(provider).parts
           and isinstance(event, str) and EVENT.fullmatch(event),
           "legacy selected test/provider/observation identity incomplete")
    routes = [r for r in case.get("test_method_candidates", ())
              if isinstance(r, dict)
              and r.get("path") == test_path
              and r.get("method") == method
              and r.get("role") == "SEMANTIC_NEGATIVE"]
    demand(len(routes) == 1, "legacy negative is not this case's registered method")
    allowed = {
        r.get("path") for key in (
            "historical_proof_declarations", "new_claim_source_candidates"
        ) for r in case.get(key, ()) if isinstance(r, dict)
    }
    demand(provider in allowed, "legacy negative borrows a foreign theorem provider")
    test_bytes = source.blob(test_path)
    original = source.blob(provider)
    cls = single_test_class(test_bytes, method)
    demand(original == original_lean
           and appended_false.startswith(original)
           and len(appended_false) > len(original),
           "legacy false mutant is not appended to its original committed provider")
    demand(original_receipt.get("replayed_false_source_sha256")
           == digest(appended_false)
           and mutation.get("head_sha") == head
           and mutation.get("test_path") == test_path
           and mutation.get("test_name") == method
           and mutation.get("source_sha256") == digest(test_bytes)
           and mutation.get("original_lean_source_path") == provider
           and mutation.get("original_lean_source_sha256") == digest(original),
           "legacy compile receipt does not bind named test/provider source")
    demand(original_receipt.get("head_sha") == head
           and original_receipt.get("case_id") == owner_id
           and mutation.get("case_ids") == [owner_id]
           and mutation.get("claim_ids") == [],
           "legacy source receipt uses a borrowed case or claim owner")

    expected_sha = original_receipt.get("legacy_test_manifest_sha256")
    metadata_sha = original_receipt.get("raw_observation_sha256")
    captured_sha = original_receipt.get("captured_false_source_sha256")
    demand(all(isinstance(x, str) and SHA256.fullmatch(x) for x in (
        expected_sha, metadata_sha, captured_sha)),
        "legacy capture manifest/observation/source SHA-256 missing")
    artifact_id = wrapper.get("historical_producing_artifact_id")
    demand(type(artifact_id) is int and artifact_id > 0
           and isinstance(authenticated_original, dict)
           and authenticated_original.get("status") ==
               "REAL_PRODUCING_BYTES_UNREVIEWED"
           and authenticated_original.get("head_sha") == head,
           "legacy capture not bound to authenticated exact-H original producers")
    produced = authenticated_original.get("producers", {}).get(artifact_id)
    demand(isinstance(produced, dict)
           and produced.get("kind") == "legacy"
           and produced.get("head_sha") == head
           and type(produced.get("check_run_id")) is int,
           "legacy original observation borrowed a different producer shard")
    members = produced.get("members")
    demand(isinstance(members, dict), "legacy original producing ZIP members missing")
    # Precisely identify one real case/test source manifest by SHA, not by
    # a caller-supplied member index. Ambiguity fails closed.
    options = [
        (name, raw)
        for name, raw in members.items()
        if isinstance(name, str)
        and name.startswith(owner_id + "/test-")
        and name.endswith("/unreviewed_test_manifest.json")
        and type(raw) is bytes
        and digest(raw) == expected_sha
    ]
    demand(len(options) == 1, "selected original historical test capture missing or duplicated")
    name, raw = options[0]
    captured = json_record(raw)
    demand(captured.get("format") ==
               "Permansson.LegacyCaseTestExecutionCandidate.v1"
           and captured.get("case_id") == owner_id
           and captured.get("status") == "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED"
           and captured.get("test_file") == test_path
           and captured.get("source_test_sha256") == digest(test_bytes)
           and captured.get("test_exit_code") == 0
           and captured.get("independent_review") is False
           and captured.get("release_approved") is False
           and method in captured.get("selected_methods", ()),
           "original GitHub producing test manifest does not match replayed route")
    prefix = name[:-len("unreviewed_test_manifest.json")]
    observation_member = prefix + "raw_compiler/" + event + "/observation.json"
    source_member = prefix + "raw_compiler/" + event + "/source.lean"
    metadata = members.get(observation_member)
    false_original = members.get(source_member)
    demand(type(metadata) is bytes and digest(metadata) == metadata_sha
           and type(false_original) is bytes and digest(false_original) == captured_sha,
           "original compiler observation/false-source bytes do not match GitHub ZIP")
    observed = json_record(metadata)
    demand(observed.get("format") ==
               "Permansson.LegacyLeanCompilerObservation.v1"
           and observed.get("case_id_unverified") == owner_id
           and observed.get("selected_method_unverified") == method
           and observed.get("source_sha256") == captured_sha,
           "captured event belongs to another case/method/source")
    # A syntactically successful original-source mutation does not establish
    # scientific relevance; independent review is a separate requirement.
    return {
        "case_id": owner_id, "selected_method": method,
        "selected_test_class": cls, "source_provider": provider,
        "original_producer_artifact_id": artifact_id,
        "original_producer_check_run_id": produced["check_run_id"],
        "observation_id": event,
        "exact_h_source_and_original_capture_bound": True,
        "independent_mathematical_review": False,
    }
