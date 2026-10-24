"""Revalidate actual v3.1 control execution bytes inside authenticated GH ZIPs.

This validates retained bytes and diagnostic kinds, NOT mathematical
relevance, historical security approval, reviewer authority, or release.
Call only after final_closure_extra_producers_v31 authenticates the actual
run, job, check, workflow Git blob and original GitHub artifact digest.
"""
from __future__ import annotations

import hashlib
import json
import re

from final_closure_producer_bytes import inspect_zip, ProducerBytesError

SHA256 = re.compile(r"^[0-9a-f]{64}$")
CLAIMS = frozenset(("Q1", "Q2", "Q3", "M1", "M2", "M3",
                    "N1", "N2", "N3", "D8", "D9"))
STATUSES = {
    "original_positive": "SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED",
    "legacy_negative": "SOURCE_APPENDED_REPLAYED_UNREVIEWED_NOT_CI_ATTRIBUTED",
    "claim_pair": "LEAN_POSITIVE_AND_FALSE_MUTANT_EXECUTED_UNREVIEWED",
}
REQUIRED_CLAIM_MEMBERS = frozenset((
    "original.lean", "appended_false.lean",
    "positive_lean.log", "negative_lean.log",
    "positive_test.stdout", "positive_test.stderr",
    "negative_test.stdout", "negative_test.stderr",
))


class RealControlError(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise RealControlError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def json_bytes(raw):
    need(type(raw) is bytes and len(raw) <= 4 * 1024 * 1024,
         "unbounded or missing source control JSON")
    try:
        return json.loads(raw)
    except (ValueError, UnicodeError, TypeError) as exc:
        raise RealControlError("original control receipt is invalid JSON") from exc


def member(members, name, expected):
    need(isinstance(name, str) and name and
         name in members and
         type(members[name]) is bytes and
         len(members[name]) <= 4 * 1024 * 1024 and
         isinstance(expected, str) and SHA256.fullmatch(expected) and
         sha(members[name]) == expected,
         "original producer member not present at authenticated digest: " +
         str(name))
    return members[name]


def source_clean_negative(log):
    text = log.decode("utf-8", errors="replace").lower()
    need("error:" in text and
         any(kind in text for kind in
             ("type mismatch", "unsolved goals", "application type mismatch")),
         "Lean did not reject the intended mathematical proof goal")
    need(not any(kind in text for kind in (
        "unknown module", "unknown identifier", "failed to import",
        "parser error", "syntax error", "out of memory", "timed out",
        "timeout", "maximum number of heartbeats",
        "failed to synthesize", "sorryax", "unknown tactic",
    )), "Lean failed for tooling/parser/resource rather than mathematics")


def verify_owner(kind, owner_id, receipt_name, members, head):
    """Return an unreviewed byte-evidence diagnostic or fail closed."""
    need(kind in STATUSES and isinstance(owner_id, str) and owner_id and
         isinstance(receipt_name, str) and receipt_name.endswith(".json") and
         receipt_name in members,
         "missing typed original control owner")
    wrapper = json_bytes(members[receipt_name])
    owner_key = "claim_id" if kind == "claim_pair" else "case_id"
    need(wrapper.get("status") == STATUSES[kind] and
         wrapper.get("head_sha") == head and
         wrapper.get(owner_key) == owner_id and
         wrapper.get("scientific_release_approved") is False,
         "source execution owner falsely promoted or mismatched")
    base = receipt_name.rsplit("/", 1)[0] + "/"
    if kind == "original_positive":
        need(wrapper.get("positive_role") in ("COMPILER_SOURCE", "EXACT_CHECK") and
             type(wrapper.get("source_positive_exit_code")) is int and
             wrapper["source_positive_exit_code"] == 0 and
             type(wrapper.get("registered_method_exit_code")) is int and
             wrapper["registered_method_exit_code"] == 0 and
             wrapper.get("actual_producing_check_run_id") is None and
             wrapper.get("authenticated_ci_artifact") is False and
             wrapper.get("independent_case_review") is False,
             "invalid original positive control execution")
        logs = (
            ("unittest_stdout.log", "unittest_stdout_sha256"),
            ("unittest_stderr.log", "unittest_stderr_sha256"),
            ("source_positive.log", "source_positive_log_sha256"),
        )
        raw = {}
        for name, digest_field in logs:
            raw[name] = member(members, base + name, wrapper.get(digest_field))
        test = raw["unittest_stderr.log"].decode("utf-8", errors="replace")
        compiled = raw["source_positive.log"].decode("utf-8", errors="replace").lower()
        need("Ran 1 test" in test and "OK" in test and
             "skipped=" not in test and "FAILED (" not in test and
             "error:" not in compiled and "sorryax" not in compiled,
             "registered true control or Lean source did not pass")
        return {"kind": kind, "owner_id": owner_id,
                "actual_log_members_checked": 3}

    if kind == "claim_pair":
        need(owner_id in CLAIMS and
             wrapper.get("format") == "Permansson.PR113.ClaimOnlyControlCandidate.v1" and
             wrapper.get("claim_ids") == [owner_id] and
             wrapper.get("case_ids") == [] and
             type(wrapper.get("lean_positive_exit_code")) is int and
             wrapper.get("lean_positive_exit_code") == 0 and
             type(wrapper.get("lean_negative_exit_code")) is int and
             wrapper["lean_negative_exit_code"] != 0 and
             wrapper.get("actual_ci_check_run_id") is None and
             wrapper.get("independent_mathematical_review") is False and
             wrapper.get("accepted_claim") is False,
             "claim positive/negative paths are missing or self-approved")
        hashes = wrapper.get("retained_member_sha256")
        need(isinstance(hashes, dict) and set(hashes) == REQUIRED_CLAIM_MEMBERS,
             "claim proof source/log set is incomplete")
        content = {
            name: member(members, base + name, hashes[name])
            for name in REQUIRED_CLAIM_MEMBERS
        }
        source = content["original.lean"]
        false = content["appended_false.lean"]
        need(len(source) > 0 and false.startswith(source) and
             len(false) > len(source), "claim false proof was not append-only")
        append = false[len(source):].decode("utf-8", errors="strict")
        need(not re.search(
                 r"(?mi)^\s*(?:import|axiom|constant|opaque|set_option)\b",
                 append) and
             not re.search(r"(?i)\b(?:sorry|sorryAx|admit)\b", append),
             "claim mutant silently changed its proof assumptions")
        source_clean_negative(content["negative_lean.log"])
        pl = content["positive_lean.log"].decode("utf-8", errors="replace").lower()
        need("error:" not in pl and "sorryax" not in pl and
             "ok" in content["positive_test.stderr"].decode(
                 "utf-8", errors="replace").lower() and
             "ok" in content["negative_test.stderr"].decode(
                 "utf-8", errors="replace").lower(),
             "claim source positive / registered test failed")
        return {"kind": kind, "owner_id": owner_id,
                "actual_log_members_checked": len(content)}

    need(wrapper.get("independent_case_review") is False and
         wrapper.get("actual_ci_check_run_id") is None and
         wrapper.get("mathematical_acceptance") is False and
         type(wrapper.get("historical_producing_artifact_id")) is int and
         wrapper["historical_producing_artifact_id"] > 0,
         "historical source-negative owner fabricated current CI acceptance")
    replay_raw = member(
        members, wrapper.get("execution_receipt_member"),
        wrapper.get("execution_receipt_sha256"))
    replay = json_bytes(replay_raw)
    raw_zip = members.get(wrapper.get("semantic_zip_member"))
    need(type(raw_zip) is bytes and
         len(raw_zip) <= 64 * 1024 * 1024 and
         sha(raw_zip) == wrapper.get("semantic_zip_sha256"),
         "historical original source-appended replay ZIP missing or modified")
    try:
        nested = inspect_zip(raw_zip)
    except ProducerBytesError as exc:
        raise RealControlError("unsafe historical nested compiler ZIP") from exc
    mut = replay.get("mutation_record")
    need(replay.get("format") ==
            "Permansson.LegacyAppendOnlyReplayCandidate.v1" and
         replay.get("status") ==
            "REPLAYED_APPEND_ONLY_UNREVIEWED_UNATTRIBUTED" and
         replay.get("case_id") == owner_id and
         replay.get("head_sha") == head and
         replay.get("independent_review") is False and
         replay.get("mathematical_acceptance") is False and
         replay.get("ci_check_run_id") is None and
         isinstance(mut, dict) and
         mut.get("head_sha") == head and
         mut.get("case_ids") == [owner_id] and
         mut.get("outcome") == "REJECTED_SEMANTIC" and
         type(mut.get("compiler_exit_code")) is int and
         mut["compiler_exit_code"] != 0 and
         isinstance(mut.get("positive_control"), dict) and
         mut["positive_control"].get("compiled") is True and
         mut["positive_control"].get("exit_code") == 0,
         "historical replay did not actually execute source positive and false")
    pos = mut["positive_control"]
    poslog = member(nested, pos.get("log_member"), pos.get("log_sha256"))
    neglog = member(nested, mut.get("log_member"), mut.get("log_sha256"))
    original = member(nested, mut.get("original_lean_source_member"),
                      mut.get("original_lean_source_sha256"))
    false = member(nested, mut.get("mutant_source_member"),
                   mut.get("mutant_source_sha256"))
    need(false.startswith(original) and len(false) > len(original),
         "legacy false assertion did not retain full original Lean provider")
    need("error:" not in poslog.decode("utf-8", errors="replace").lower(),
         "historical original positive control did not compile")
    source_clean_negative(neglog)
    return {"kind": kind, "owner_id": owner_id,
            "actual_log_members_checked": 4}


def validate_executed_controls(head, contract, zipped):
    """Validate all 76 original GH ZIP owner payloads, without review claims."""
    need(isinstance(contract, dict) and contract.get("head_sha") == head and
         isinstance(zipped, dict), "original v3.1 CI payload unavailable")
    owners = {}
    jobs = contract.get("producers")
    need(isinstance(jobs, list) and jobs and
         {j.get("artifact_id") for j in jobs} == set(zipped),
         "producer artifacts not in exact declared set")
    for job in jobs:
        raw = zipped[job["artifact_id"]]
        need(type(raw) is bytes, "missing genuine original ZIP bytes")
        try:
            members = inspect_zip(raw)
        except ProducerBytesError as exc:
            raise RealControlError("unsafe original source producer ZIP") from exc
        for row in job["owners"]:
            key = (row["kind"], row["owner_id"])
            need(key not in owners, "duplicate source control owner")
            name = row["receipt_member"]
            member(members, name, row["receipt_sha256"])
            owners[key] = verify_owner(
                row["kind"], row["owner_id"], name, members, head)
    from collections import Counter
    n = Counter(kind for kind, _ in owners)
    need(len(owners) == 76 and n == {
         "original_positive": 45, "legacy_negative": 20, "claim_pair": 11
    }, "original complete 45/20/11 source-control ownership incomplete")
    need({k[1] for k in owners if k[0] == "claim_pair"} == CLAIMS,
         "claim owner identity differs from original eleven")
    return {
        "format": "Permansson.PR113.GenuineSourceExecutionBytes.v1",
        "status": "ACTUAL_CONTROL_BYTES_REVALIDATED_UNREVIEWED",
        "source_head": head,
        "source_owner_count": 76,
        "claim_positive_negative_directions": 22,
        "execution_log_members_checked": sum(
            row["actual_log_members_checked"] for row in owners.values()),
        "independent_review": False,
        "mathematical_acceptance": False,
        "publication_approved": False,
    }
