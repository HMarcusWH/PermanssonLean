"""Package actual 45-case source-positive execution as a v3.1 CI owner ZIP root.

This module never makes GitHub, independent-review or mathematical acceptance
claims.  Artifact IDs and trusted check-run identities are supplied ONLY by
the later independent GitHub artifact authenticator.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
INDEX_FORMAT = "Permansson.PR113.AdditionalControlProducerIndex.v1"
SUMMARY_FORMAT = "Permansson.PR113.OriginalPositiveRoutesCandidate.v1"
RECEIPT_FORMAT = "Permansson.PR113.OriginalCasePositiveCandidate.v1"
STATUS = "SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED"
LOGS = ("unittest_stdout.log", "unittest_stderr.log", "source_positive.log")
KEYS = ("unittest_stdout_sha256", "unittest_stderr_sha256",
        "source_positive_log_sha256")


class ProducerError(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise ProducerError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def regular(path):
    path = Path(path).absolute()
    require(not any(part.is_symlink() for part in (path, *path.parents)),
            "symlinked producer path forbidden")
    require(path.is_file(), "required producer member missing")
    return path


def validate_one(head, case_id, directory):
    """Inspect REAL source-run outputs and return original, audited bytes."""
    require(isinstance(case_id, str) and
            re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]{1,30}", case_id),
            "invalid original source case ID")
    receipt = regular(directory / "unreviewed_positive.json").read_bytes()
    data = json.loads(receipt)
    require(data.get("format") == RECEIPT_FORMAT and
            data.get("status") == STATUS and
            data.get("case_id") == case_id and
            data.get("head_sha") == head and
            data.get("positive_role") in ("COMPILER_SOURCE", "EXACT_CHECK") and
            data.get("source_positive_exit_code") == 0 and
            data.get("registered_method_exit_code") == 0 and
            data.get("actual_producing_check_run_id") is None and
            data.get("authenticated_ci_artifact") is False and
            data.get("independent_case_review") is False and
            data.get("scientific_release_approved") is False,
            "positive owner does not represent successful, unreviewed execution")
    checked = {}
    for filename, key in zip(LOGS, KEYS):
        raw = regular(directory / filename).read_bytes()
        require(len(raw) <= 4*1024*1024 and
                isinstance(data.get(key), str) and
                SHA256.fullmatch(data[key]) and
                digest(raw) == data[key],
                "original producer log digest/size mismatch: " + case_id)
        checked[filename] = raw
    stderr = checked["unittest_stderr.log"].decode("utf-8", errors="replace")
    leanlog = checked["source_positive.log"].decode("utf-8",
                                                    errors="replace").lower()
    require("Ran 1 test" in stderr and "OK" in stderr and
            "skipped=" not in stderr and "FAILED (" not in stderr and
            "error:" not in leanlog and "sorryax" not in leanlog,
            "actual source control was not a successful exact-scope execution")
    return receipt, checked


def owner_manifest(head, run_id, run_attempt, source, destination):
    require(isinstance(head, str) and SHA40.fullmatch(head),
            "exact real source head required")
    require(type(run_id) is int and run_id > 0 and
            type(run_attempt) is int and run_attempt > 0,
            "real GitHub run/attempt identity required")
    source = Path(source).resolve(strict=True)
    destination = Path(destination).absolute()
    require(not destination.exists() and not destination.is_symlink() and
            not destination.is_relative_to(source) and
            not destination.is_relative_to(
                Path(__file__).resolve().parents[2]),
            "fresh detached artifact output required")
    summary = json.loads(regular(
        source / "unreviewed_45_positive_routes.json").read_bytes())
    records = summary.get("positive_route_records")
    require(summary.get("format") == SUMMARY_FORMAT and
            summary.get("status") ==
                "EXECUTED_NO_PRODUCING_CI_OR_MATH_REVIEW" and
            summary.get("head_sha") == head and
            summary.get("actual_positive_cases") == 45 and
            summary.get("authenticated_ci_artifact") is False and
            summary.get("scientific_release_approved") is False and
            isinstance(records, list) and len(records) == 45,
            "complete original 45-case real positive-run manifest missing")
    names = [row.get("case_id") for row in records
             if isinstance(row, dict)]
    require(len(names) == 45 and len(set(names)) == 45,
            "duplicate or malformed case-level execution report")
    require(set(names) == set(p.name for p in source.iterdir() if p.is_dir()),
            "source-positive report omitted or invented a case directory")
    # Verify ALL original bytes before writing an artifact at all.
    verified = []
    for cid in sorted(names):
        report = next(row for row in records if row["case_id"] == cid)
        actual, logs = validate_one(head, cid, source / cid)
        require(json.loads(actual) == report,
                "source original per-case receipt changed after summary")
        verified.append((cid, actual, logs))
    destination.mkdir(parents=True)
    (destination / "positive").mkdir()
    owners = []
    for cid, receipt, logs in verified:
        path = destination / "positive" / cid
        path.mkdir()
        (path / "unreviewed_positive.json").write_bytes(receipt)
        for name, raw in logs.items():
            (path / name).write_bytes(raw)
        member = "positive/" + cid + "/unreviewed_positive.json"
        owners.append({
            "kind": "original_positive",
            "owner_id": cid,
            "receipt_member": member,
            "receipt_sha256": digest(receipt),
        })
    index = {
        "format": INDEX_FORMAT,
        "head_sha": head,
        "github_run_id": run_id,
        "github_run_attempt": run_attempt,
        "accepted_cases": 0,
        "accepted_claims": 0,
        "independent_review": False,
        "owners": owners,
    }
    (destination / "owner_index.json").write_text(
        json.dumps(index, sort_keys=True, indent=2) + "\n")
    return index


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head", required=True)
    p.add_argument("--run-id", required=True, type=int)
    p.add_argument("--run-attempt", required=True, type=int)
    p.add_argument("--source", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    a = p.parse_args(argv)
    try:
        result = owner_manifest(a.head, a.run_id, a.run_attempt,
                                a.source, a.output)
    except (ProducerError, OSError, ValueError, KeyError, TypeError) as exc:
        print("PR113 authentic source-positive CI artifact BLOCKED:", exc,
              file=sys.stderr)
        return 2
    print(json.dumps({"status": "45_UNREVIEWED_OWNERS_PACKED",
                      "owner_count": len(result["owners"])},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
