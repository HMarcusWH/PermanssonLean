"""Populate only unit cases from complete, exact-source downloaded CI reports.

No network or repository mutation. A source is JSON or ARTIFACT.zip!MEMBER.json.
The caller independently establishes the intended H/B/S and publisher provenance.
Nine nonunit technical cases remain pending; twelve operational cases stay deferred.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path
import re
import sys
import zipfile

ACCEPTED = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
REPOSITORY = "HMarcusWH/PermanssonLean"
SUITES = ("reference", "preservation", "tex", "context", "workflow", "archive")
JSON_LIMIT = 8 * 1024 * 1024
ZIP_LIMIT = 64 * 1024 * 1024
CONTEXT_FIELDS = ("repository", "accepted_release", "event", "pr_number", "head_sha", "base_sha",
                  "checked_sha", "checked_tree", "run_id", "run_attempt", "event_sha256", "scope")


class ReceiptError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise ReceiptError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def strict_json(raw):
    require(len(raw) <= JSON_LIMIT, "JSON exceeds 8 MiB")
    def pairs(items):
        result = {}
        for name, value in items:
            require(name not in result, "Duplicate JSON key: " + name)
            result[name] = value
        return result
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                          parse_constant=lambda value: (_ for _ in ()).throw(ReceiptError("Non-finite JSON number")))
    except (ValueError, UnicodeError) as exc:
        raise ReceiptError("Invalid JSON: " + str(exc)) from exc


def read_source(source):
    """Read bounded payloads without extracting artifact members."""
    archive_name, delimiter, member = source.partition("!")
    path = Path(archive_name).resolve()
    require(path.is_file(), "Missing source: " + archive_name)
    limit = ZIP_LIMIT if delimiter else JSON_LIMIT
    require(path.stat().st_size <= limit, "Source exceeds its fixed budget")
    with path.open("rb") as stream:
        raw_file = stream.read(limit + 1)
    require(len(raw_file) <= limit, "Source grew beyond its fixed budget")
    identity = {"source": str(path), "container_sha256": sha256(raw_file), "container_bytes": len(raw_file)}
    if delimiter:
        require(member and not member.startswith("/") and "\\" not in member and ":" not in member
                and all(part not in {"", ".", ".."} for part in member.split("/")), "Unsafe report member name")
        try:
            with zipfile.ZipFile(io.BytesIO(raw_file)) as archive:
                entries = [entry for entry in archive.infolist() if entry.filename == member]
                require(len(entries) == 1, "Missing or duplicate report member: " + member)
                entry = entries[0]
                require(not entry.is_dir() and entry.file_size <= JSON_LIMIT and not entry.flag_bits & 1,
                        "Unsupported or oversized report member")
                require((entry.external_attr >> 16) & 0o170000 != 0o120000, "Report member is a symlink")
                with archive.open(entry) as stream:
                    raw = stream.read(JSON_LIMIT + 1)
                require(len(raw) == entry.file_size and len(raw) <= JSON_LIMIT, "Report member length mismatch")
        except (OSError, zipfile.BadZipFile, RuntimeError) as exc:
            raise ReceiptError("Cannot read report artifact: " + str(exc)) from exc
        identity["member"] = member
    else:
        raw = raw_file
    identity.update(sha256=sha256(raw), bytes=len(raw))
    return strict_json(raw), identity


def expected_cases():
    result = {}
    for prefix, count, suite in (("REF", 15, "reference"), ("PRES", 23, "preservation"),
                                 ("TEX", 20, "tex"), ("ARCH", 27, "archive")):
        for number in range(1, count + 1):
            result[f"{prefix}-{number:02}"] = (suite, "integration" if prefix == "ARCH" and number in {14, 23} else "unit")
    for number in range(1, 12):
        level = "unit" if number in {3, 6, 7, 9} else "review" if number == 10 else "live_pr"
        suite = "context" if number in {3, 9} else "workflow" if number in {6, 7} else None
        result[f"CI-{number:02}"] = (suite, level)
    for number in range(1, 13):
        result[f"OPS-{number:02}"] = (None, "authorized_rollout")
    return result


def validate_template(template):
    require(isinstance(template, dict), "Ledger template must be an object")
    rows = template.get("cases")
    require(isinstance(rows, list) and len(rows) == 108, "Exactly 108 requirement records are required")
    wanted, observed = expected_cases(), {}
    for row in rows:
        require(isinstance(row, dict) and isinstance(row.get("id"), str), "Malformed requirement record")
        identity = row["id"]
        require(identity in wanted and identity not in observed, "Unknown or duplicate requirement: " + identity)
        require((row.get("suite"), row.get("level")) == wanted[identity], "Changed suite/level: " + identity)
        expected_status = "DEFERRED_BY_USER" if row["level"] == "authorized_rollout" else "PENDING_EVIDENCE"
        require(row.get("status") == expected_status, "Use the unpopulated template; unexpected status for " + identity)
        require(row.get("actual_result") is None and row.get("checked_sha") is None and row.get("evidence") == [],
                "Template already contains execution claims: " + identity)
        if row["level"] == "unit":
            methods = row.get("required_methods")
            require(isinstance(methods, list) and methods and all(isinstance(name, str) and name for name in methods)
                    and len(methods) == len(set(methods)), "Missing/duplicate required method: " + identity)
        observed[identity] = row
    require(set(observed) == set(wanted), "Missing requirement records")
    require(sum(row["level"] == "unit" for row in rows) == 87, "Exactly 87 unit requirements are required")
    return observed


def full_sha(value, label):
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value), "Missing/full SHA required: " + label)
    return value


def validate_context(context, *, head, base, synthetic, pr):
    require(isinstance(context, dict), "Missing actual CI context")
    full_sha(head, "H"); full_sha(base, "B"); full_sha(synthetic, "S")
    require(type(pr) is int and pr > 0, "Missing PR number")
    expected = {"repository": REPOSITORY, "accepted_release": ACCEPTED, "event": "pull_request",
                "pr_number": pr, "head_sha": head, "base_sha": base, "checked_sha": synthetic,
                "scope": "canonical_commit_objects"}
    for key, value in expected.items():
        require(context.get(key) == value and not (key == "pr_number" and type(context.get(key)) is not int),
                "Context mismatch: " + key)
    full_sha(context.get("checked_tree"), "tested synthetic tree")
    require(isinstance(context.get("event_sha256"), str) and re.fullmatch(r"[0-9a-f]{64}", context["event_sha256"]),
            "Missing captured event digest")
    for name in ("run_id", "run_attempt"):
        require(type(context.get(name)) is int and context[name] > 0, "Missing genuine run identity: " + name)
    return {name: context[name] for name in CONTEXT_FIELDS}


def validate_report(report, suite, context, cases):
    require(isinstance(report, dict) and report.get("format") == "Permansson.Hardening.Tests.v1"
            and type(report.get("schema_version")) is int and report["schema_version"] == 1, "Wrong test report format")
    require(report.get("suite") == suite and report.get("status") == "PASS" and report.get("error_code") is None,
            "Suite did not pass: " + suite)
    require(report.get("execution_tracked_clean") is True, "Suite did not execute clean tracked sources: " + suite)
    actual_context = report.get("context", {})
    validate_context(actual_context, head=context["head_sha"], base=context["base_sha"],
                     synthetic=context["checked_sha"], pr=context["pr_number"])
    require(all(actual_context.get(key) == value for key, value in context.items()), "Report/context mismatch: " + suite)
    runtime = report.get("runtime", {})
    require(isinstance(runtime.get("python"), str) and re.fullmatch(r"3\.13\.[0-9]+", runtime["python"])
            and isinstance(runtime.get("git"), str) and runtime["git"], "Unsupported or absent CI runtime: " + suite)
    for name in ("failures", "errors", "skips"):
        require(type(report.get(name)) is int and report[name] == 0, "Suite failed or skipped: " + suite)
    unit_cases = {identity: row for identity, row in cases.items() if row["level"] == "unit" and row["suite"] == suite}
    covered = report.get("covered_requirements")
    require(isinstance(covered, list) and all(isinstance(identity, str) for identity in covered)
            and len(covered) == len(set(covered)) and set(covered) == set(unit_cases), "Missing/extra covered cases: " + suite)
    mapping = defaultdict(list)
    for identity, row in unit_cases.items():
        for method in row["required_methods"]:
            mapping[method].append(identity)
    records = report.get("results")
    require(isinstance(records, list) and records, "Empty suite execution: " + suite)
    methods, subtests = {}, defaultdict(list)
    for row in records:
        require(isinstance(row, dict) and isinstance(row.get("method"), str) and row["method"], "Malformed executed method")
        method = row["method"]
        require(row.get("status") == "PASS", "A method or subtest did not pass: " + method)
        requirements = row.get("requirements")
        require(isinstance(requirements, list) and sorted(requirements) == sorted(mapping.get(method, [])),
                "Result requirement mapping differs: " + method)
        if "subtest" in row:
            require(isinstance(row["subtest"], str) and row["subtest"], "Malformed executed subtest")
            subtests[method].append(row)
        else:
            require(method not in methods, "Duplicate completed method: " + method)
            methods[method] = row
    require(set(mapping) <= set(methods) and set(subtests) <= set(methods), "Mapped method did not complete: " + suite)
    require(type(report.get("methods_run")) is int and report["methods_run"] == len(methods) and methods,
            "Method count mismatch: " + suite)
    require(type(report.get("subtests_run")) is int and report["subtests_run"] == sum(map(len, subtests.values())),
            "Subtest count mismatch: " + suite)
    return {"cases": sorted(unit_cases), "methods": methods, "subtests": subtests,
            "methods_run": len(methods), "subtests_run": sum(map(len, subtests.values())), "runtime": runtime}


def assemble(template, context_document, reports, *, head, base, synthetic, pr, context_identity=None):
    require(context_document.get("format") == "Permansson.Hardening.CIContext.v1", "Wrong source-context document")
    require(context_document.get("status", "PASS") == "PASS", "Source-context capture did not pass")
    context = validate_context(context_document, head=head, base=base, synthetic=synthetic, pr=pr)
    ledger = deepcopy(template)
    cases = validate_template(ledger)
    require(set(reports) == set(SUITES), "All six suites are required exactly once")
    reserved = {identity: deepcopy(row) for identity, row in cases.items() if row["level"] != "unit"}
    inventory = {}
    for suite in SUITES:
        report, identity = reports[suite]
        verified = validate_report(report, suite, context, cases)
        inventory[suite] = {**identity, "run_id": context["run_id"], "run_attempt": context["run_attempt"],
                            "methods_run": verified["methods_run"], "subtests_run": verified["subtests_run"],
                            "runtime": verified["runtime"], "covered_requirements": verified["cases"]}
        for case_id in verified["cases"]:
            row = cases[case_id]
            row.update(status="PASS", checked_sha=synthetic,
                       actual_result={"unit_requirement_verified": True, "expected_validator_outcome": row["expected_result"],
                                      "suite": suite, "methods": row["required_methods"]},
                       evidence=[{"suite": suite, "report_sha256": identity["sha256"],
                                  "methods": row["required_methods"], "run_id": context["run_id"],
                                  "run_attempt": context["run_attempt"],
                                  "passed_subtests": sum(len(verified["subtests"].get(name, [])) for name in row["required_methods"])}])
    require(all(cases[identity] == row for identity, row in reserved.items()), "Nonunit case was modified")
    require(Counter(row["status"] for row in cases.values()) == {"PASS": 87, "PENDING_EVIDENCE": 9, "DEFERRED_BY_USER": 12},
            "Final case-state conjunction is invalid")
    ledger["template_only"] = False
    ledger["maintenance_context"].update(repository=REPOSITORY, pr_number=pr, head_H=head, base_B=base,
                                           synthetic_S=synthetic, synthetic_tree=context["checked_tree"], main_merge_M=None,
                                           main_tree=None, workflow_runs=[{"run_id": context["run_id"], "run_attempt": context["run_attempt"]}])
    ledger["completion_policy"].update(all108_complete=False, overall_F3_closed=False)
    ledger["receipt_assembly"] = {"format": "Permansson.Hardening.UnitReceiptAssembly.v1",
                                   "assembled_at_utc": datetime.now(timezone.utc).isoformat(),
                                   "scope": "87_unit_requirements_only", "source_context": context,
                                   "context_evidence": context_identity, "reports": inventory,
                                   "remaining_technical_cases": sorted(identity for identity, row in cases.items()
                                                                       if row["status"] == "PENDING_EVIDENCE"),
                                   "publisher_authentication": "must_be_established_from_separate_API_artifact_and_job_records",
                                   "merge_acceptance": "NOT_ESTABLISHED", "operational_completion": "DEFERRED_BY_USER"}
    return ledger


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--template", required=True)
    parser.add_argument("--context", required=True, help="Current downloaded context.json, or artifact.zip!context.json")
    parser.add_argument("--head", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--synthetic", required=True)
    parser.add_argument("--pr", type=int, required=True)
    parser.add_argument("--report", action="append", required=True, help="SUITE=report.json or SUITE=artifact.zip!member.json")
    parser.add_argument("--output", required=True, help="New path under this script's external artifacts directory")
    args = parser.parse_args(argv)
    try:
        template, template_identity = read_source(args.template)
        context, context_identity = read_source(args.context)
        reports = {}
        for value in args.report:
            suite, separator, source = value.partition("=")
            require(separator and suite in SUITES and suite not in reports, "Unknown or duplicate report suite")
            reports[suite] = read_source(source)
        result = assemble(template, context, reports, head=args.head, base=args.base, synthetic=args.synthetic,
                          pr=args.pr, context_identity=context_identity)
        result["receipt_assembly"]["template_evidence"] = template_identity
        output = Path(args.output).absolute()
        require(not output.is_symlink() and not any(parent.is_symlink() for parent in output.parents), "Output traverses a symlink")
        output = output.resolve()
        artifacts = Path(__file__).resolve().parent
        require(artifacts in output.parents, "Output must remain under the external artifacts directory")
        output.parent.mkdir(parents=True, exist_ok=True)
        encoded = (json.dumps(result, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False) + "\n").encode()
        with output.open("xb") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        print("87 unit requirements populated; 9 technical cases pending; 12 OPS deferred")
        print("OUTPUT_SHA256=" + sha256(encoded))
        return 0
    except (ReceiptError, OSError, ValueError, TypeError, KeyError) as exc:
        print("Receipt assembly failed: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
