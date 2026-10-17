"""Assemble an explicitly curated external PR77 receipt; never mutate a repository.

No network calls, Git writes, glob of artifacts/, source refresh, or publication.
Historical inputs are selected by reviewed inventory hashes. Final inputs must
come from the separately captured repaired head, never the rejected abccf head.
This helper checks joins and file identity; it does not authenticate copied API
JSON or turn source/code review into GitHub APPROVED review or OPS completion.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import urllib.parse
import zipfile

REPOSITORY = "HMarcusWH/PermanssonLean"
ACCEPTED = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
REJECTED_HEAD = "abccf9d7ce389fffe5637ea0ff0acd5718d9058f"
FINAL_DIRECTORY = "hardening-pr77-finalized-acceptance"
MAX_FILE = 128 * 1024 * 1024
MAX_TOTAL = 384 * 1024 * 1024
HISTORICAL_INDICES = {
    "hardening-pr77-prebase-acceptance/capture-inventory.json":
        (57, "3282a82c9b39eb3cda61412962b2f4266c13b82fa9b897d20a0773dc90608b4e"),
    "hardening-pr78-final-acceptance/capture-files.json":
        (25, "4be63916d70efa1452981ba98aac1ae91ab2bad5e8b8d53dd23327d837adac5c"),
    "hardening-pr78-final-acceptance/postmerge-addendum-files.json":
        (10, "f4949d2158fd3db318b050d01432bc96353151a64cf8fa0e230564ae8274445a"),
}
# Individually reviewed files only. Existence never authorizes a sibling file.
REQUIRED_FILES = (
    "hardening-pr77/12110875886.zip",
    "hardening-pr77/check-runs-h2-final.json",
    "maintenance-final-evidence-checklist.md",
    "maintenance-acceptance-ledger-template.json",
    "populate_maintenance_unit_ledger.py",
    "check_live_context_transition.py",
    "hardening-source-evidence-refs.json",
    "hardening-source-evidence-refs-repaired.json",
    "live-context-transition-independent-review.md",
    "hardening-codex-review-resolutions.md",
    "hardening-review-record.md",
    "hardening-pr77-final-acceptance/local-head-independent-review.json",
    "hardening-pr76-comment-authority-20261017/comment-6235925253.json",
    "hardening-pr76-comment-authority-20261017/comment-6236142249.json",
    "hardening-pr76-comment-authority-20261017/comment-pins.json",
    "hardening-pr76-comment-authority-20261017/p1-independent-review.json",
)
OPTIONAL_REVIEW_FILES = (
    "capture_public_evidence.py", "check_reviewed_source_restore.py",
    "hardening-context-reviewed.json", "hardening-workflow-reviewed.json",
    "hardening-preservation-reviewed-package.json", "hardening-preservation-scope-cli.json",
    "hardening-reviewed-source-restore.json", "hardening-tex-reviewed-package.json",
    "unit-ledger-assembler-diagnostics.json",
    "maintenance-acceptance-ledger-template-repaired.json",
    "maintenance-acceptance-ledger-template-repaired-validated.json",
    "maintenance-acceptance-ledger-template-finalized.json",
    "maintenance-acceptance-ledger-finalized-premerge-verified.json",
    "hardening-source-evidence-refs-finalized.json",
    "refresh_maintenance_ledger_template.py", "ledger-template-refresh-independent-review.json",
    "complete_maintenance_technical_ledger.py",
    "add_main_acceptance.py", "add-main-acceptance-author-controls.json",
    "add-main-acceptance-independent-review.json",
    "maintenance-technical-ledger-helper-review.json",
    "maintenance-technical-ledger-helper-selfcheck.json",
    "ledger-template-finalized-independent-review.json",
    "maintenance-receipt-builder-selfcheck.json",
    "maintenance-receipt-builder-selfcheck-reviewed.json", "maintenance-receipt-builder-selfcheck-ready.json",
    "maintenance-receipt-builder-selfcheck-root-171.json", "maintenance-receipt-builder-selfcheck-frozen.json",
    "maintenance-receipt-builder-selfcheck-finalized.json",
    "maintenance-receipt-builder-selfcheck-postmerge.json",
    "maintenance-receipt-builder-selfcheck-postmerge-reviewed.json",
    "maintenance-receipt-builder-selfcheck-capture-whitelist.json",
    "review_receipt_packet_builder.py",
    "hardening-pr77/archive-capture-regressions-final.json",
    "hardening-pr77/p1-fixed-comment-regressions.json",
    "hardening-pr77/delivered-inventory-limits-regressions.json",
    "hardening-pr77/delivered-inventory-limits-independent-review.json",
    "hardening-pr77/publication-integrity-independent-review.json",
    "hardening-pr77/publication-existing-candidate-independent.json",
    "hardening-pr77/publication-gate-real-H171c-positive.json",
    "hardening-pr77/legacy-context-binding-regressions.json",
    "hardening-pr77/legacy-source-binding-independent-review.json",
    "hardening-pr77/independent-final-source-review.json",
    "hardening-workflow-finalized-tooling.json",
    "hardening-pr77/local-restore-92e451.json",
    "hardening-pr77/review-92e451.json", "hardening-pr77/review-92e451-sources.json",
    "hardening-pr77/restore_repacked_bundle.py", "hardening-pr77/review_publication_packaging.py",
    "hardening-pr77-repaired-acceptance/final-checks-h171-historical.json",
    "hardening-pr77-repaired-acceptance/hardening-preservation-reports.zip",
    "hardening-pr77-repaired-acceptance/final-integrity-artifacts.json",
    "hardening-pr77-repaired-acceptance/initial-pr77.json",
    "hardening-pr77-repaired-acceptance/synthetic-commit.json",
    "hardening-pr77/review-049-packaging.json", "hardening-pr77/review_049_packaging.py",
    "hardening-pr77/review-cc114.json", "hardening-pr77/review_cc114_packaging.py",
    "hardening-pr77/review-3f279.json", "hardening-pr77/review_next_packaging.py",
    "hardening-pr77/review-abccf-delta.json", "hardening-pr77/review_abccf_delta.py",
    "hardening-pr77/review-repaired-packaging.json",
    "hardening-pr77/guide-independent-review.json",
    "hardening-pr77/guide-closure-independent-review.json", "hardening-pr77/review_guide_packaging.py",
    "hardening-pr77/review-171c954.json", "hardening-pr77/review-171c954-sources.json",
)
FINAL_NAMES = {
    "README.md", "capture-inventory.json", "capture-files.json", "verification-summary.json",
    "initial-pr77.json", "initial-checks.json", "initial-runs.json", "initial-reviews.json",
    "initial-comments.json", "initial-merge-checks.json", "synthetic-commit.json",
    "initial-application-artifacts.json", "initial-integrity-artifacts.json", "initial-lean-artifacts.json",
    "initial-portability-artifacts.json", "initial-research-artifacts.json", "initial-verification-artifacts.json",
    "final-pr77.json", "final-checks.json", "final-runs.json", "final-reviews.json",
    "final-comments.json", "final-research-run.json", "final-research-jobs.json",
    "final-research-artifacts.json", "research-jobs.json", "research-artifacts-initial.json",
    "final-lean-artifacts.json", "final-verification-artifacts.json", "final-application-artifacts.json",
    "integrity-artifacts.json", "final-integrity-artifacts.json", "integrity-jobs.json",
    "portability-artifacts.json", "portability-artifacts-initial.json", "portability-jobs.json",
    "portability-run.json", "review-threads-initial.json", "review-threads-final.json",
    "maintenance-scope.json", "actual-maintenance-acceptance.json", "acceptance-environment.json",
    "actual-scope-independent-review.json", "ci10-credential-review.json", "live-base-transition.json",
    "live-head-transition.json", "c10-release-evidence.zip", "c10-content-verification.json",
    "d0-finite-calculation-evidence.zip", "hardening-preservation-reports.zip",
    "hardening-export-reports.zip", "hardening-archive-reports.zip",
    "hardening-windows-portability-reports.zip", "verify_capture.py", "prepare_final_verifier.py",
    "recheck_c10.py", "source-binding.json", "merge-verification.json", "merge-observation.json",
    "R-c10-artifact-metadata.json", "R-c10.zip", "R-copy-provenance.json",
    "legacy-build-source-context.zip", "legacy-research-source-context.zip",
    "legacy-executable-source-context.zip", "legacy-application-source-context-ubuntu-latest.zip",
    "legacy-application-source-context-windows-latest.zip", "legacy-context-artifacts.json",
    "legacy-context-verification.json",
}
LEGACY_CONTEXT_ARTIFACTS = {
    "legacy-build-source-context": "build",
    "legacy-research-source-context": "research",
    "legacy-executable-source-context": "executable-verification",
    "legacy-application-source-context-ubuntu-latest": "Application contract (ubuntu-latest)",
    "legacy-application-source-context-windows-latest": "Application contract (windows-latest)",
}
FINAL_PATTERN = re.compile(
    r"(?:final-jobs-[0-9]+|poll[0-9]+-(?:pr77|checks|comments|research-artifacts|windows-artifacts|"
    r"portability-artifacts|integrity-artifacts|lean-artifacts|application-artifacts|verification-artifacts|"
    r"integrity-run|integrity-jobs|runs)|run-[0-9]+|jobs-[0-9]+)\.json")
POSTMERGE_NAMES = FINAL_NAMES | {"main-checks.json", "main-runs.json", "main-commit.json",
                                 "main-artifacts.json", "merge-verification.json"}
SIGNED_KEYS = {"sig", "signature", "token", "access_token", "credential", "credentials",
               "x-amz-signature", "x-amz-credential", "x-goog-signature", "se", "sp", "sv", "sr"}


def reject(message):
    raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def full_sha(value):
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{40}", value) is None:
        reject("Expected a complete lower-case Git SHA")
    return value


def relative(value):
    if (not isinstance(value, str) or not value or "\\" in value or "\0" in value
            or ":" in value or value.startswith("/") or any(c in value for c in "\r\n")):
        reject("Unsafe relative path: " + repr(value))
    p = PurePosixPath(value)
    if any(part in {"", ".", ".."} for part in value.split("/")) or p.is_absolute():
        reject("Noncanonical relative path: " + value)
    return value


def ordinary_file(root, rel):
    path = root / relative(rel)
    for item in [path, *path.parents]:
        if item.is_symlink() or (hasattr(item, "is_junction") and item.is_junction()):
            reject("Symlink/junction source is forbidden: " + str(path))
        if item == root:
            break
    if not path.is_file() or path.stat().st_size > MAX_FILE:
        reject("Missing, nonregular or oversized approved source: " + rel)
    return path


def read(root, rel):
    return ordinary_file(root, rel).read_bytes()


def load(data):
    def unique(rows):
        result = {}
        for key, value in rows:
            if key in result:
                reject("Duplicate JSON key")
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=unique)


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def screen_text(text, label):
    if re.search(r"(?:github_pat_|gh[pousr]_)[A-Za-z0-9_]{20,}|Bearer\s+[A-Za-z0-9._-]{25,}", text):
        reject("Credential-shaped content in approved source: " + label)
    for url in re.findall(r"https?://[^\s<>\"']+", text):
        keys = {key.lower() for key, _ in urllib.parse.parse_qsl(urllib.parse.urlsplit(url).query)}
        if keys & SIGNED_KEYS:
            reject("Temporary signed/credential URL in approved source: " + label)


def screen_payload(data, label, depth=0):
    if depth > 4:
        reject("Excessively nested publisher ZIP: " + label)
    if data.startswith(b"PK\x03\x04"):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            seen, size = set(), 0
            if len(archive.infolist()) > 2000:
                reject("Too many ZIP members: " + label)
            for member in archive.infolist():
                name = member.filename.rstrip("/")
                relative(name)
                if name in seen or member.flag_bits & 1 or stat.S_IFMT(member.external_attr >> 16) == stat.S_IFLNK:
                    reject("Unsafe or duplicate ZIP member: " + label)
                seen.add(name)
                size += member.file_size
                if member.file_size > MAX_FILE or size > MAX_TOTAL:
                    reject("Oversized ZIP content: " + label)
                if not member.is_dir():
                    screen_payload(archive.read(member), label + "!" + member.filename, depth + 1)
        return
    try:
        text = data.decode("utf-8")
    except UnicodeError:
        reject("Unexpected binary input outside a whitelisted publisher ZIP: " + label)
    screen_text(text, label)
    if label.endswith(".json"):
        def walk(value):
            if isinstance(value, str):
                screen_text(value, label)
            elif isinstance(value, dict):
                for item in value.values():
                    walk(item)
            elif isinstance(value, list):
                for item in value:
                    walk(item)
        walk(load(data))


def indexed_inputs(artifacts, index, expected_count=None, expected_digest=None, final=False, postmerge=False):
    data = read(artifacts, index)
    if expected_digest is not None and sha(data) != expected_digest:
        reject("Reviewed historical inventory changed: " + index)
    value = load(data)
    rows = value.get("files", value.get("entries"))
    if not isinstance(rows, list) or not rows or (expected_count is not None and len(rows) != expected_count):
        reject("Unexpected indexed file count: " + index)
    result = {index: data}
    base = PurePosixPath(index).parent
    for row in rows:
        name = relative(row["path"])
        allowed = POSTMERGE_NAMES if postmerge else FINAL_NAMES
        if (final or postmerge) and ("/" in name or not (name in allowed or FINAL_PATTERN.fullmatch(name))):
            reject("Final capture member needs explicit whitelist review: " + name)
        rel = (base / name).as_posix()
        if rel in result:
            reject("Duplicate/self-including source inventory: " + rel)
        payload = read(artifacts, rel)
        if type(row.get("size")) is not int or len(payload) != row["size"] or sha(payload) != row.get("sha256"):
            reject("Indexed source bytes differ: " + rel)
        result[rel] = payload
    return result


def git_object(repo, oid, kind="commit"):
    full_sha(oid)
    environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    environment.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
                       GIT_OPTIONAL_LOCKS="0", GIT_TERMINAL_PROMPT="0")
    process = subprocess.run(["git", "-C", str(repo), "cat-file", kind, oid], check=False,
                             capture_output=True, timeout=60, env=environment)
    if process.returncode:
        reject("Required local canonical Git object unavailable: " + oid)
    data = process.stdout
    if hashlib.sha1(kind.encode() + b" " + str(len(data)).encode() + b"\0" + data).hexdigest() != oid:
        reject("Git object hash mismatch: " + oid)
    return data


def commit_identity(repo, oid):
    raw = git_object(repo, oid).split(b"\n\n", 1)[0].splitlines()
    return {"sha": oid, "tree": next(line[5:].decode() for line in raw if line.startswith(b"tree ")),
            "parents": [line[7:].decode() for line in raw if line.startswith(b"parent ")]}


def verify_ledger(value, head, base, synthetic, tooling, require_all):
    ctx = value.get("maintenance_context", {})
    if (ctx.get("repository") != REPOSITORY or ctx.get("pr_number") != 77
            or (ctx.get("head_H"), ctx.get("base_B"), ctx.get("synthetic_S")) != (head, base, synthetic)
            or value.get("registry_source", {}).get("commit") != tooling):
        reject("Ledger source H/B/S/T differs from explicit final inputs")
    cases = value.get("cases", [])
    expected_ids = {f"{name}-{number:02}" for name, count in {"REF": 15, "PRES": 23, "TEX": 20, "ARCH": 27, "CI": 11, "OPS": 12}.items() for number in range(1, count + 1)}
    if len(cases) != 108 or {row.get("id") for row in cases} != expected_ids:
        reject("Ledger does not contain 108 distinct cases")
    counts = Counter(row.get("level") for row in cases)
    if counts != {"unit": 87, "integration": 2, "live_pr": 6, "review": 1, "authorized_rollout": 12}:
        reject("Ledger requirement levels changed")
    for row in cases:
        expected = "DEFERRED_BY_USER" if row["level"] == "authorized_rollout" else "PASS"
        if row["level"] == "unit" or row["level"] == "authorized_rollout" or require_all:
            if row.get("status") != expected:
                reject("Unfinished or promoted case in final ledger: " + row["id"])
        if row["level"] == "unit" and row.get("checked_sha") != synthetic:
            reject("Unit case is not bound to current S: " + row["id"])
    source = value.get("receipt_assembly", {}).get("source_context", {})
    if (source.get("head_sha"), source.get("base_sha"), source.get("checked_sha")) != (head, base, synthetic):
        reject("Unit receipt assembly source is stale")
    policy = value.get("completion_policy", {})
    if policy.get("all108_complete") is not False or policy.get("overall_F3_closed") is not False:
        reject("Final packet must retain deferred operational/F3 boundaries")
    science = value.get("scientific_exclusions", {})
    if (science.get("new_or_changed_theorem_declarations") != 0
            or science.get("new_mathematical_assumptions") != 0 or science.get("scientific_promotion") is not False):
        reject("Maintenance scientific exclusions were changed or omitted")
    if require_all:
        premerge = value.get("premerge_acceptance", {})
        if ("HOLD" in premerge.get("status", "")
                or premerge.get("acceptance_hold", {}).get("status", "").startswith("OPEN")):
            reject("Current review/acceptance hold is still open")
        conditions = value.get("additional_acceptance_conditions", [])
        if (len(conditions) != 1 or conditions[0].get("status") != "PASS"
                or conditions[0].get("checked_sha") != synthetic
                or conditions[0].get("production_tooling_source", {}).get("commit") != tooling):
            reject("Final actual-S K4 scope evidence is missing/stale")
    return ctx


def artifact_source(value, artifacts):
    """Resolve only an explicit original artifacts path, never a basename guess."""
    if not isinstance(value, str):
        reject("Malformed evidence path")
    normalized = value.replace("\\", "/")
    prefix = artifacts.as_posix().rstrip("/") + "/"
    if normalized.startswith(prefix):
        return relative(normalized[len(prefix):])
    if normalized.startswith("artifacts/"):
        return relative(normalized[10:])
    return relative(normalized)


def portable_ledger(value, mapping, artifacts, ledger_name):
    result = deepcopy(value)
    links = []
    def walk(node):
        if isinstance(node, list):
            for item in node:
                walk(item)
        elif isinstance(node, dict):
            original = node.get("original_artifact_path", node.get("original_artifact_source"))
            role = "path" if "original_artifact_path" in node else "source"
            if original is None and isinstance(node.get("source"), str):
                text = node["source"].replace("\\", "/")
                if text.startswith(artifacts.as_posix() + "/"):
                    original, role = node["source"], "source"
            if original is not None:
                source = artifact_source(original, artifacts)
                if source not in mapping:
                    reject("Ledger references an unselected artifact: " + source)
                destination = mapping[source]
                node.setdefault("raw_original_" + role, node.get(role))
                node["portable_path"] = destination
                node["portable_href"] = "../" + destination
                node[role] = "../" + destination
                node.setdefault("original_artifact_" + role, original)
                member = node.get("member")
                links.append({"ledger": ledger_name, "source_artifact": source,
                    "portable_path": destination, "member": member,
                    "expected_file_sha256": node.get("container_sha256", node.get("sha256")),
                    "expected_file_bytes": node.get("container_bytes", node.get("bytes")),
                    "expected_member_sha256": node.get("member_sha256", node.get("sha256") if "container_sha256" in node and member else None),
                    "expected_member_bytes": node.get("member_bytes", node.get("bytes") if "container_bytes" in node and member else None)})
            if isinstance(node.get("commit"), str) and re.fullmatch(r"[0-9a-f]{40}", node["commit"]) and isinstance(node.get("path"), str):
                path = relative(node["path"])
                node["immutable_source_url"] = "https://github.com/" + REPOSITORY + "/blob/" + node["commit"] + "/" + path
            for item in list(node.values()):
                walk(item)
    walk(result)
    if isinstance(result.get("premerge_acceptance"), dict):
        record = result["premerge_acceptance"]
        record["raw_original_portable_evidence_paths"] = record.get("portable_evidence_paths")
        record["portable_evidence_paths"] = "path/source and portable_href are relative from ledger/; portable_path is relative from the packet root. Raw original acquisition locations and source ledgers are retained unchanged under artifacts/."
    result["receipt_packet_portability"] = {"raw_ledger_retained": True, "rewritten_fields": "Evidence path/source/portable_href/portable_path only; source/code claims and case verdicts retained", "layout": "artifacts/<original acquisition-relative name>", "source_references_preserved": True}
    return result, links


def verify_links(links, files):
    for row in links:
        data = files[row["portable_path"]]
        if row["expected_file_sha256"] is not None and row["expected_file_sha256"] != sha(data):
            reject("Ledger reference digest differs: " + row["source_artifact"])
        if row["expected_file_bytes"] is not None and row["expected_file_bytes"] != len(data):
            reject("Ledger reference size differs: " + row["source_artifact"])
        member = row["member"]
        if member is not None:
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                matches = [entry for entry in archive.infolist() if entry.filename == member]
                if len(matches) != 1:
                    reject("Ledger ZIP member missing/duplicate: " + str(member))
                payload = archive.read(matches[0])
                if row["expected_member_sha256"] is not None and row["expected_member_sha256"] != sha(payload):
                    reject("Ledger ZIP member digest differs: " + str(member))
                if row["expected_member_bytes"] is not None and row["expected_member_bytes"] != len(payload):
                    reject("Ledger ZIP member size differs: " + str(member))


def verify_repository_references(repo, *ledgers):
    references = set()
    def walk(value):
        if isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, dict):
            if "immutable_source_url" in value:
                references.add(full_sha(value["commit"]) + ":" + relative(value["path"]))
            for item in value.values():
                walk(item)
    for ledger in ledgers:
        walk(ledger)
    if len(references) > 1000:
        reject("Too many canonical repository source references")
    environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    environment.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_CONFIG_NOSYSTEM="1",
                       GIT_CONFIG_GLOBAL=os.devnull, GIT_OPTIONAL_LOCKS="0", GIT_TERMINAL_PROMPT="0")
    items = sorted(references)
    if not items:
        return []
    process = subprocess.run(["git", "-C", str(repo), "cat-file", "--batch-check=%(objecttype)"],
        input=("\n".join(items) + "\n").encode(), capture_output=True, timeout=60, env=environment)
    if process.returncode or process.stdout.splitlines() != [b"blob"] * len(items):
        reject("A pinned canonical repository source path is missing or not a blob")
    return items


def api_payload(value):
    return value.get("response", value.get("payload", value))


def verify_legacy_contexts(selected, prefix, checks, summary, head, base, synthetic, tree, main=None):
    """Join five actual publisher ZIPs to their source tuple and check run.

    This validates retained evidence consistency. It does not independently
    authenticate copied publisher metadata or turn a fixture into real CI.
    """
    check_by_name = {row.get("name"): row for row in checks}
    for artifact, name in LEGACY_CONTEXT_ARTIFACTS.items():
        payload = selected.get(prefix + artifact + ".zip")
        publisher = [row for row in summary.get("artifacts", []) if row.get("name") == artifact]
        if (payload is None or len(publisher) != 1 or publisher[0].get("sha256") != sha(payload)
                or publisher[0].get("bytes") != len(payload)):
            reject("Legacy source-context publisher/ZIP identity differs: " + name)
        with zipfile.ZipFile(io.BytesIO(payload)) as archive:
            entries = archive.infolist()
            if len(entries) != 1 or entries[0].filename != "required-source.json" or entries[0].is_dir():
                reject("Legacy source-context ZIP must contain exactly required-source.json: " + name)
            if entries[0].file_size > 1024 * 1024:
                reject("Legacy source-context report exceeds its fixed budget: " + name)
            value = load(archive.read(entries[0]))
        check = check_by_name.get(name, {})
        run = re.fullmatch(r"https://github\.com/HMarcusWH/PermanssonLean/actions/runs/([0-9]+)/job/([0-9]+)",
                           check.get("details_url", ""))
        if (not isinstance(value, dict) or value.get("format") != "Permansson.Hardening.CIContext.v1"
                or value.get("repository") != REPOSITORY or value.get("accepted_release") != ACCEPTED
                or value.get("checked_sha") != (main or synthetic) or value.get("checked_tree") != tree
                or value.get("event") != ("push" if main else "pull_request")
                or value.get("pr_number") != (None if main else 77)
                or value.get("head_sha") != (None if main else head)
                or value.get("base_sha") != (None if main else base)
                or not {"pr_number", "head_sha", "base_sha"}.issubset(value)
                or value.get("scope") != "canonical_commit_objects"
                or type(value.get("run_id")) is not int or value["run_id"] <= 0
                or type(value.get("run_attempt")) is not int or value["run_attempt"] <= 0
                or re.fullmatch(r"[0-9a-f]{64}", value.get("event_sha256", "")) is None
                or run is None or value["run_id"] != int(run.group(1))
                or check.get("id") != int(run.group(2))):
            reject("Legacy source-context report is not for the actual current "
                   + ("main-push/check run: " if main else "PR/check run: ") + name)


def verify_final_capture(selected, head, base, synthetic, tree, main=None, directory=FINAL_DIRECTORY):
    prefix = directory + "/"
    required = ("final-pr77.json", "final-checks.json", "verification-summary.json",
                "maintenance-scope.json", "actual-maintenance-acceptance.json", "c10-content-verification.json")
    if any(prefix + name not in selected for name in required):
        reject("Final repaired capture lacks required source/check/scope/C10 verification files")
    pr = api_payload(load(selected[prefix + "final-pr77.json"]))
    allowed_merges = {synthetic} | ({main} if main else set())
    if (pr.get("number") != 77 or pr.get("head", {}).get("sha") != head
            or pr.get("base", {}).get("sha") != base or pr.get("merge_commit_sha") not in allowed_merges
            or pr.get("base", {}).get("repo", {}).get("full_name") != REPOSITORY):
        reject("Final captured PR H/B/S differs from explicit inputs")
    checks = api_payload(load(selected[prefix + "final-checks.json"])).get("check_runs", [])
    expected = {"build", "research", "executable-verification", "Application contract (ubuntu-latest)",
                "Application contract (windows-latest)", "frozen-source-preservation", "release-export-integrity",
                "archive-reproducibility", "integrity-portability-windows"}
    if (len(checks) != 9 or {row.get("name") for row in checks} != expected
            or any(row.get("head_sha") != head or row.get("status") != "completed"
                   or row.get("conclusion") != "success" or row.get("app", {}).get("id") != 15368 for row in checks)):
        reject("Final capture does not contain nine actual successful current-head Actions checks")
    scope = load(selected[prefix + "maintenance-scope.json"])
    if (scope.get("status") != "PASS" or scope.get("context", {}).get("checked_sha") != synthetic
            or scope.get("context", {}).get("checked_tree") != tree
            or scope.get("details", {}).get("acceptance_only") is not True):
        reject("Final actual-S maintenance scope report is missing/stale")
    summary = load(selected[prefix + "verification-summary.json"])
    if (summary.get("status") != "PASS" or summary.get("source", {}).get("head") != head
            or summary.get("source", {}).get("base") != base or summary.get("source", {}).get("synthetic") != synthetic
            or summary.get("source", {}).get("tree") != tree):
        reject("Final capture verifier did not PASS")
    verify_legacy_contexts(selected, prefix, checks, summary, head, base, synthetic, tree)
    c10 = load(selected[prefix + "c10-content-verification.json"])
    if (c10.get("status") != "PASS" or c10.get("source", {}).get("head_sha") != head
            or c10.get("source", {}).get("base_sha") != base or c10.get("source", {}).get("synthetic_merge_sha") != synthetic):
        reject("Current C10 consistency source differs")
    publisher = [row for row in summary.get("artifacts", []) if row.get("name") == "c10-release-evidence"]
    c10_bytes = selected.get(prefix + "c10-release-evidence.zip")
    if (len(publisher) != 1 or c10_bytes is None or publisher[0].get("sha256") != sha(c10_bytes)
            or publisher[0].get("bytes") != len(c10_bytes) or c10.get("zip_sha256") != sha(c10_bytes)):
        reject("Current C10 publisher/ZIP byte identity differs")
    actual = load(selected[prefix + "actual-maintenance-acceptance.json"])
    if (actual.get("process_exit") != 0 or actual.get("checkout_HEAD") != synthetic
            or actual.get("checkout_clean_before_and_after") is not True
            or actual.get("ordered_parents") != [base, head] or actual.get("tree") != tree
            or actual.get("source", {}).get("head_sha") != head or actual.get("source", {}).get("base_sha") != base):
        reject("Actual clean-S scope receipt does not match final H/B/S")


def verify_postmerge_capture(selected, directory, head, base, synthetic, tree, main):
    """Check a separately acquired main-push addendum, preserving premerge data."""
    full_sha(main)
    prefix = directory + "/"
    required = ("main-checks.json", "main-runs.json", "main-commit.json",
                "research-jobs.json", "verification-summary.json")
    if any(prefix + name not in selected for name in required):
        reject("Postmerge addendum lacks actual main checks/runs/commit/research/summary")
    checks = api_payload(load(selected[prefix + "main-checks.json"])).get("check_runs", [])
    expected = {"build", "research", "executable-verification", "Application contract (ubuntu-latest)",
                "Application contract (windows-latest)", "frozen-source-preservation", "release-export-integrity",
                "archive-reproducibility", "integrity-portability-windows"}
    if (len(checks) != 9 or {row.get("name") for row in checks} != expected
            or any(row.get("head_sha") != main or row.get("status") != "completed"
                   or row.get("conclusion") != "success" or row.get("app", {}).get("id") != 15368 for row in checks)):
        reject("Postmerge checks are not nine actual successful current-main Actions checks")
    run_ids = set()
    for check in checks:
        match = re.fullmatch(r"https://github\.com/HMarcusWH/PermanssonLean/actions/runs/([0-9]+)/job/([0-9]+)",
                             check.get("details_url", ""))
        if match is None or check.get("id") != int(match.group(2)):
            reject("Postmerge check run/job resource identity differs")
        run_ids.add(int(match.group(1)))
    runs = api_payload(load(selected[prefix + "main-runs.json"])).get("workflow_runs", [])
    if (len(run_ids) != 6 or len(runs) != 6 or {row.get("id") for row in runs} != run_ids
            or any(row.get("head_sha") != main or row.get("event") != "push"
                   or row.get("head_branch") != "main" or row.get("status") != "completed"
                   or row.get("conclusion") != "success"
                   or row.get("repository", {}).get("full_name") != REPOSITORY for row in runs)):
        reject("Postmerge run records are not the six actual main-push workflows")
    commit = api_payload(load(selected[prefix + "main-commit.json"]))
    if (commit.get("sha") != main or [row.get("sha") for row in commit.get("parents", [])] != [base, head]
            or commit.get("commit", commit).get("tree", {}).get("sha") != tree):
        reject("Postmerge API commit parent/tree identity differs")
    summary = load(selected[prefix + "verification-summary.json"])
    if (summary.get("status") != "PASS" or summary.get("source") != {
            "main": main, "tree": tree, "head": head, "base": base, "synthetic": synthetic}):
        reject("Postmerge summary does not bind the accepted H/B/S/tree and actual M")
    integrity = {"hardening-preservation-reports": "frozen-source-preservation",
                 "hardening-export-reports": "release-export-integrity",
                 "hardening-archive-reports": "archive-reproducibility",
                 "hardening-windows-portability-reports": "integrity-portability-windows"}
    names = set(LEGACY_CONTEXT_ARTIFACTS) | set(integrity) | {"d0-finite-calculation-evidence"}
    records = summary.get("artifacts", [])
    if len(records) != 10 or {row.get("name") for row in records} != names:
        reject("Postmerge requires ten publisher ZIPs and no PR-only C10 artifact")
    for record in records:
        payload = selected.get(prefix + record["name"] + ".zip")
        if payload is None or record.get("sha256") != sha(payload) or record.get("bytes") != len(payload):
            reject("Postmerge publisher/ZIP bytes differ: " + record["name"])
    verify_legacy_contexts(selected, prefix, checks, summary, head, base, synthetic, tree, main=main)
    check_by_name = {row["name"]: row for row in checks}
    for artifact, name in integrity.items():
        with zipfile.ZipFile(io.BytesIO(selected[prefix + artifact + ".zip"])) as archive:
            entries = archive.infolist()
            if (len({entry.filename for entry in entries}) != len(entries)
                    or sum(entry.filename == "context.json" for entry in entries) != 1
                    or archive.getinfo("context.json").file_size > 1024 * 1024):
                reject("Postmerge integrity ZIP has an absent/ambiguous/oversized context")
            value = load(archive.read("context.json"))
        check = check_by_name[name]
        run_id = int(re.search(r"/runs/([0-9]+)/", check["details_url"]).group(1))
        if (not isinstance(value, dict) or value.get("format") != "Permansson.Hardening.CIContext.v1"
                or value.get("repository") != REPOSITORY or value.get("accepted_release") != ACCEPTED
                or value.get("checked_sha") != main or value.get("checked_tree") != tree
                or value.get("event") != "push" or value.get("scope") != "canonical_commit_objects"
                or not {"pr_number", "head_sha", "base_sha"}.issubset(value)
                or any(value[key] is not None for key in ("pr_number", "head_sha", "base_sha"))
                or type(value.get("run_id")) is not int or value["run_id"] != run_id
                or type(value.get("run_attempt")) is not int or value["run_attempt"] <= 0):
            reject("Postmerge integrity context is not for the actual main-push check")
    research = check_by_name["research"]
    jobs = api_payload(load(selected[prefix + "research-jobs.json"])).get("jobs", [])
    job = next((row for row in jobs if row.get("id") == research["id"]), None)
    if job is None or job.get("conclusion") != "success":
        reject("Postmerge actual Research job record is absent/failed")
    for name in ("Generate and independently verify C10 release proof evidence", "Upload source-bound C10 proof evidence"):
        steps = [row for row in job.get("steps", []) if row.get("name") == name]
        if len(steps) != 1 or steps[0].get("conclusion") != "skipped":
            reject("Postmerge PR-only C10 generation/upload was not reported skipped")


def assemble(args):
    workspace = Path(args.workspace).resolve()
    artifacts = workspace / "artifacts"
    head, base, synthetic, tooling = map(full_sha, (args.head, args.base, args.synthetic, args.tooling))
    if head == REJECTED_HEAD:
        reject("Habcc has open historical findings; it cannot be certified or assembled as the final head")
    index_path = PurePosixPath(relative(args.final_index))
    final_directory = index_path.parent.as_posix()
    if (re.fullmatch(r"hardening-pr77-[a-z0-9-]+-acceptance", final_directory) is None
            or index_path.name not in {"capture-inventory.json", "capture-files.json"}):
        reject("Final source requires an explicit bounded PR77 acceptance-folder index")
    postmerge_directory = None
    postmerge_index = getattr(args, "postmerge_index", None)
    if postmerge_index is not None:
        post = PurePosixPath(relative(postmerge_index))
        postmerge_directory = post.parent.as_posix()
        if (re.fullmatch(r"hardening-pr77-[a-z0-9-]+-main-push", postmerge_directory) is None
                or post.name not in {"capture-inventory.json", "capture-files.json"}):
            reject("Postmerge source requires an explicit bounded PR77 main-push-folder index")
    if (re.fullmatch(r"maintenance-acceptance-ledger-[A-Za-z0-9-]+\.json", args.ledger) is None
            or re.fullmatch(r"maintenance-unit-ledger-[A-Za-z0-9-]+\.json", args.unit_ledger) is None):
        reject("Ledger inputs must be explicit root-level maintenance acceptance/unit ledger JSON files")
    selected = {}
    def merge(rows):
        for rel, data in rows.items():
            if rel in selected and selected[rel] != data:
                reject("Different bytes at overlapping approved source: " + rel)
            selected[rel] = data
    for name, (count, pinned) in HISTORICAL_INDICES.items():
        merge(indexed_inputs(artifacts, name, count, pinned))
    merge(indexed_inputs(artifacts, args.final_index, final=True))
    if postmerge_index is not None:
        merge(indexed_inputs(artifacts, postmerge_index, postmerge=True))
    for rel in (*REQUIRED_FILES, args.ledger, args.unit_ledger):
        merge({rel: read(artifacts, rel)})
    for rel in OPTIONAL_REVIEW_FILES:
        if (artifacts / rel).exists():
            merge({rel: read(artifacts, rel)})
    # Preserve this reviewed assembler as a receipt tool, not an acceptance input.
    script = Path(__file__).resolve()
    if script.parent != artifacts:
        reject("Run the reviewed helper from the explicit external artifacts directory")
    merge({script.name: script.read_bytes()})
    if sum(map(len, selected.values())) > MAX_TOTAL:
        reject("Curated packet exceeds total budget")
    for rel, data in selected.items():
        screen_payload(data, rel)
    ledger, unit = load(selected[args.ledger]), load(selected[args.unit_ledger])
    ctx = verify_ledger(ledger, head, base, synthetic, tooling, True)
    verify_ledger(unit, head, base, synthetic, tooling, False)
    repo = Path(args.repo).resolve()
    identity = commit_identity(repo, synthetic)
    if identity["parents"] != [base, head] or identity["tree"] != ctx.get("synthetic_tree"):
        reject("Canonical S parents/tree differ from final ledger")
    for oid in (head, base, tooling):
        commit_identity(repo, oid)
    verify_final_capture(selected, head, base, synthetic, identity["tree"], ctx.get("main_merge_M"), final_directory)
    if bool(postmerge_index) != bool(ctx.get("main_merge_M")):
        reject("Premerge requires M=null; a postmerge ledger requires its separate main-push index")
    if postmerge_index is not None:
        verify_postmerge_capture(selected, postmerge_directory, head, base, synthetic,
                                 identity["tree"], ctx["main_merge_M"])
    mapping = {rel: "artifacts/" + rel for rel in selected}
    files = {mapping[rel]: data for rel, data in selected.items()}
    portable, links = portable_ledger(ledger, mapping, artifacts, "ledger/acceptance-ledger.json")
    portable_unit, unit_links = portable_ledger(unit, mapping, artifacts, "ledger/unit-ledger.json")
    verify_links(links + unit_links, files)
    repository_references = verify_repository_references(repo, portable, portable_unit)
    files["ledger/acceptance-ledger.json"] = json_bytes(portable)
    files["ledger/unit-ledger.json"] = json_bytes(portable_unit)
    source = {"repository": REPOSITORY, "pr_number": 77, "head_H": head, "base_B": base,
              "synthetic_S": synthetic, "tooling_T": tooling, "synthetic_tree": identity["tree"],
              "synthetic_ordered_parents": identity["parents"], "accepted_release": ACCEPTED,
              "main_merge_M": ctx.get("main_merge_M"), "main_tree": ctx.get("main_tree")}
    if source["main_merge_M"] is not None:
        main = commit_identity(repo, full_sha(source["main_merge_M"]))
        if main["parents"] != [base, head] or main["tree"] != identity["tree"] or source["main_tree"] != main["tree"]:
            reject("Eventual main merge does not match the accepted synthetic")
    files["source-binding.json"] = json_bytes({"format": "Permansson.CuratedReceiptSource.v1", "source": source,
        "postmerge_index": postmerge_index, "main_push_checks_joined": postmerge_index is not None,
        "status": "SOURCE_JOIN_CHECKED_PACKET_ASSEMBLED", "scope": "Curated external evidence; no new CI execution, publisher authentication, counted approval or operational rollout inferred."})
    files["source-reference-map.json"] = json_bytes({"format": "Permansson.CuratedReceiptReferences.v1", "source": source,
        "raw_source_artifacts": mapping, "portable_ledger_links": links + unit_links,
        "verified_canonical_repository_references": repository_references,
        "boundary": "Raw acquisition files and ledgers are byte-identical; only separate ledger views receive portable links. Historical paths and tuples remain historical."})
    files["README.md"] = ("# Permansson v0.2.0 maintenance evidence: H/T/S/M\n\n"
        "This packet records PR77 source H `" + head + "`, tooling T `" + tooling + "`, genuine synthetic S `" + synthetic + "`, main merge M `" + str(source["main_merge_M"] or "PENDING") + "`, and base B `" + base + "`.\n\n"
        "Read [source binding](source-binding.json), the [portable ledger](ledger/acceptance-ledger.json), its [unit ledger](ledger/unit-ledger.json), and the [reference map](source-reference-map.json). Original captures and source ledgers retain their exact bytes under `artifacts/`; historical H2, prebase and PR78 records are not relabeled as final PR77 evidence.\n\n"
        + ("The separate main-push addendum binds nine actual successful checks from six workflows and ten publisher ZIPs to M and the accepted synthetic tree. Its five legacy and four integrity source-context reports carry push/M with null PR/head/base fields; the Research C10 generation/upload steps are recorded skipped as designed. The original PR-only C10 evidence remains in the unchanged premerge capture.\n\n" if postmerge_index else "This premerge receipt has M=null and contains no postmerge acceptance claim. A later main-push receipt must be assembled in a new staging directory and preserve this packet and its source captures.\n\n")
        +
        "The 96 technical cases and 12 deferred OPS cases retain their recorded scope. Repository enforcement, remote archival tags, eligible human approval and external publication remain separate. Source restoration, artifact replay, actual CI compiler execution and publisher authentication are distinct evidence types.\n\n"
        "This maintenance change records **0 new or changed theorem declarations and 0 new mathematical assumptions**, with no scientific promotion. The original Lean core and accepted research scope, paper, provenance, toolchain and dependency pins, manifests, application schema and accepted release bytes remain unchanged; the permanent comparator covers all 369 protected entries.\n\n"
        "Strict MA2 remains OPEN. A3 coupling-Wasserstein/KR identification, invariant existence and ergodic factorization are not inferred. D2 retains its proved initialized finite-path reach-and-stay objective, with broader solver obligations open. Both X1 replete-region Exact-GR claims fail; distinct actual-model occupation laws retain their accepted proofs, while numerical margin reflection, unrestricted discounted-history strategy verification and confirmatory/grounding gates remain OPEN. Broader A3/D2/E1 research is outside this maintenance change.\n\n"
        "Downstream K5 remains deferred: all 12 OPS cases retain DEFERRED_BY_USER. An eligible independent reviewer and durable external publication destination remain undetermined; repository settings/read-back, remote archival tags, external publication and retrieval require their separate authorized rollout. Pushing this receipt to a repository branch does not complete those operations or close F3.\n\n"
        "The helper only assembles explicitly selected files and checks source/file joins. It does not independently authenticate copied GitHub JSON or rerun Lean. Historical reproduction scripts may require an explicit repository checkout/environment described in their source; their preserved acquisition paths are mapped in source-reference-map.json.\n\n"
        "[Hash inventory](packet-inventory.json) excludes itself and its checksum sidecar. The first created file is `.gitattributes` with `* -text`, preserving every copied canonical byte during later Git staging.\n").encode()
    files[".gitattributes"] = b"* -text\n"
    for name, data in files.items():
        relative(name)
        screen_payload(data, name)
    output = Path(args.output).absolute()
    if output.exists() or output.is_symlink() or tuple(output.parts[-2:]) != ("maintenance-evidence", "v020-hardening-77"):
        reject("Output must be a new maintenance-evidence/v020-hardening-77 directory")
    resolved = output.resolve()
    source_directories = [final_directory, "hardening-pr77-prebase-acceptance", "hardening-pr78-final-acceptance"]
    if postmerge_directory is not None:
        source_directories.append(postmerge_directory)
    if not resolved.is_relative_to(artifacts.resolve()) or any(resolved.is_relative_to((artifacts / d).resolve()) for d in source_directories):
        reject("Output must be external staging under artifacts/, outside source captures/repositories")
    for parent in output.parents:
        if parent.is_symlink() or (hasattr(parent, "is_junction") and parent.is_junction()):
            reject("Output ancestor is a symlink/junction")
    output.mkdir(parents=True)
    # First write is deliberately the attributes policy, before any payload.
    (output / ".gitattributes").write_bytes(files[".gitattributes"])
    for name in sorted(files):
        if name == ".gitattributes":
            continue
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(files[name])
    records = [{"path": name, "size": len(data), "sha256": sha(data)} for name, data in sorted(files.items())]
    manifest = {"format": "Permansson.CuratedMaintenanceReceipt.v1", "assembled_at": datetime.now(timezone.utc).isoformat(),
                "source": source, "status": "ASSEMBLED", "files": records,
                "curation": {"historical_indices": HISTORICAL_INDICES, "initial_H2_files": list(REQUIRED_FILES[:2]),
                             "premerge_index": args.final_index, "postmerge_index": postmerge_index,
                             "original_source_ledgers_retained": True, "unrelated_artifacts_recursively_copied": False},
                "self_exclusion": ["packet-inventory.json", "packet-inventory.sha256"],
                "authority_limit": "Checksums and packet assembly do not create publisher authentication, a mathematical certificate, an APPROVED review or OPS completion."}
    inventory = json_bytes(manifest)
    (output / "packet-inventory.json").write_bytes(inventory)
    (output / "packet-inventory.sha256").write_bytes((sha(inventory) + "  packet-inventory.json\n").encode())
    for row in records:
        if sha((output / row["path"]).read_bytes()) != row["sha256"]:
            reject("Copied bytes changed during assembly")
    return {"status": "ASSEMBLED", "files": len(records), "inventory_sha256": sha(inventory), "output": str(output), "source": source}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", required=True)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--synthetic", required=True)
    parser.add_argument("--tooling", required=True)
    parser.add_argument("--final-index", required=True, help="artifacts-relative reviewed repaired capture index")
    parser.add_argument("--postmerge-index", help="optional artifacts-relative separately captured main-push index; requires ledger M")
    parser.add_argument("--ledger", required=True)
    parser.add_argument("--unit-ledger", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    try:
        print(json.dumps(assemble(args), sort_keys=True))
        return 0
    except (ValueError, OSError, KeyError, TypeError, zipfile.BadZipFile, subprocess.SubprocessError) as error:
        print("Receipt assembly rejected: " + str(error))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
