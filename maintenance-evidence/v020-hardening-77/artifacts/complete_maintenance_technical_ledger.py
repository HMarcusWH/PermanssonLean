"""Complete this exact maintenance tuple from explicit, already verified evidence.

Standard library only, plus read-only Git object queries. No acquisition, source
mutation, directory inventory, publication, merge or operational promotion.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile

A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
AT = "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
H = None  # Explicit immutable --head, joined to current captured PR and canonical S.
B = "37c0cb8f2fbe7934639127e5f8b6d64a01e6950f"
S = None  # Explicit immutable --synthetic; no stale default.
TREE = None  # Explicit immutable --tree; no stale default.
T = "71cc34fa0bc4b639c05d2ec5f39f0b88afd56388"
REPO = "HMarcusWH/PermanssonLean"
OLD_H = "cc114ee60ff8749b3bb64bb24a8d5e76d2120af9"
OLD_S = "86ff0d8ce3482935d2ff09ee24c260d309f069d1"
HEAD_BASELINE_H = "171c954c4733d2c8eaaac3ad90e60e4d1d4637c3"
HEAD_BASELINE_S = "7743ecbcfec71711f6be9a035934ac01a767c40d"
HEAD_BASELINE_TREE = "90f4d4eeb50a1b801302620571534e1149bda265"
R_HASH = "75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8"
MODULE_HASH = "fb55ab26b16ce02e154c0c349c9c319614f81713b16c5e9be403ab3c8d8b1411"
EXPECTED_BUNDLE_SHA256 = "f49203e5a7f2189565c24509bd56652318ab383dfcda36ee756b78332b1e5792"
GUIDE_HASH = "d6e53c10c1123444d86a52b9fb478ac09b07364aee6333e5bd76fcf51de0e1e2"
REGISTRY_HASH = "000b9d116b5ef24573d3d07825d1ae65ff23120d36bda56d2549a8f20174cf77"
LEGACY_CONTEXTS = {
    "legacy-build-source-context": "build",
    "legacy-research-source-context": "research",
    "legacy-executable-source-context": "executable-verification",
    "legacy-application-source-context-ubuntu-latest": "Application contract (ubuntu-latest)",
    "legacy-application-source-context-windows-latest": "Application contract (windows-latest)",
}
CHECKS = {"build", "research", "executable-verification", "Application contract (ubuntu-latest)",
          "Application contract (windows-latest)", "integrity-portability-windows",
          "frozen-source-preservation", "release-export-integrity", "archive-reproducibility"}
TECHNICAL = {"ARCH-14", "ARCH-23", "CI-01", "CI-02", "CI-04", "CI-05", "CI-08", "CI-10", "CI-11"}
SUITES = {"reference": ("hardening-preservation-reports.zip", "reference-tests.json"),
          "preservation": ("hardening-preservation-reports.zip", "preservation-tests.json"),
          "context": ("hardening-preservation-reports.zip", "context-tests.json"),
          "workflow": ("hardening-preservation-reports.zip", "workflow-tests.json"),
          "tex": ("hardening-export-reports.zip", "tex-tests.json"),
          "archive": ("hardening-archive-reports.zip", "archive-tests.json")}
EXPECTED_METHODS = {"reference": 17, "preservation": 26, "context": 6, "workflow": 8, "tex": 20, "archive": 35}
LIMIT = 8 * 1024 * 1024
ARTIFACTS = Path(__file__).resolve().parent


class LedgerError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise LedgerError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def strict_json(raw):
    require(len(raw) <= LIMIT, "JSON exceeds fixed budget")
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "Duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(LedgerError("Nonfinite JSON")))


def safe_artifact(path, *, exists=True):
    path = Path(path).absolute()
    require(not path.is_symlink() and not any(p.is_symlink() for p in path.parents), "Symlink input/output")
    path = path.resolve()
    require(ARTIFACTS in path.parents, "Evidence/output must stay under this explicit artifacts directory")
    if exists:
        require(path.is_file(), "Missing evidence: " + str(path))
    return path


def raw_file(path, limit=LIMIT):
    path = safe_artifact(path)
    require(path.stat().st_size <= limit, "Evidence exceeds fixed budget")
    with path.open("rb") as stream:
        raw = stream.read(limit + 1)
    require(len(raw) <= limit, "Evidence grew past budget")
    return raw


def document(path):
    return strict_json(raw_file(path))


def api(path):
    value = document(path)
    require(isinstance(value, dict) and isinstance(value.get("response"), (dict, list)), "Missing captured API envelope")
    return value["response"]


def evidence(path, member=None):
    path = safe_artifact(path)
    raw = raw_file(path, 64 * 1024 * 1024)
    relative = path.relative_to(ARTIFACTS).as_posix()
    result = {"path": relative, "original_artifact_path": relative, "sha256": sha(raw), "bytes": len(raw)}
    if member:
        content = zip_member(path, member)
        result.update(member=member, member_sha256=sha(content), member_bytes=len(content))
    return result


def zip_member(path, name):
    safe_artifact(path)
    require(Path(path).stat().st_size <= 64 * 1024 * 1024, "ZIP exceeds fixed budget")
    with zipfile.ZipFile(path) as archive:
        entries = [e for e in archive.infolist() if e.filename == name]
        require(len(entries) == 1, "Missing/duplicate ZIP member: " + name)
        entry = entries[0]
        require(not entry.is_dir() and not entry.flag_bits & 1 and entry.file_size <= LIMIT
                and (entry.external_attr >> 16) & 0o170000 != 0o120000, "Unsupported ZIP member")
        with archive.open(entry) as stream:
            raw = stream.read(LIMIT + 1)
        require(len(raw) == entry.file_size and len(raw) <= LIMIT, "Member length/budget mismatch")
        return raw


def zipped(path, member):
    return strict_json(zip_member(path, member))


def source_context(value, *, head=None, base=None, synthetic=None, tree=None):
    head, base = H if head is None else head, B if base is None else base
    synthetic, tree = S if synthetic is None else synthetic, TREE if tree is None else tree
    expected = {"repository": REPO, "accepted_release": A, "event": "pull_request", "pr_number": 77,
                "head_sha": head, "base_sha": base, "checked_sha": synthetic,
                "checked_tree": tree, "scope": "canonical_commit_objects"}
    require(all(value.get(k) == v for k, v in expected.items())
            and value.get("format", "Permansson.Hardening.CIContext.v1") == "Permansson.Hardening.CIContext.v1", "Stale/wrong source context")
    require(type(value.get("pr_number")) is int and type(value.get("run_id")) is int and value["run_id"] > 0
            and type(value.get("run_attempt")) is int and value["run_attempt"] > 0
            and re.fullmatch(r"[0-9a-f]{64}", value.get("event_sha256", "")), "Missing genuine run/event identity")


def git_read(repo, *args):
    environment = {k: v for k, v in os.environ.items() if not k.upper().startswith("GIT_")}
    environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_SYSTEM=os.devnull, GIT_CONFIG_GLOBAL=os.devnull,
                       GIT_NO_REPLACE_OBJECTS="1", GIT_TERMINAL_PROMPT="0", GIT_OPTIONAL_LOCKS="0")
    result = subprocess.run(["git", "--no-pager", "-c", "core.fsmonitor=false", "-C", str(repo), *args],
                            env=environment, capture_output=True, timeout=60)
    require(result.returncode == 0 and len(result.stdout) <= LIMIT, "Canonical Git read failed")
    return result.stdout


def canonical_pair(repo, context):
    sha_value = context["checked_sha"]
    parents, tree = git_read(repo, "show", "-s", "--format=%P%n%T", sha_value).decode().splitlines()
    require(parents.split() == [context["base_sha"], context["head_sha"]]
            and tree == context["checked_tree"], "Canonical synthetic parent/tree mismatch")


def completed_checks(value, head):
    rows = value["check_runs"]
    require(value["total_count"] == len(rows) == 9 and {r["name"] for r in rows} == CHECKS,
            "Missing/duplicate actual job contexts")
    require(all(r["head_sha"] == head and r["status"] == "completed" and r["conclusion"] == "success"
                and r["app"]["id"] == 15368 for r in rows), "Non-success/wrong source/publisher check")
    return rows


def complete(args):
    capture = Path(args.capture).resolve()
    prebase, head_baseline = Path(args.prebase_capture).resolve(), Path(args.head_baseline_capture).resolve()
    unit = document(args.unit_ledger)
    ledger = deepcopy(unit)
    summary = document(capture / "verification-summary.json")
    require(summary.get("format") == "Permansson.Hardening.FinalMergeCandidateArtifactVerification.v1"
            and summary.get("status") == "PASS", "Final verification-summary PASS is required")
    require(summary["source"] == {"repository": REPO, "pr_number": 77, "head": H, "base": B,
                                  "synthetic": S, "tree": TREE}, "Final summary is not this replacement source")
    context = zipped(capture / "hardening-preservation-reports.zip", "context.json")
    source_context(context)
    canonical_pair(args.repo, context)
    require(git_read(args.repo, "rev-parse", H + "^").decode().strip() == T, "Unexpected packaging/tooling ancestry")
    require(not git_read(args.repo, "diff", "--name-only", B, H, "--", "release").strip(), "Release paths changed")
    canonical_manifest = strict_json(git_read(args.repo, "show", S + ":archival/v0.2.0/supplement-1/archive-manifest.json"))
    require(canonical_manifest["bundle"]["sha256"] == EXPECTED_BUNDLE_SHA256,
            "Unexpected bundle encoding; independent new-pack review is required")
    mc = ledger["maintenance_context"]
    require(mc["head_H"] == H and mc["base_B"] == B and mc["synthetic_S"] == S and mc["synthetic_tree"] == TREE
            and mc["main_merge_M"] is None and mc["main_tree"] is None, "Unit ledger has stale or merged source")
    require(ledger["registry_source"]["commit"] == T and ledger["registry_source"]["sha256"] ==
            REGISTRY_HASH, "Wrong requirement registry authority")
    rows = {r["id"]: r for r in ledger["cases"]}
    require(len(ledger["cases"]) == len(rows) == 108, "Missing/duplicate requirement IDs")
    registry_raw = git_read(args.repo, "show", T + ":verification/integrity/test_coverage.json")
    require(sha(registry_raw) == REGISTRY_HASH, "Canonical registry pin differs")
    registry = strict_json(registry_raw)
    canonical = {r["id"]: r for r in registry["cases"]}
    require(len(canonical) == 108 and set(rows) == set(canonical), "Requirement IDs differ from canonical T")
    require(ledger["registry_controls"] == registry["controls"], "Registry control mapping differs from canonical T")
    for identity, row in rows.items():
        expected = canonical[identity]
        require((row["level"], row["suite"], row["required_methods"]) ==
                (expected["level"], expected["suite"], expected["methods"]), "Requirement level/suite/method differs: " + identity)
    require(Counter(r["status"] for r in rows.values()) == {"PASS": 87, "PENDING_EVIDENCE": 9, "DEFERRED_BY_USER": 12}
            and {i for i, r in rows.items() if r["status"] == "PENDING_EVIDENCE"} == TECHNICAL,
            "Expected exactly 87 unit passes, nine pending technical and twelve deferred OPS")
    require(all(r["level"] == "unit" and r["checked_sha"] == S for r in rows.values() if r["status"] == "PASS"),
            "Unit results belong to another source or level")
    require(all(r["level"] == "authorized_rollout" and r["actual_result"] is None and r["evidence"] == []
                for r in rows.values() if r["status"] == "DEFERRED_BY_USER"), "OPS must remain unexecuted/deferred")
    reserved_units = {i: deepcopy(r) for i, r in rows.items() if r["level"] == "unit"}
    for suite, (archive, member) in SUITES.items():
        report = zipped(capture / archive, member)
        source_context(report["context"])
        require(report["context"] == {k: v for k, v in context.items() if k != "format"}
                and report["status"] == "PASS" and report["errors"] == report["failures"] == report["skips"] == 0
                and report["execution_tracked_clean"] is True and report["methods_run"] == EXPECTED_METHODS[suite]
                and report["format"] == "Permansson.Hardening.Tests.v1" and report["schema_version"] == 1,
                "Wrong/failed source-bound unit report")
        recorded = unit["receipt_assembly"]["reports"][suite]
        require(recorded["sha256"] == sha(zip_member(capture / archive, member))
                and recorded["container_sha256"] == sha(raw_file(capture / archive, 64 * 1024 * 1024)),
                "Unit ledger is not bound to the fresh downloaded reports")

    require(sum(EXPECTED_METHODS.values()) == 112, "Expected112 actual unit methods")
    checks = completed_checks(api(capture / "final-checks.json"), H)
    require(len(summary["checks"]) == 9 and all(c["conclusion"] == "success" for c in summary["checks"]), "Summary checks incomplete")
    pr = api(capture / "final-pr77.json")
    require(pr["head"]["sha"] == H and pr["base"]["sha"] == B and pr["merge_commit_sha"] == S
            and pr["state"] == "open" and pr["merged"] is False, "Not an open current premerge PR tuple")
    runs = api(capture / "final-runs.json")["workflow_runs"]
    require(len(runs) == len({r["id"] for r in runs}) == 6 and all(r["head_sha"] == H and r["event"] == "pull_request"
            and r["status"] == "completed" and r["conclusion"] == "success" for r in runs), "Final six workflows incomplete")
    jobs = []
    for run in runs:
        value = api(capture / ("final-jobs-" + str(run["id"]) + ".json"))
        require(value["total_count"] == len(value["jobs"]), "Incomplete job pagination")
        require(all(j["head_sha"] == H and j["run_id"] == run["id"] and j["status"] == "completed"
                    and j["conclusion"] == "success" for j in value["jobs"]), "Wrong actual job source/result")
        jobs.extend(value["jobs"])
    require(len(jobs) == 9 and {j["id"] for j in jobs} == {c["id"] for c in checks}, "Check/job source inventories differ")
    artifacts = []
    for filename in ("final-integrity-artifacts.json", "portability-artifacts.json", "final-research-artifacts.json",
                     "final-lean-artifacts.json", "final-verification-artifacts.json", "final-application-artifacts.json"):
        value = api(capture / filename)
        require(value["total_count"] == len(value["artifacts"]), "Incomplete artifact pagination")
        artifacts.extend(value["artifacts"])
    names = {"hardening-preservation-reports", "hardening-export-reports", "hardening-archive-reports",
             "hardening-windows-portability-reports", "c10-release-evidence", "d0-finite-calculation-evidence"} | set(LEGACY_CONTEXTS)
    require(len(artifacts) == len({a["id"] for a in artifacts}) == 11 and {a["name"] for a in artifacts} == names, "Missing final artifact inventory")
    for artifact in artifacts:
        payload = raw_file(capture / (artifact["name"] + ".zip"), 64 * 1024 * 1024)
        require(len(payload) == artifact["size_in_bytes"] and "sha256:" + sha(payload) == artifact["digest"]
                and artifact["workflow_run"]["head_sha"] == H
                and artifact["workflow_run"]["id"] in {r["id"] for r in runs}, "Artifact bytes/source differ from publisher metadata")
    legacy_contexts, legacy_evidence = [], []
    for artifact in artifacts:
        if artifact["name"] not in LEGACY_CONTEXTS:
            continue
        source_zip = capture / (artifact["name"] + ".zip")
        with zipfile.ZipFile(source_zip) as archive:
            require(archive.namelist() == ["required-source.json"], "Legacy context artifact is not the exact flat report")
        required_source = zipped(source_zip, "required-source.json")
        source_context(required_source)
        run = next(r for r in runs if r["id"] == artifact["workflow_run"]["id"])
        job = next(j for j in jobs if j["name"] == LEGACY_CONTEXTS[artifact["name"]])
        guards = [step for step in job["steps"] if step["name"] == "Bind genuine required-check source"]
        require(required_source["format"] == "Permansson.Hardening.CIContext.v1"
                and required_source["run_id"] == job["run_id"] == run["id"]
                and required_source["run_attempt"] == run["run_attempt"]
                and len(guards) == 1 and guards[0]["status"] == "completed" and guards[0]["conclusion"] == "success",
                "Legacy source report did not execute successfully in its actual publisher job")
        legacy_contexts.append({"job": job["name"], "job_id": job["id"], "artifact_id": artifact["id"],
                                "source_context": required_source})
        legacy_evidence.append(evidence(source_zip, "required-source.json"))
    require(len(legacy_contexts) == 5 and len(summary["legacy_source_contexts"]) == 5,
            "Missing current legacy required-source evidence")
    review = summary["codex_review"]["code_review"]
    require(review["commit_sha"] == H and review["status"] == "completed" and review["has_any_findings"] is False
            and review["has_unresolved_findings"] is False, "Current completed clean review required")
    thread_capture = document(capture / "review-threads-final.json")
    require(thread_capture["result"].get("isError") is False and thread_capture["request"] ==
            {"pr_number": 77, "repo_full_name": REPO}, "Thread response/error/source differs")
    threads = thread_capture["result"]["structuredContent"]["review_threads"]
    required_threads = {"PRRT_kwDOUkBtPs6" + suffix for suffix in
                        ("tjLfP", "tjLfT", "tjLfU", "tjLfZ", "tjLfb", "tj32h", "tj32j", "tj32m",
                         "tkGIS", "tkGIV", "tkGIY", "tkGIZ")}
    require(required_threads <= {t["id"] for t in threads} and len(threads) >= 12 and len({t["id"] for t in threads}) == len(threads)
            and all(t["is_resolved"] is True for t in threads) and summary["review_threads"]["unresolved"] == 0,
            "Empty/incomplete/unresolved review-thread capture")

    def ev(filename, member=None):
        return evidence(capture / filename, member)
    def fill(identity, checked, result, records, notes=None):
        row = rows[identity]
        require(row["status"] == "PENDING_EVIDENCE" and row["actual_result"] is None and row["evidence"] == [], "Technical case already populated")
        row.update(status="PASS", checked_sha=checked, actual_result=result, evidence=records)
        row["notes"] += notes or []

    original = raw_file(capture / "R-c10.zip")
    metadata = document(capture / "R-c10-artifact-metadata.json")
    require(len(original) == 9377 and sha(original) == R_HASH and metadata["id"] == 12106535829
            and metadata["digest"] == "sha256:" + R_HASH and metadata["workflow_run"]["id"] == 39045919534
            and metadata["workflow_run"]["head_sha"] == "cdbe7ed5124781be495404122fac1de3315cb6ec", "Wrong original R publisher bytes/metadata")
    require(git_read(args.repo, "show", H + ":archival/v0.2.0/supplement-1/evidence/R-c10-artifact-metadata.json") == raw_file(capture / "R-c10-artifact-metadata.json"),
            "Original R metadata differs from canonical package")
    require(git_read(args.repo, "show", H + ":archival/v0.2.0/supplement-1/evidence/R-c10.zip") == original,
            "Original R bytes differ from the canonical new package")
    copied = document(capture / "R-copy-provenance.json")
    require(copied["format"] == "Permansson.HistoricalEvidenceCanonicalCopy.v1" and copied["repository"] == REPO
            and copied["canonical_head"] == H and copied["claim"] ==
            "copy_of_already_acquired_original_publisher_bytes; NOT_fresh_acquisition", "R copy provenance is mislabeled")
    fill("ARCH-14", S, {"artifact_id": 12106535829, "run_id": 39045919534, "bytes": 9377,
         "sha256": R_HASH, "copy_is_new_acquisition": False}, [ev("R-c10.zip"), ev("R-c10-artifact-metadata.json"), ev("R-copy-provenance.json")])
    replay = zipped(capture / "hardening-archive-reports.zip", "archive-replay.json")
    source_context(replay["context"])
    d = replay["details"]
    require(replay["format"] == "Permansson.Hardening.Check.v1" and replay["schema_version"] == 1
            and replay["check"] == "archive-reproducibility" and replay["error_code"] is None
            and replay["status"] == "PASS" and d["source_restore"] == d["artifact_replay"] == "PASS"
            and d["replay_target"] == A and d["replay_tree"] == AT and d["counts"] ==
            {"refs": 36, "input_commits": 26, "objects": 8202, "legacy_test_methods": 29}, "Accepted replay incomplete")
    isolation = d["isolation"]
    require(isolation["network_isolation"] == "ENFORCED" and isolation["parent_network_namespace"] != isolation["child_network_namespace"]
            and isolation["outward_routes"] == [] and isolation["outward_socket_denied_errno"] in {1, 13, 101, 113}
            and isolation["capabilities"] == "all_zero" and isolation["supplementary_groups"] == []
            and isolation["no_new_privileges"] is True and isolation["uid"] != 0 and isolation["gid"] != 0, "Offline execution not enforced")
    tooling = d["tooling"]
    require(tooling["binding"] == "canonical_T_C_and_executing_code" and tooling["source_candidate"] == S
            and tooling["source_commit"] == T and tooling["files"] == 35 and tooling["guide_sha256"] == GUIDE_HASH
            and tooling["reproduction_instructions_match"] is True, "Unbound/stale code-guide closure")
    publication = d["publication"]
    require(publication["status"] == "PASS" and publication["scope"] == "canonical_candidate_objects"
            and publication["candidate"] == S and publication["members"] == publication["canonical_inner_files"] == 71
            and publication["verified_filesystem_matches_C"] is True and "committed_publication" in d["completed_stages"],
            "Committed publication integrity was not established")
    publication_path = "archival/v0.2.0/publication-candidate/Permansson_v0.2.0_archival-supplement-1.zip"
    require(publication["zip_path"] == publication_path
            and sha(git_read(args.repo, "show", S + ":" + publication_path)) == publication["zip_sha256"],
            "Publication report differs from canonical S bytes")
    require([r["stage"] for r in d["legacy"]] == ["final_release_verifier", "package_verify_only", "legacy_29_tests", "R_c10_consistency"]
            and all(r["exit_code"] == 0 for r in d["legacy"]) and d["fresh_lean_execution"] == "NOT_PERFORMED"
            and d["publisher_authentication"] == "NOT_CREATED_BY_OFFLINE_REPLAY", "Legacy replay not complete or mislabeled")
    fill("ARCH-23", S, {"source_restore": "PASS", "artifact_replay": "PASS", "replay_target": A,
         "counts": d["counts"], "isolation": isolation, "tooling": tooling, "publication": publication, "fresh_lean_execution": "NOT_PERFORMED"},
         [ev("hardening-archive-reports.zip", "archive-replay.json"), ev("verification-summary.json")])
    scoped_paths = git_read(args.repo, "diff", "--name-only", B, H).decode().splitlines()
    allowed = (".github/workflows/", ".github/repository-rules/", "verification/integrity/", "verification/archive/",
               "archival/v0.2.0/", "docs/")
    require(scoped_paths and all(path.startswith(allowed) for path in scoped_paths), "PR leaves scoped maintenance paths")
    fill("CI-01", S, {"release_paths_changed": 0, "scoped_maintenance_paths": scoped_paths, "basis": "canonical B-to-H Git diff", "three_hardening_jobs": "success"},
         [ev("final-checks.json"), ev("final-pr77.json"), ev("verification-summary.json")])
    fill("CI-02", S, {"ordered_parents": [B, H], "tree": TREE, "genuine_context": context},
         [ev("synthetic-commit.json"), ev("hardening-preservation-reports.zip", "context.json")])

    head_change = document(capture / "live-head-transition.json")
    previous, accepted = head_change["old_context"], head_change["new_context"]
    source_context(previous, head=HEAD_BASELINE_H, base=B, synthetic=HEAD_BASELINE_S, tree=HEAD_BASELINE_TREE)
    source_context(accepted)
    canonical_pair(args.repo, previous)
    canonical_pair(args.repo, accepted)
    require(accepted == context and head_change["status"] == "PASS" and head_change["kind"] == "head-change"
            and head_change["previous_pair_positive_control"] == head_change["current_pair_positive_control"] == "PASS"
            and head_change["previous_pair_for_current_objects"] == "E_CONTEXT", "Current head-change exercise incomplete")
    old_context_zip = head_baseline / "hardening-preservation-reports.zip"
    require(sha(raw_file(old_context_zip, 64 * 1024 * 1024)) == head_change["old_zip_sha256"]
            and sha(raw_file(capture / "hardening-preservation-reports.zip", 64 * 1024 * 1024)) == head_change["new_zip_sha256"]
            and zipped(old_context_zip, "context.json") == previous, "Head-change ZIP contexts differ")
    old_checks = completed_checks(api(head_baseline / "final-checks-h171-historical.json"), HEAD_BASELINE_H)
    old_green = max(c["completed_at"] for c in old_checks)
    require(old_green < min(r["created_at"] for r in runs), "Current head movement after baseline all-green not established")
    fill("CI-04", S, {"exercise": "fresh head change", "previous_source": previous, "new_source": accepted,
         "stale_result": "E_CONTEXT", "previous_all_nine_green_at": old_green},
         [ev("live-head-transition.json"), evidence(head_baseline / "final-checks-h171-historical.json"),
          evidence(old_context_zip, "context.json"), ev("hardening-preservation-reports.zip", "context.json")],
         ["H171c/B37/S7743 is the actual earlier positive pair; this case is freshly repeated for current H/B/S."])
    transition = document(capture / "live-base-transition.json")
    require(transition["status"] == "PASS" and transition["kind"] == "base-change" and transition["new_context"] == context
            and transition["old_context"]["head_sha"] == OLD_H and transition["old_context"]["base_sha"] == A
            and transition["old_context"]["checked_sha"] == OLD_S and transition["previous_pair_for_current_objects"] == "E_CONTEXT"
            and transition["previous_pair_positive_control"] == transition["current_pair_positive_control"] == "PASS"
            and transition["new_zip_sha256"] == sha(raw_file(capture / "hardening-preservation-reports.zip", 64 * 1024 * 1024))
            and transition["old_zip_sha256"] == sha(raw_file(prebase / "hardening-windows-portability-reports.zip", 64 * 1024 * 1024))
            and transition["old_context"] == zipped(prebase / "hardening-windows-portability-reports.zip", "context.json"), "Fresh base transition mismatched")
    cc_green = max(c["completed_at"] for c in completed_checks(api(prebase / "final-checks.json"), OLD_H))
    merged = document(args.base_merge)
    require(merged["status"] == "PASS" and merged["source"]["main_merge_sha"] == B
            and cc_green < merged["source"]["github_merged_at"], "Observed integration base did not move after prior green")
    fill("CI-05", S, {"old_source": transition["old_context"], "new_source": context, "stale_result": "E_CONTEXT",
         "old_all_nine_green_at": cc_green, "base_merge_at": merged["source"]["github_merged_at"]},
         [ev("live-base-transition.json"), evidence(prebase / "final-checks.json"), evidence(args.base_merge)])
    fill("CI-08", S, {"actual_contexts": sorted(CHECKS), "publisher_app_id": 15368, "all_nine_success": True, "five_legacy_source_guards": legacy_contexts},
         [ev("final-checks.json"), ev("legacy-context-verification.json")] + legacy_evidence)
    credentials = document(capture / "ci10-credential-review.json")
    require(credentials["status"] == "PASS" and credentials["head_sha"] == H and credentials["synthetic_merge_sha"] == S and credentials["H_S_canonical_workflow_blobs_equal"] is True,
            "CI10 requires replacement-head source review")
    pins = {".github/workflows/lean.yml": "2dc2bc23f6013faed093fbff8238801b0dab1bc6a121c9ea12dc07c99fa20432",
            ".github/workflows/research-lean.yml": "cb676566d9c0867b4b990ff83dffded6927972aca58068c6ab185cdf6af64eca",
            ".github/workflows/verification.yml": "8ec37551fc4a7b71e24fac0d5ead92ab308c40b4c35fe83f8befec39f14ce302",
            ".github/workflows/application.yml": "356d62c5e8203ff9cc478f6d5f19d6bccb018eec5c3612b4d30d4b318c8db7e0",
            ".github/workflows/research-integrity.yml": "70cd7e8569beb995981be210369f57c34460289e6a5890c54153683a26939093",
            ".github/workflows/research-integrity-portability.yml": "23c0b16125590d19c017a191b1b4a0b41ea8b15063fc13b246352901f64ad43e"}
    require({w["path"] for w in credentials["workflows"]} == set(pins), "Missing workflow credential review")
    for w in credentials["workflows"]:
        payload = git_read(args.repo, "show", H + ":" + w["path"])
        require(sha(payload) == pins[w["path"]] == w["sha256"] and payload == git_read(args.repo, "show", S + ":" + w["path"])
                and w["top_level_permissions"] == {"contents": "read"} and w["job_permission_overrides"] is False
                and w["candidate_secret_or_write_grant_declarations"] is False and w["checkout_persist_credentials"] is False
                and w["all_action_references_full_immutable_commits"] is True
                and w["checkout_count"] == (3 if w["path"] == ".github/workflows/research-integrity.yml" else 1),
                "Credential source/profile differs")
    fill("CI-10", H, {"review_kind": credentials["review_kind"], "source_head": H, "synthetic_with_same_blobs": S,
         "counted_GitHub_APPROVED_review": False}, [ev("ci10-credential-review.json")])
    c10 = document(capture / "c10-content-verification.json")
    c10_source = {"repository": REPO, "pr_number": 77, "head_sha": H, "base_sha": B, "synthetic_merge_sha": S}
    require(c10["status"] == "PASS" and c10["source"] == c10_source and c10["zip_sha256"] == sha(raw_file(capture / "c10-release-evidence.zip"))
            and summary["current_c10"] == c10 and c10["local_lean_rerun"] is False, "Fresh C10 content/source binding missing")
    research = next((r for r in runs if r["name"] == "Research Lean"), None)
    c10_artifact = next(a for a in artifacts if a["name"] == "c10-release-evidence")
    require(research is not None and c10_artifact["workflow_run"]["id"] == research["id"], "Fresh C10 not published by current Research run")
    fill("CI-11", S, {"source": c10_source, "research_run_id": research["id"], "artifact_id": c10_artifact["id"],
         "current_payload_sha256": c10["zip_sha256"], "proof": c10["proof"], "local_lean_rerun": False,
         "historical_R_remains_separate": True}, [ev("c10-content-verification.json"), ev("c10-release-evidence.zip"), ev("final-research-artifacts.json")])

    scope = document(capture / "maintenance-scope.json")
    actual = document(capture / "actual-maintenance-acceptance.json")
    require(scope["format"] == "Permansson.Hardening.Check.v1" and scope["status"] == "PASS" and scope["error_code"] is None
            and scope["check"] == "maintenance-Lean-scope" and scope["context"]["event"] == "local"
            and scope["context"]["checked_sha"] == S and scope["context"]["checked_tree"] == TREE, "Actual-S scope report missing")
    sd = scope["details"]
    require(sd["accepted_release"] == A and sd["accepted_tree"] == AT and sd["candidate"] == S and sd["candidate_tree"] == TREE
            and sd["acceptance_only"] is True and sd["permanent_preservation_policy"] is False and sd["differences"] == []
            and set(sd["compared_paths"]) == {"PermanssonLean/", "PermanssonResearch/", "PermanssonLean.lean", "PermanssonResearch.lean"}
            and {"fixed_authority", "complete_Lean_scope_comparison"} <= set(sd["completed_stages"]), "Incomplete actual-S scope condition")
    require(actual["status"] == "PASS" and actual["source"] == context and actual["process_exit"] == 0 and actual["checkout_HEAD"] == S
            and actual["ordered_parents"] == [B, H] and actual["tree"] == TREE and actual["checkout_clean_before_and_after"] is True
            and actual["report_sha256"] == sha(raw_file(capture / "maintenance-scope.json")) and actual["executing_module_sha256"] == MODULE_HASH
            and actual["ci_zip_sha256"] == sha(raw_file(capture / "hardening-preservation-reports.zip", 64 * 1024 * 1024)), "Scope/source execution receipt differs")
    independent = document(capture / "actual-scope-independent-review.json")
    require(independent["format"] == "Permansson.Hardening.ActualScopeIndependentReview.v1"
            and independent["status"] == "PASS" and independent["source"] == context
            and independent["canonical_ordered_parents"] == [B, H] and independent["canonical_tree"] == TREE
            and independent["actual_scope_local_report"]["sha256"] == sha(raw_file(capture / "maintenance-scope.json"))
            and independent["actual_scope_receipt"]["sha256"] == sha(raw_file(capture / "actual-maintenance-acceptance.json")),
            "Independent actual-S scope review is stale or incomplete")
    condition = ledger["additional_acceptance_conditions"][0]
    require(condition["outside_108_case_registry"] is True and condition["status"] == "PENDING_EVIDENCE"
            and condition["production_tooling_source"]["commit"] == T, "Wrong/already populated K4 predicate")
    condition.update(status="PASS", checked_sha=S, checked_tree=TREE, actual_result={"process_exit": 0,
                     "local_execution": True, "independent_current_PR_tuple_join": True, "complete_scope_unchanged": True},
                     evidence=[ev("maintenance-scope.json"), ev("actual-maintenance-acceptance.json"), ev("actual-scope-independent-review.json")])
    require(all(rows[i] == r for i, r in reserved_units.items()), "Unit evidence was changed")
    require(Counter(r["status"] for r in rows.values()) == {"PASS": 96, "DEFERRED_BY_USER": 12}, "Final requirement conjunction failed")
    ledger["completion_policy"].update(all108_complete=False, all96_technical_complete=True, overall_F3_closed=False)
    for stage in ("F1.code_verified", "F2.code_verified", "F3.bundle_materialized",
                  "F3.offline_restore_verified", "F3.original_evidence_captured"):
        require(ledger["stage_states"][stage] == "PENDING_EVIDENCE", "Unexpected technical stage state")
        ledger["stage_states"][stage] = "PASS"
    ledger["maintenance_context"].update(main_merge_M=None, main_tree=None,
        workflow_runs=[{"run_id": r["id"], "run_attempt": r["run_attempt"], "conclusion": "success"} for r in runs],
        review_evidence=[ev("ci10-credential-review.json"), ev("final-comments.json"), ev("review-threads-final.json")])
    ledger["receipt_assembly"].update(scope="96 technical cases and separate actual-S K4 condition; 12 OPS deferred",
        remaining_technical_cases=[], merge_acceptance="PREMERGE_CURRENT_TUPLE_ONLY; MAIN_M_NOT_ESTABLISHED")
    ledger["premerge_acceptance"] = {"format": "Permansson.Hardening.PremergeAcceptance.v1", "status": "TECHNICAL_PASS_OPS_DEFERRED",
        "assembled_at_utc": datetime.now(timezone.utc).isoformat(), "source": summary["source"], "tooling_T": T,
        "all_nine_current_checks_green": True, "current_head_review_clean": True, "main_merge_M": None,
        "requirement_status_counts": {"PASS": 96, "DEFERRED_BY_USER": 12}, "actual_candidate_K4_scope": "PASS",
        "raw_unit_ledger": evidence(args.unit_ledger), "final_verification_summary": ev("verification-summary.json"),
        "scope_limits": ["No evidence transfers to a changed H/B/S or eventual main M.",
                         "Agent/code-review evidence is not a counted GitHub APPROVED review or mathematical peer-review certificate.",
                         "Archive replay is distinct from the fresh GitHub Research Lean execution.",
                         "The legitimate bundle repack changed binary encoding; fresh import and offline replay belong to this source, not earlier bundle bytes.",
                         "Reviewer/publication destination remain undetermined; settings/tag/external publication remain deferred."]}
    return ledger


def main(argv=None):
    global H, S, TREE
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("unit-ledger", "capture", "prebase-capture", "head-baseline-capture", "base-merge", "repo", "output", "head", "synthetic", "tree"):
        parser.add_argument("--" + name, required=True)
    args = parser.parse_args(argv)
    try:
        require(all(re.fullmatch(r"[0-9a-f]{40}", v or "") for v in (args.head, args.synthetic, args.tree)), "Full immutable H/S/tree inputs required")
        H, S, TREE = args.head, args.synthetic, args.tree
        require(H != HEAD_BASELINE_H and S != HEAD_BASELINE_S, "Refuse superseded-source acceptance")
        output = safe_artifact(args.output, exists=False)
        require(not output.exists(), "Refuse to overwrite existing acceptance evidence")
        result = complete(args)
        payload = (json.dumps(result, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False) + "\n").encode()
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("xb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        print(json.dumps({"status": "TECHNICAL_PASS_OPS_DEFERRED", "technical_pass": 96,
                          "OPS_deferred": 12, "main_merge_M": None, "sha256": sha(payload)}))
        return 0
    except (LedgerError, OSError, ValueError, TypeError, KeyError, StopIteration, subprocess.SubprocessError, zipfile.BadZipFile) as exc:
        print("Technical ledger completion blocked: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
