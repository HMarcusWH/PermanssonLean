"""Validate downloaded pre-base-change CI bytes against captured GitHub metadata."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import re
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parent
H = "92e45179a5e3ecbe1b2bcadc4da54a0d1657f501"
A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
B = "37c0cb8f2fbe7934639127e5f8b6d64a01e6950f"
S = "d5f2d3a72bda670859c5da87bb173f9eb96696ee"
TREE = "d1c01b2812a13b672f164841a7cc4a8ab7dcc778"
T = "71cc34fa0bc4b639c05d2ec5f39f0b88afd56388"
RUNS = {39068230438, 39068230443, 39068230445, 39068230440, 39068230480, 39068230472}
EXPECTED_CHECKS = {"build", "research", "executable-verification",
                   "Application contract (ubuntu-latest)", "Application contract (windows-latest)",
                   "integrity-portability-windows", "frozen-source-preservation",
                   "release-export-integrity", "archive-reproducibility"}

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def load(name):
    return json.loads((ROOT / name).read_bytes())

def api(name):
    return load(name)["response"]

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def context(value, run):
    expected = {"repository": "HMarcusWH/PermanssonLean", "pr_number": 77,
                "head_sha": H, "base_sha": B, "checked_sha": S,
                "checked_tree": TREE, "accepted_release": A,
                "event": "pull_request", "run_id": run, "run_attempt": 1,
                "scope": "canonical_commit_objects"}
    need(all(value.get(k) == v for k, v in expected.items()), "Report context differs from exact H/B/S/run")
    need(isinstance(value.get("event_sha256"), str) and len(value["event_sha256"]) == 64, "Missing event digest")

checks = api("final-checks.json")
need(checks["total_count"] == len(checks["check_runs"]) == 9, "Expected exactly nine check runs")
need({c["name"] for c in checks["check_runs"]} == EXPECTED_CHECKS, "Unexpected check contexts")
for check in checks["check_runs"]:
    need(check["status"] == "completed" and check["conclusion"] == "success"
         and check["head_sha"] == H and check["app"]["id"] == 15368, "Non-success/wrong source/publisher check")
pr = api("final-pr77.json")
need(pr["head"]["sha"] == H and pr["base"]["sha"] == B and pr["merge_commit_sha"] == S, "PR current head/base/synthetic differs")
synthetic = api("synthetic-commit.json")
need([p["sha"] for p in synthetic["parents"]] == [B, H] and synthetic["tree"]["sha"] == TREE, "Genuine synthetic parent/tree mismatch")
runs = api("final-runs.json")
need(runs["total_count"] == len(runs["workflow_runs"]) == 6, "Unexpected run inventory")
need({r["id"] for r in runs["workflow_runs"]} == RUNS, "Wrong workflow runs")
for run in runs["workflow_runs"]:
    need(run["status"] == "completed" and run["conclusion"] == "success"
         and run["event"] == "pull_request" and run["head_sha"] == H, "Wrong workflow source/result")
jobs = []
for run in runs["workflow_runs"]:
    captured = api("final-jobs-" + str(run["id"]) + ".json")
    need(captured["total_count"] == len(captured["jobs"]), "Incomplete final jobs inventory")
    for job in captured["jobs"]:
        need(job["run_id"] == run["id"] and job["head_sha"] == H
             and job["status"] == "completed" and job["conclusion"] == "success", "Wrong job source/result")
    jobs.extend(captured["jobs"])
need({j["id"] for j in jobs} == {c["id"] for c in checks["check_runs"]} and len(jobs) == 9, "Final check/job identities differ")

artifacts = []
for name in ("final-integrity-artifacts.json", "portability-artifacts.json", "final-research-artifacts.json",
             "final-lean-artifacts.json", "final-verification-artifacts.json", "final-application-artifacts.json"):
    value = api(name)
    need(value["total_count"] == len(value["artifacts"]), "Artifact metadata pagination incomplete")
    artifacts.extend(value["artifacts"])
need(len(artifacts) == 11 and len({a["id"] for a in artifacts}) == 11, "Expected eleven exact artifact records")
report_rows, tests, decoded = [], [], {}
for artifact in artifacts:
    path = ROOT / (artifact["name"] + ".zip")
    raw = path.read_bytes()
    need(len(raw) == artifact["size_in_bytes"] and "sha256:" + sha(raw) == artifact["digest"], "GitHub artifact bytes/digest mismatch")
    run = artifact["workflow_run"]["id"]
    need(artifact["workflow_run"]["head_sha"] == H and run in RUNS and artifact["expired"] is False, "Artifact source/expiry mismatch")
    with ZipFile(path) as archive:
        entries = archive.infolist()
        names = [e.filename for e in entries]
        need(len(names) == len(set(names)) and 0 < len(names) <= 32, "Duplicate/invalid artifact inventory")
        data = {}
        for entry in entries:
            name = entry.filename
            parts = PurePosixPath(name).parts
            need(not name.startswith("/") and "\\" not in name and ":" not in name
                 and parts and all(p not in ("", ".", "..") for p in parts)
                 and not entry.is_dir() and entry.file_size <= 2 * 1024 * 1024
                 and stat.S_IFMT(entry.external_attr >> 16) in (0, stat.S_IFREG), "Unsafe artifact entry")
            need(not entry.flag_bits & 1, "Encrypted artifact")
            if name.endswith(".json"):
                data[name] = json.loads(archive.read(entry))
        if artifact["name"].startswith("hardening-"):
            need("context.json" in data, "Missing required artifact context")
            context(data["context.json"], run)
            for name, value in data.items():
                if name == "context.json":
                    continue
                context(value["context"], run)
                need(value.get("status") == "PASS", "Non-PASS report")
                if name.endswith("-tests.json"):
                    need(value["methods_run"] > 0 and value["errors"] == value["failures"] == value["skips"] == 0
                         and value["execution_tracked_clean"] is True
                         and all(row["status"] == "PASS" for row in value["results"]), "Tests incomplete/dirty/failing")
                    tests.append({"artifact": artifact["name"], "suite": value["suite"],
                                  "methods": value["methods_run"], "subtests": value["subtests_run"],
                                  "covered_requirements": value["covered_requirements"]})
        decoded[artifact["name"]] = data
        report_rows.append({"id": artifact["id"], "name": artifact["name"], "run_id": run,
                            "bytes": len(raw), "sha256": sha(raw), "files": names})

expected_members = {
    "hardening-preservation-reports": {"context.json", "preservation.json", "reference-tests.json", "preservation-tests.json", "context-tests.json", "workflow-tests.json"},
    "hardening-export-reports": {"context.json", "tex-export.json", "tex-tests.json"},
    "hardening-archive-reports": {"context.json", "archive-tests.json", "archive-replay.json"},
    "hardening-windows-portability-reports": {"context.json", "reference-tests.json", "preservation-tests.json", "tex-tests.json"},
}
for key, expected in expected_members.items():
    need(set(decoded[key]) == expected, "Required report inventory mismatch")
need(set(decoded) == set(expected_members) | {"c10-release-evidence", "d0-finite-calculation-evidence",
     "legacy-build-source-context", "legacy-research-source-context", "legacy-executable-source-context",
     "legacy-application-source-context-ubuntu-latest", "legacy-application-source-context-windows-latest"},
     "Unexpected complete artifact name inventory")
preserved = decoded["hardening-preservation-reports"]["preservation.json"]
need(preserved["details"]["protected_count"] == 369 and preserved["details"]["protected_bytes"] == 6680695, "Wrong preservation result")
tex = decoded["hardening-export-reports"]["tex-export.json"]["details"]
need(tex["actual_size"] == 71379 and tex["equation_records"] == 10 and tex["actual_sha256"] == "3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416", "Wrong export result")
replay = decoded["hardening-archive-reports"]["archive-replay.json"]["details"]
tooling = replay["tooling"]
need(tooling == {"binding": "canonical_T_C_and_executing_code", "source_candidate": S,
                 "source_commit": T, "files": 35, "guide_path": "archival/v0.2.0/README.md",
                 "guide_blob": "39fda5fa453fc66985c1cf9f227c81eaf4c1ce6f",
                 "guide_sha256": "d6e53c10c1123444d86a52b9fb478ac09b07364aee6333e5bd76fcf51de0e1e2",
                 "reproduction_instructions_match": True,
                 "publisher_authentication": "not_created_by_content_hashes"},
     "Archive worker did not bind canonical T/C code and guide")
publication = replay["publication"]
need(publication == {"candidate": S, "canonical_inner_files": 71, "members": 71,
     "scope": "canonical_candidate_objects", "sidecar_blob": "4e7691fb4e7dececb28b9cff45d3d95e8fa43e49",
     "status": "PASS", "verified_filesystem_matches_C": True,
     "zip_blob": "9f76cb81cd15c4ab33b4596f65557e8f842f60a5", "zip_bytes": 7465148,
     "zip_path": "archival/v0.2.0/publication-candidate/Permansson_v0.2.0_archival-supplement-1.zip",
     "zip_sha256": "f6f119cadb1a3ebe09f9010510476bab2e75194ededde922eb99a8891652eca4"}
     and "committed_publication" in replay["completed_stages"], "Committed publication ZIP was not bound to genuine candidate C")
isolation = replay["isolation"]
need(isolation["network_isolation"] == "ENFORCED" and isolation["uid"] > 0 and isolation["gid"] > 0
     and isolation["supplementary_groups"] == [] and isolation["capabilities"] == "all_zero"
     and isolation["no_new_privileges"] is True and isolation["outward_routes"] == []
     and isolation["parent_network_namespace"] != isolation["child_network_namespace"]
     and isolation["outward_socket_denied_errno"] in (1, 13, 101, 113), "Offline isolation not enforced")
need(replay["source_restore"] == replay["artifact_replay"] == "PASS"
     and replay["replay_target"] == A and replay["replay_tree"] == "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
     and replay["counts"] == {"refs": 36, "input_commits": 26, "objects": 8202, "legacy_test_methods": 29}, "Replay target/counts wrong")
need([r["stage"] for r in replay["legacy"]] == ["final_release_verifier", "package_verify_only", "legacy_29_tests", "R_c10_consistency"]
     and all(r["exit_code"] == 0 for r in replay["legacy"])
     and "Ran 29 tests" in replay["legacy"][2]["diagnostic_tail"], "Legacy replay stages incomplete")
c10 = load("c10-content-verification.json")
need(c10["status"] == "PASS" and c10["source"] == {"repository": "HMarcusWH/PermanssonLean", "pr_number": 77, "head_sha": H, "base_sha": B, "synthetic_merge_sha": S}, "C10 helper result source mismatch")
c10_artifact = next(row for row in report_rows if row["name"] == "c10-release-evidence")
need(c10["zip_sha256"] == c10_artifact["sha256"] and c10["zip_size"] == c10_artifact["bytes"]
     and c10_artifact["run_id"] == 39068230445 and c10["entries"] == 13
     and c10["local_lean_rerun"] is False, "C10 structural helper is not joined to its publisher ZIP")
threads = load("review-threads-final.json")["result"]["structuredContent"]["review_threads"]
need(all(thread["is_resolved"] for thread in threads), "Unresolved review thread")

# The one-time scope report intentionally remains a local execution record.
# The independent captured genuine tuple above supplies its H/B/S join.
scope = load("maintenance-scope.json")
need(scope["status"] == "PASS" and scope["check"] == "maintenance-Lean-scope"
     and scope["context"]["checked_sha"] == S and scope["context"]["checked_tree"] == TREE
     and scope["context"]["accepted_release"] == A and scope["context"]["event"] == "local", "Actual-S scope report mismatch")
d = scope["details"]
need(d["candidate"] == S and d["candidate_tree"] == TREE and d["accepted_release"] == A
     and d["accepted_tree"] == "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
     and d["acceptance_only"] is True and d["permanent_preservation_policy"] is False
     and d["differences"] == [] and set(d["compared_paths"]) == {
        "PermanssonLean/", "PermanssonLean.lean", "PermanssonResearch/", "PermanssonResearch.lean"}
     and {"fixed_authority", "complete_Lean_scope_comparison"} <= set(d["completed_stages"]), "Incomplete one-time maintenance condition")
need({"context", "verification"} <= set(scope["completed_stages"]), "Incomplete generic check-report stages")
actual = load("actual-maintenance-acceptance.json")
need(actual["status"] == "PASS" and actual["process_exit"] == 0 and actual["checkout_HEAD"] == S
     and actual["checkout_clean_before_and_after"] is True and actual["tree"] == TREE
     and actual["ordered_parents"] == [B, H] and actual["local_event_does_not_manufacture_GitHub_execution"] is True,
     "Actual clean current-S execution receipt mismatch")
need(actual["source"] == decoded["hardening-preservation-reports"]["context.json"]
     and actual["ci_zip_sha256"] == sha((ROOT / "hardening-preservation-reports.zip").read_bytes())
     and actual["report_sha256"] == sha((ROOT / "maintenance-scope.json").read_bytes())
     and actual["executing_module_sha256"] == "fb55ab26b16ce02e154c0c349c9c319614f81713b16c5e9be403ab3c8d8b1411",
     "Scope receipt not bound to independently captured exact source/ZIP/module")
transition = load("live-base-transition.json")
need(transition["status"] == "PASS" and transition["kind"] == "base-change"
     and transition["old_context"]["base_sha"] == A and transition["new_context"]["base_sha"] == B
     and transition["new_context"] == decoded["hardening-preservation-reports"]["context.json"]
     and transition["previous_pair_positive_control"] == transition["current_pair_positive_control"] == "PASS"
     and transition["previous_pair_for_current_objects"] == "E_CONTEXT"
     and transition["new_zip_sha256"] == actual["ci_zip_sha256"], "Live base-change receipt mismatch")
comments = api("final-comments.json")
review = None
for comment in comments:
    match = re.search(r"<!-- codex-review-state:v1 (.*?) -->", comment.get("body", ""))
    if match and comment.get("user", {}).get("login") == "chatgpt-codex-connector[bot]":
        candidate_review = json.loads(match.group(1))
        if candidate_review.get("code_review", {}).get("commit_sha") == H:
            review = candidate_review
need(review is not None and review["code_review"]["commit_sha"] == H
     and review["code_review"]["status"] == "completed"
     and review["code_review"]["has_any_findings"] is False
     and review["code_review"]["has_unresolved_findings"] is False, "No current clean completed Codex code review")
expected_methods = {"reference": 17, "preservation": 26, "context": 6, "workflow": 8, "tex": 20, "archive": 35}
for row in tests:
    need(row["methods"] == expected_methods[row["suite"]], "Unexpected executed method count")
need(sum(row["methods"] for row in tests if row["artifact"] == "hardening-windows-portability-reports") == 63, "Windows 63-method run incomplete")
need(sum(row["methods"] for row in tests if row["artifact"] != "hardening-windows-portability-reports") == 112,
     "Linux 112-method six-suite run incomplete")

legacy_mapping = {
    "legacy-build-source-context": ("build", 39068230472, "Build"),
    "legacy-research-source-context": ("research", 39068230445, "Build research library and audit its transitive axioms"),
    "legacy-executable-source-context": ("executable-verification", 39068230440, "Install Python dependencies"),
    "legacy-application-source-context-ubuntu-latest": ("Application contract (ubuntu-latest)", 39068230480, "Install application-only dependencies"),
    "legacy-application-source-context-windows-latest": ("Application contract (windows-latest)", 39068230480, "Install application-only dependencies"),
}
legacy_contexts = []
for name, (job_name, run_id, first_work) in legacy_mapping.items():
    need(set(decoded[name]) == {"required-source.json"}, "Legacy source artifact has an unexpected payload inventory")
    value = decoded[name]["required-source.json"]
    context(value, run_id)
    need(value["format"] == "Permansson.Hardening.CIContext.v1", "Legacy report format differs")
    matches = [job for job in jobs if job["name"] == job_name and job["run_id"] == run_id]
    need(len(matches) == 1, "No unique actual legacy job for its report")
    job = matches[0]
    guards = [step for step in job["steps"] if step["name"] == "Bind genuine required-check source"]
    work = [step for step in job["steps"] if step["name"] == first_work]
    need(len(guards) == len(work) == 1 and guards[0]["conclusion"] == "success"
         and guards[0]["status"] == "completed" and work[0]["conclusion"] == "success"
         and guards[0]["number"] < work[0]["number"], "Legacy job did not bind genuine source before work")
    row = next(row for row in report_rows if row["name"] == name)
    need(row["run_id"] == run_id, "Legacy publisher artifact run differs from report/job")
    legacy_contexts.append({"name": name, "job": job_name, "job_id": job["id"], "run_id": run_id,
                            "report": value, "sha256": row["sha256"], "bytes": row["bytes"],
                            "guard_step": guards[0]["number"], "work_step": work[0]["number"], "status": "PASS"})
(ROOT / "legacy-context-verification.json").write_text(json.dumps({
    "format": "Permansson.IndependentLegacySourceContextJoin.v1", "status": "PASS",
    "source": {"head": H, "base": B, "synthetic": S, "tree": TREE},
    "records": legacy_contexts, "limits": ["Consistency and execution ordering; no independent publisher authentication"]
}, sort_keys=True, indent=2) + "\n", encoding="utf-8")

report = {
    "format": "Permansson.Hardening.FinalMergeCandidateArtifactVerification.v1", "status": "PASS",
    "executed_at": datetime.now(timezone.utc).isoformat(),
    "source": {"repository": "HMarcusWH/PermanssonLean", "pr_number": 77, "head": H, "base": B, "synthetic": S, "tree": TREE},
    "checks": [{"id": c["id"], "name": c["name"], "app_id": c["app"]["id"], "status": c["status"], "conclusion": c["conclusion"]} for c in checks["check_runs"]],
    "artifacts": report_rows, "tests": tests, "isolation": isolation, "archive_tooling": tooling,
    "publication": publication, "legacy_source_contexts": legacy_contexts,
    "accepted_legacy_replay": {"methods": 29, "target": A, "source_restore": "PASS", "artifact_replay": "PASS"},
    "one_time_actual_S_scope": {"status": "PASS", "candidate": S, "tree": TREE, "local_execution": True, "independent_genuine_tuple_join": True, "scope_report_sha256": actual["report_sha256"], "clean_exit_zero": True}, "live_base_change": {"status": "PASS", "old_base": A, "new_base": B, "stale_result": "E_CONTEXT"}, "codex_review": review, "current_c10": c10, "review_threads": {"count": len(threads), "unresolved": 0},
    "limits": ["This exact merge-candidate tuple does not certify later source changes or eventual main M", "Agent review is not a GitHub APPROVED review", "OPS/reviewer/publication remain deferred", "Captured source metadata and checksums are consistency evidence, not independent publisher authentication"],
}
(ROOT / "verification-summary.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps({"status": "PASS", "checks": 9, "artifacts": 11, "tests": tests, "offline": "ENFORCED", "current_c10": "PASS"}, indent=2))
