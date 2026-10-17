"""Validate downloaded pre-base-change CI bytes against captured GitHub metadata."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parent
H = "cc114ee60ff8749b3bb64bb24a8d5e76d2120af9"
B = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
S = "86ff0d8ce3482935d2ff09ee24c260d309f069d1"
TREE = "bc2af29f32f6b89b5ea927ea04a6579422e4e6eb"
RUNS = {39061789373, 39061789338, 39061789410, 39061789402, 39061789322, 39061789385}
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
                "checked_tree": TREE, "accepted_release": B,
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
need(pr["head"]["sha"] == H and pr["base"]["sha"] == B and pr["merge_commit_sha"] == S, "PR was not captured before base transition")
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
for name in ("final-integrity-artifacts.json", "portability-artifacts.json", "final-research-artifacts.json"):
    value = api(name)
    need(value["total_count"] == len(value["artifacts"]), "Artifact metadata pagination incomplete")
    artifacts.extend(value["artifacts"])
need(len(artifacts) == 6 and len({a["id"] for a in artifacts}) == 6, "Expected six exact artifact records")
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
preserved = decoded["hardening-preservation-reports"]["preservation.json"]
need(preserved["details"]["protected_count"] == 369 and preserved["details"]["protected_bytes"] == 6680695, "Wrong preservation result")
tex = decoded["hardening-export-reports"]["tex-export.json"]["details"]
need(tex["actual_size"] == 71379 and tex["equation_records"] == 10 and tex["actual_sha256"] == "3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416", "Wrong export result")
replay = decoded["hardening-archive-reports"]["archive-replay.json"]["details"]
isolation = replay["isolation"]
need(isolation["network_isolation"] == "ENFORCED" and isolation["uid"] > 0 and isolation["gid"] > 0
     and isolation["supplementary_groups"] == [] and isolation["capabilities"] == "all_zero"
     and isolation["no_new_privileges"] is True and isolation["outward_routes"] == []
     and isolation["parent_network_namespace"] != isolation["child_network_namespace"]
     and isolation["outward_socket_denied_errno"] in (1, 13, 101, 113), "Offline isolation not enforced")
need(replay["source_restore"] == replay["artifact_replay"] == "PASS"
     and replay["replay_target"] == B and replay["replay_tree"] == "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
     and replay["counts"] == {"refs": 36, "input_commits": 26, "objects": 8202, "legacy_test_methods": 29}, "Replay target/counts wrong")
need([r["stage"] for r in replay["legacy"]] == ["final_release_verifier", "package_verify_only", "legacy_29_tests", "R_c10_consistency"]
     and all(r["exit_code"] == 0 for r in replay["legacy"])
     and "Ran 29 tests" in replay["legacy"][2]["diagnostic_tail"], "Legacy replay stages incomplete")
c10 = load("c10-content-verification.json")
need(c10["status"] == "PASS" and c10["source"] == {"repository": "HMarcusWH/PermanssonLean", "pr_number": 77, "head_sha": H, "base_sha": B, "synthetic_merge_sha": S}, "C10 helper result source mismatch")
threads = load("review-threads-final.json")["result"]["structuredContent"]["review_threads"]
need(all(thread["is_resolved"] for thread in threads), "Unresolved review thread")
report = {
    "format": "Permansson.Hardening.PrebaseCIArtifactVerification.v1", "status": "PASS",
    "executed_at": datetime.now(timezone.utc).isoformat(),
    "source": {"repository": "HMarcusWH/PermanssonLean", "pr_number": 77, "head": H, "base": B, "synthetic": S, "tree": TREE},
    "checks": [{"id": c["id"], "name": c["name"], "app_id": c["app"]["id"], "status": c["status"], "conclusion": c["conclusion"]} for c in checks["check_runs"]],
    "artifacts": report_rows, "tests": tests, "isolation": isolation,
    "accepted_legacy_replay": {"methods": 29, "target": B, "source_restore": "PASS", "artifact_replay": "PASS"},
    "current_c10": c10, "review_threads": {"count": len(threads), "unresolved": 0},
    "limits": ["This exact prebase tuple does not certify later base/head changes or final integration", "No standalone candidate-bound maintenance-scope CLI receipt at this head; that follow-up remains open", "Agent review is not a GitHub APPROVED review", "OPS/reviewer/publication remain deferred", "Captured source metadata and checksums are consistency evidence, not independent publisher authentication"],
}
(ROOT / "verification-summary.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps({"status": "PASS", "checks": 9, "artifacts": 6, "tests": tests, "offline": "ENFORCED", "current_c10": "PASS"}, indent=2))
