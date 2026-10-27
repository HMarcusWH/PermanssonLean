"""Authenticate a PR113 candidate artifact to its REAL producing GitHub job.

Do NOT attach ordinary green research check IDs to detached local logs. This
tool verifies an externally supplied artifact ZIP by GitHub's own SHA-256
artifact digest and authentic workflow/run/job/check-run identities, then
checks its bounded candidate manifest. It cannot attest mathematical truth,
proof-scope sufficiency, a particular reviewer's work, or any release gate.

Artifact authenticity is separate from the full 45/11 source obligations.
No record emitted here may be converted to accepted receipts automatically.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

from final_closure_authenticate import live, paginate, AuthenticationError
from final_closure_case_receipts import load_detached_bundle, EvidenceError
from final_closure_all_original_semantics import select_cases
from final_closure_legacy_semantic_evidence import shard_cases
from final_closure_mutation_evidence import git_head, MutationEvidenceError
from pr113_boundary_io import strict_json_object

BRANCH = "research/final-mathematical-closure"
SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
MAX_ARTIFACT_BYTES = 64 * 1024 * 1024
KINDS = {
    "append": {
        "workflow": ".github/workflows/pr113-all-original-semantic-candidates.yml",
        "job": "semantic-candidate-shard",
        "artifact": "pr113-all-original-semantic-candidates-",
        "count": 9, "manifest": "unreviewed_shard_manifest.json",
    },
    "legacy": {
        "workflow": ".github/workflows/pr113-legacy-semantic-evidence.yml",
        "job": "legacy-original-shard",
        "artifact": "pr113-legacy-semantic-candidates-",
        "count": 8, "manifest": "unreviewed_shard_manifest.json",
    },
    "compiler": {
        "workflow": ".github/workflows/pr113-all-case-compiler.yml",
        "job": "compiler-shard",
        "artifact": "pr113-compiler-shard-",
        "count": 4, "manifest": "complete_compiler_candidate.json",
    },
}


def demand(ok, why):
    if not ok:
        raise AuthenticationError(why)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify_manifest(members: dict, kind: str, shard: int, head: str):
    spec = KINDS[kind]
    name = spec["manifest"]
    demand(name in members, "original candidate manifest missing from artifact")
    try:
        manifest = strict_json_object(members[name])
    except (TypeError, ValueError) as exc:
        raise AuthenticationError("candidate manifest is invalid JSON") from exc
    demand(isinstance(manifest, dict), "candidate manifest must be an object")
    if kind == "append":
        expected = list(select_cases(shard, spec["count"]))
        demand(
            manifest.get("format") == "Permansson.AllOriginalSemanticCandidateShard.v1"
            and manifest.get("status") ==
                "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED_RECEIPT"
            and manifest.get("head") == head
            and manifest.get("shard_index") == shard
            and manifest.get("shard_count") == spec["count"]
            and manifest.get("case_ids") == expected
            and [r.get("case_id") for r in manifest.get("completed", [])
                 if isinstance(r, dict)] == expected
            and manifest.get("independent_review") is False
            and manifest.get("ci_check_run_id") is None
            and manifest.get("mathematical_acceptance") is False,
            "append-only candidate manifest is incomplete, stale or promoted")
    elif kind == "legacy":
        _byid, expected = shard_cases(head, shard, spec["count"])
        expected = list(expected)
        demand(
            manifest.get("format") == "Permansson.OriginalLegacyCompilerShard.v1"
            and manifest.get("status") ==
                "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED"
            and manifest.get("source_head") == head
            and manifest.get("case_ids") == expected
            and [r.get("case_id") for r in manifest.get("case_reports", [])
                 if isinstance(r, dict)] == expected
            and manifest.get("independent_review") is False
            and manifest.get("ci_check_run_id") is None
            and manifest.get("merged_main_sha") is None
            and manifest.get("scientific_release_approved") is False,
            "legacy candidate manifest incomplete, stale or promoted")
        for entry in manifest["case_reports"]:
            tests = entry.get("tests")
            demand(isinstance(tests, list) and bool(tests) and
                   all(t.get("status") ==
                       "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED" and
                       t.get("independent_review") is False and
                       t.get("ci_check_run_id") is None and
                       not t.get("semantic_methods_missing_candidate")
                       for t in tests if isinstance(t, dict)) and
                   all(isinstance(t, dict) for t in tests),
                   "legacy test did not cover all selected semantic negatives")
    else:
        demand(manifest.get("format") == "Permansson.AllCaseCompilerCandidate.v1"
               and manifest.get("status") == "COMPILER_ONLY_UNREVIEWED"
               and manifest.get("head_sha") == head
               and manifest.get("case_count") == 45
               and manifest.get("claim_count") == 11
               and manifest.get("shard_index") == shard
               and manifest.get("shard_count") == spec["count"]
               and manifest.get("independent_review") is False
               and manifest.get("authentic_ci_job_bound") is False
               and manifest.get("merged_main_sha") is None
               and isinstance(manifest.get("compiler_axiom_receipts"), list)
               and len(manifest["compiler_axiom_receipts"]) ==
                   manifest.get("proof_count"),
               "theorem evidence manifest missing or falsely promoted")
    return manifest


def verify_artifact(*, kind: str, shard: int, head: str,
                    run_id: int, artifact_id: int, artifact_zip: Path) -> dict:
    demand(kind in KINDS and type(shard) is int and
           0 <= shard < KINDS[kind]["count"], "invalid shard type or index")
    demand(isinstance(head, str) and SHA40.fullmatch(head),
           "invalid exact source head")
    demand(type(run_id) is int and run_id > 0 and
           type(artifact_id) is int and artifact_id > 0,
           "invalid producing GitHub run or artifact ID")
    demand(git_head() == head, "checkout differs from producing source head")
    demand(os.environ.get("GITHUB_TOKEN"), "live GitHub authentication token required")
    spec = KINDS[kind]
    run = live(f"/actions/runs/{run_id}")
    demand(isinstance(run, dict) and run.get("id") == run_id
           and run.get("head_sha") == head and run.get("head_branch") == BRANCH
           and run.get("event") in ("push", "workflow_dispatch")
           and run.get("status") == "completed"
           and run.get("conclusion") == "success",
           "producing workflow is not successful at exact H")
    workflow_path = str(run.get("path", ""))
    demand(workflow_path == spec["workflow"] or
           workflow_path.endswith("/" + spec["workflow"]),
           "artifact comes from an unexpected workflow source")
    job_rows = paginate(f"/actions/runs/{run_id}/jobs", key="jobs")
    expected_name = f'{spec["job"]} ({shard})'
    jobs = [j for j in job_rows if isinstance(j, dict) and
            j.get("name") == expected_name]
    demand(len(jobs) == 1, "producing matrix job not uniquely identified")
    job = jobs[0]
    demand(job.get("run_id") == run_id and
           job.get("head_sha") == head and
           job.get("status") == "completed" and
           job.get("conclusion") == "success" and
           job.get("run_attempt") == run.get("run_attempt"),
           "producing job is not the current successful attempt")
    check_run_url = job.get("check_run_url")
    demand(isinstance(check_run_url, str) and
           re.fullmatch(
               r"https://api[.]github[.]com/repos/HMarcusWH/PermanssonLean/"
               r"check-runs/[1-9][0-9]*", check_run_url),
           "job is missing its real check-run URL")
    check_id = int(check_run_url.rsplit("/", 1)[-1])
    check = live(f"/check-runs/{check_id}")
    demand(check.get("id") == check_id and
           check.get("head_sha") == head and
           (check.get("app") or {}).get("slug") == "github-actions" and
           check.get("status") == "completed" and
           check.get("conclusion") == "success",
           "real producer check-run does not match GitHub job")
    artifact = live(f"/actions/artifacts/{artifact_id}")
    expected_artifact_name = spec["artifact"] + str(shard)
    digest = artifact.get("digest")
    demand(artifact.get("id") == artifact_id and
           artifact.get("name") == expected_artifact_name and
           artifact.get("expired") is False and
           (artifact.get("workflow_run") or {}).get("id") == run_id and
           (artifact.get("workflow_run") or {}).get("head_sha") == head and
           isinstance(digest, str) and digest.startswith("sha256:") and
           SHA256.fullmatch(digest[7:]),
           "GitHub artifact lacks verified exact-run SHA-256 metadata")
    artifact_zip = Path(artifact_zip)
    demand(artifact_zip.is_file() and not artifact_zip.is_symlink() and
           0 < artifact_zip.stat().st_size <= MAX_ARTIFACT_BYTES,
           "detached uploaded artifact ZIP is unsafe or too large")
    actual = sha(artifact_zip.read_bytes())
    demand(actual == digest[7:],
           "artifact ZIP bytes differ from GitHub authoritative digest")
    try:
        members = load_detached_bundle(artifact_zip, actual)
        manifest = verify_manifest(members, kind, shard, head)
    except (EvidenceError, MutationEvidenceError) as exc:
        raise AuthenticationError("artifact content is unsafe/incomplete") from exc
    return {
        "format": "Permansson.PR113.AuthenticatedProducerArtifact.v1",
        "status": "CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED",
        "head_sha": head,
        "workflow_path": spec["workflow"],
        "run_id": run_id,
        "run_attempt": run.get("run_attempt"),
        "job_id": job.get("id"),
        "actual_check_run_id": check_id,
        "artifact_id": artifact_id,
        "artifact_name": expected_artifact_name,
        "artifact_sha256": actual,
        "manifest_sha256": sha(members[spec["manifest"]]),
        "case_ids_unreviewed": manifest.get("case_ids", []),
        "mathematical_acceptance": False,
        "independent_review": False,
        "scientific_release_approved": False,
        "merged_main_sha": None,
    }


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True)
    ap.add_argument("--kind", required=True, choices=sorted(KINDS))
    ap.add_argument("--shard", required=True, type=int)
    ap.add_argument("--run-id", required=True, type=int)
    ap.add_argument("--artifact-id", required=True, type=int)
    ap.add_argument("--artifact-zip", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    a = ap.parse_args(argv)
    try:
        out = a.output.resolve()
        from final_closure_case_receipts import ROOT
        demand(not out.exists() and not out.is_relative_to(ROOT.resolve())
               and not ROOT.resolve().is_relative_to(out),
               "attestation must be written to a new detached location")
        report = verify_artifact(
            kind=a.kind, shard=a.shard, head=a.head, run_id=a.run_id,
            artifact_id=a.artifact_id, artifact_zip=a.artifact_zip)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, sort_keys=True, indent=2)+"\n")
    except (OSError, ValueError, AuthenticationError, MutationEvidenceError) as exc:
        print("CI ARTIFACT ATTESTATION BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({k: report[k] for k in (
        "status", "head_sha", "artifact_sha256", "actual_check_run_id")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
