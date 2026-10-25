"""PR113 infrastructure-only acceptance, never mathematical or release acceptance.

Use only after a security-reviewed source-controlled T/T2 + A2 workflow is
actually ACTIVE. Detached historical artifact ZIPs must be from successful,
source-bound GitHub Actions jobs. Security review must be real, authorized and
bound to the exact head/artifact bytes; an approval label in JSON is useless.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import stat
import sys
import zipfile

from final_closure_authenticate import (
    AuthenticationError, REQUIRED, authenticated_checks, current_reviews_by_user,
    git as real_git, live as real_live, paginate as real_paginate,
)
import release_target
from pr113_dual_tooling_candidate import validate_dual_reports
from localized_prefix_gate import MUTATIONS as HISTORICAL_MUTATIONS
from pr113_a2_successor_compiler import MUTATIONS as SUCCESSOR_MUTATIONS

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.InfrastructureEvidence.v1"
AUTHORITY_PATH = "research/certification/infrastructure_reviewer_authority.json"
ACTIVE_WORKFLOW = ".github/workflows/pr113-historical-migration-candidates.yml"
REVIEW_PREFIX = "PERMANSSON-INFRA-SECURITY-V1:"
A2_HISTORICAL = "f71a76032b169aac7bfe0694aa715339a94d4e05"
EXPECTED_ARTIFACTS = {
    "T": ("historical-T-and-H-unreviewed", "pr113-T-H-historical-candidate"),
    "A2": ("historical-A2-and-H-unreviewed", "pr113-A2-historical-candidate"),
}
SOURCE_FIELDS = frozenset((
    "run_id", "run_attempt", "job_id", "check_run_id", "artifact_id",
))
EVIDENCE_FIELDS = frozenset((
    "format", "target", "source_bound_ci", "historical_T",
    "historical_A2", "security_review_id",
))
HEX256 = re.compile(r"^[a-f0-9]{64}$")


class InfrastructureError(ValueError):
    pass


def need(test, why):
    if not test:
        raise InfrastructureError(why)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def json_member(files, name):
    need(name in files and 0 < len(files[name]) <= 4 * 1024 * 1024,
         "missing/big original evidence: " + name)
    try:
        item = json.loads(files[name])
    except (ValueError, TypeError) as exc:
        raise InfrastructureError("original source report not valid JSON: " + name) from exc
    need(isinstance(item, dict), "report is not a JSON object: " + name)
    return item


def inspect_zip(raw):
    """Bounded and exact-byte historical artifact member intake; no extraction."""
    need(type(raw) is bytes and 0 < len(raw) <= 256 * 1024 * 1024,
         "missing/oversize original GitHub historical artifact bytes")
    files = {}
    folded = set()
    total = 0
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            infos = z.infolist()
            need(1 <= len(infos) <= 500, "unbounded historical evidence members")
            for item in infos:
                name = item.filename
                path = PurePosixPath(name)
                mode = (item.external_attr >> 16) & 0o170000
                need(isinstance(name, str) and name == path.as_posix()
                     and not path.is_absolute() and not item.is_dir()
                     and "\\" not in name and ".." not in path.parts
                     and len(name) <= 300 and len(path.parts) <= 12
                     and all(x not in ("", ".") for x in name.split("/"))
                     and name.casefold() not in folded
                     and mode in (0, stat.S_IFREG),
                     "unsafe/duplicate historical evidence ZIP member")
                folded.add(name.casefold())
                need(0 < item.file_size <= 64 * 1024 * 1024
                     and item.compress_size > 0
                     and item.file_size <= item.compress_size * 300,
                     "unbounded historical evidence expanded member")
                total += item.file_size
                need(total <= 320 * 1024 * 1024,
                     "historical evidence ZIP exceeds total expanded budget")
                data = z.read(item)
                need(len(data) == item.file_size,
                     "incomplete original historical evidence ZIP member")
                files[name] = data
    except (OSError, RuntimeError, ValueError, zipfile.BadZipFile,
            zipfile.LargeZipFile) as exc:
        raise InfrastructureError("invalid original GH historical ZIP") from exc
    return files


def inspect_T(files, head):
    old_raw = files.get("original_T_archive.json")
    current_raw = files.get("current_H_workflow.json")
    need(type(old_raw) is bytes and type(current_raw) is bytes,
         "historical T and H real underlying reports missing")
    old = json_member(files, "original_T_archive.json")
    current = json_member(files, "current_H_workflow.json")
    try:
        verified = validate_dual_reports(
            old, current, T_source=release_target.T, H_source=head)
    except (ValueError, KeyError, TypeError) as exc:
        raise InfrastructureError("historical T/current H report validation failed") from exc
    receipt = json_member(files, "dual_tooling_unreviewed.json")
    dossier = json_member(files, "T2_security_review_candidate.json")
    need(verified["status"] == "DUAL_T_AND_H_EXECUTED_UNREVIEWED"
         and receipt.get("status") == verified["status"]
         and receipt.get("original_T_archive_unchanged") is True
         and receipt.get("historical_T") == release_target.T
         and receipt.get("current_H") == head
         and receipt.get("historical_T_report_sha256") == sha(old_raw)
         and receipt.get("current_H_report_sha256") == sha(current_raw)
         and receipt.get("independent_security_review") is False
         and receipt.get("versioned_successor_T2_approved") is False
         and dossier.get("format")
             == "Permansson.PR113.ToolingSecurityReviewDossier.v1"
         and dossier.get("status")
             == "COMPLETE_DUAL_EXECUTION_CANDIDATE_SECURITY_REVIEW_PENDING"
         and dossier.get("T") == release_target.T
         and dossier.get("H") == head
         and dossier.get("T_original_offline_restore_report_sha256")
             == sha(old_raw)
         and dossier.get("H_original_workflow_test_report_sha256")
             == sha(current_raw)
         and dossier.get("legacy_T_did_not_accept_current_C") is True
         and dossier.get("owner_authorization_present") is False
         and dossier.get("independent_security_review_present") is False
         and dossier.get("historical_required_CI_replaced") is False
         and dossier.get("required_workflow_inventory_count") == 25,
         "T/T2 candidate does not bind original real reports or historical invariants")
    return {"T_report_sha256": sha(old_raw),
            "H_report_sha256": sha(current_raw),
            "T2_dossier_sha256": sha(files["T2_security_review_candidate.json"])}


def verify_compiler_receipt(files, prefix, expected_status, expected_mutations):
    path = prefix + "/receipt.json"
    row = json_member(files, path)
    need(row.get("status") == expected_status
         and row.get("source_unchanged") is True
         and isinstance(row.get("declarations"), dict)
         and len(row["declarations"]) > 0
         and isinstance(row.get("mutations"), dict)
         and set(row["mutations"]) == set(expected_mutations)
         and all(isinstance(x, dict) and x.get("status") == "SEMANTICALLY_REJECTED"
                 for x in row["mutations"].values()),
         "A2 historical/current compiler proof or semantic negative missing")
    commands = row.get("commands")
    need(isinstance(commands, list) and len(commands) >= 8,
         "A2 compiler did not retain all real command logs")
    labels = {x.get("label") for x in commands if isinstance(x, dict)}
    need({"compiler_version", "research_build", "signatures_axioms",
          "positive_fixture"} <= labels
         and set(expected_mutations) <= labels,
         "A2 compiler failed to run a mandatory proof/control")
    for command in commands:
        need(isinstance(command, dict) and
             type(command.get("returncode")) is int and
             command["returncode"] not in (-999, -998) and
             isinstance(command.get("log"), str) and
             isinstance(command.get("log_sha256"), str) and
             HEX256.fullmatch(command["log_sha256"]),
             "untrusted A2 log source/exit code")
        name = prefix + "/" + command["log"]
        need(name in files and sha(files[name]) == command["log_sha256"],
             "A2 compiled command was not preserved byte-for-byte")
        if command["label"] in expected_mutations:
            need(command["returncode"] != 0 and
                 b"error:" in files[name].lower() and
                 b"parser error" not in files[name].lower() and
                 b"timeout" not in files[name].lower(),
                 "A2 false source did not produce a semantic rejection")
        else:
            need(command["returncode"] == 0,
                 "A2 original nonnegative compiler leg failed")
    for name, entry in row.get("artifacts", {}).items():
        full = prefix + "/" + name
        need(isinstance(entry, dict) and full in files and
             entry.get("sha256") == sha(files[full]) and
             entry.get("bytes") == len(files[full]),
             "A2 reported artifact bytes do not match original ZIP")
    return row, sha(files[path])


def inspect_A2(files, head):
    overall = json_member(files, "unreviewed_dual_A2_candidate.json")
    historical, hhash = verify_compiler_receipt(
        files, "historical_original_A2",
        "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING", HISTORICAL_MUTATIONS)
    successor, shash = verify_compiler_receipt(
        files, "pr113_successor_A2",
        "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING", SUCCESSOR_MUTATIONS)
    prov = overall.get("historical_runtime_provenance")
    need(overall.get("format") == "Permansson.PR113.DualA2CompilerCandidate.v2"
         and overall.get("status")
             == "BOTH_ACTUAL_A2_COMPILER_PATHS_EXECUTED_UNREVIEWED"
         and overall.get("historical_source_commit") == A2_HISTORICAL
         and overall.get("current_source_commit") == head
         and overall.get("historical_test_executed") is True
         and overall.get("successor_test_executed") is True
         and overall.get("historical_semantic_mutants") == 4
         and overall.get("successor_semantic_mutants") == 4
         and overall.get("original_verifier_modified") is False
         and overall.get("independent_security_approval") is False
         and overall.get("independent_mathematical_approval") is False
         and overall.get("merged_main_sha") is None
         and overall.get("full_release_approved") is False
         and isinstance(prov, dict)
         and prov.get("imported_current_A2_gate") is False
         and prov.get("historical_checkout_sha") == A2_HISTORICAL
         and prov.get("output_receipt_sha256") == hhash
         and historical.get("source_unchanged") is True
         and successor.get("source_unchanged") is True,
         "dual A2 report not genuine historical+successor execution scope")
    return {"original_A2_sha256": hhash, "successor_A2_sha256": shash,
            "dual_A2_sha256": sha(files["unreviewed_dual_A2_candidate.json"])}


def exact_committed_lake_blob(head, *, git=real_git):
    """Authentic full Git blob bytes; never .strip() source contents."""
    need(isinstance(head,str) and re.fullmatch(r"[a-f0-9]{40}",head),
         "committed Lake manifest requested for invalid Git H")
    if git is real_git:
        try:
            raw=subprocess.check_output(
                ["git","show",head+":lake-manifest.json"],cwd=ROOT,
                stderr=subprocess.DEVNULL,timeout=25)
        except (OSError,subprocess.CalledProcessError,
                subprocess.TimeoutExpired) as exc:
            raise InfrastructureError("authentic Lake Git blob unavailable") from exc
    else:
        candidate=git("show",head+":lake-manifest.json")
        raw=candidate.encode("utf-8") if isinstance(candidate,str) else candidate
    need(type(raw) is bytes and 0<len(raw)<=1024*1024,
         "Lake source dependency bytes missing or unbounded")
    return raw


def verify_A2_dependency_bridge(files, head, *, manifest_raw):
    """Check the historical dependency bridge against actual committed H bytes.

    It authenticates *candidate evidence* only. It never makes a historical
    verifier into the new mandatory gate and never supplies reviewer authority.
    """
    bridge = json_member(files, "historical_dependency_bridge.json")
    if isinstance(manifest_raw, str):
        manifest_raw = manifest_raw.encode("utf-8")
    need(type(manifest_raw) is bytes and 0 < len(manifest_raw) <= 1024 * 1024,
         "missing true current-H committed Lake manifest")
    try:
        manifest = json.loads(manifest_raw)
    except (ValueError, TypeError) as exc:
        raise InfrastructureError("committed Lean dependency manifest invalid") from exc
    packages = manifest.get("packages") if isinstance(manifest, dict) else None
    need(isinstance(packages, list) and bool(packages) and
         manifest.get("packagesDir") == ".lake/packages",
         "committed dependency manifest invalid or missing package pins")
    expected = {}
    for item in packages:
        need(isinstance(item, dict) and item.get("type") == "git"
             and isinstance(item.get("name"), str)
             and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_-]*", item["name"])
             and item["name"] not in expected
             and isinstance(item.get("rev"), str)
             and re.fullmatch(r"[a-f0-9]{40}", item["rev"]),
             "untrusted, duplicated or unpinned historical dependency")
        expected[item["name"]] = item["rev"]
    need(expected.get("mathlib") ==
             "5ed2965256430c3649e86755f9576b54eca72435",
         "historical A2 dependency closure uses unauthorized mathlib")
    need(set(bridge) == {
             "format", "status", "historical_head", "current_head",
             "manifest_sha256", "pinned_packages", "original_verifier_modified",
             "historical_project_proofs_reused", "independent_security_review",
             "mathematical_acceptance"} and
         bridge.get("format") == "Permansson.PR113.HistoricalA2DependencyBridge.v1"
         and bridge.get("status") ==
             "PINNED_DEPENDENCIES_REUSED_WITHOUT_PROOF_BUILD_IMPORT"
         and bridge.get("historical_head") == A2_HISTORICAL
         and bridge.get("current_head") == head
         and bridge.get("manifest_sha256") == sha(manifest_raw)
         and bridge.get("pinned_packages") == expected
         and bridge.get("original_verifier_modified") is False
         and bridge.get("historical_project_proofs_reused") is False
         and bridge.get("independent_security_review") is False
         and bridge.get("mathematical_acceptance") is False,
         "historical A2 dependency reuse receipt not bound to real pins")
    return sha(files["historical_dependency_bridge.json"])


def source_meta(data):
    need(isinstance(data, dict) and set(data) == SOURCE_FIELDS
         and all(type(data.get(x)) is int and data[x] > 0
                 for x in SOURCE_FIELDS),
         "GH source evidence must contain exact positive run/attempt/job/check/artifact IDs")
    return data


def authenticate_original_zip(kind, identity, original_bytes, head, *, live):
    source_meta(identity)
    run_id, attempt = identity["run_id"], identity["run_attempt"]
    job_id, check_id, artifact_id = (
        identity["job_id"], identity["check_run_id"], identity["artifact_id"])
    run = live(f"/actions/runs/{run_id}")
    jobs = live(f"/actions/runs/{run_id}/jobs?per_page=100")
    check = live(f"/check-runs/{check_id}")
    meta = live(f"/actions/artifacts/{artifact_id}")
    name, artifact_name = EXPECTED_ARTIFACTS[kind]
    need(isinstance(run, dict) and
         run.get("head_sha") == head and
         run.get("head_branch") == "research/final-mathematical-closure" and
         run.get("event") in ("push", "workflow_dispatch") and
         run.get("status") == "completed" and
         run.get("conclusion") == "success" and
         run.get("run_attempt") == attempt and
         str(run.get("path", "")).endswith(ACTIVE_WORKFLOW),
         "historical artifact run not authentic successful final-H workflow")
    joblist = jobs.get("jobs") if isinstance(jobs, dict) else None
    matches = [j for j in joblist if isinstance(j, dict) and
               j.get("id") == job_id] if isinstance(joblist, list) else []
    need(len(matches) == 1, "historical producing job absent/ambiguous")
    job = matches[0]
    need(job.get("run_id") == run_id and
         job.get("run_attempt") == attempt and
         job.get("head_sha") == head and
         job.get("name") == name and
         job.get("status") == "completed" and
         job.get("conclusion") == "success" and
         str(job.get("check_run_url", "")).endswith("/check-runs/" + str(check_id)),
         "historical evidence uploaded by failed/foreign producer job")
    need(isinstance(check, dict) and
         check.get("id") == check_id and
         check.get("name") == name and
         check.get("head_sha") == head and
         check.get("status") == "completed" and
         check.get("conclusion") == "success" and
         (check.get("app") or {}).get("slug") == "github-actions",
         "historical source check is not successful GitHub Actions")
    need(isinstance(meta, dict) and
         meta.get("id") == artifact_id and
         meta.get("name") == artifact_name and
         meta.get("expired") is False and
         meta.get("digest") == "sha256:" + sha(original_bytes) and
         (meta.get("workflow_run") or {}).get("id") == run_id and
         (meta.get("workflow_run") or {}).get("head_sha") == head,
         "source historical artifact ZIP digest/name/run invalid")
    timestamps = [job.get("started_at"), meta.get("created_at"),
                  job.get("completed_at")]
    need(all(isinstance(v, str) and
             re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", v)
             for v in timestamps)
         and timestamps[0] <= timestamps[1] <= timestamps[2],
         "historical artifact uploaded outside producing job attempt")
    return {"run_id": run_id, "attempt": attempt,
            "job_id": job_id, "check_run_id": check_id,
            "artifact_id": artifact_id, "sha256": sha(original_bytes)}


def authority_policy(head, *, git):
    try:
        policy = json.loads(git("show", head + ":" + AUTHORITY_PATH))
    except (ValueError, TypeError, OSError) as exc:
        raise InfrastructureError("versioned security reviewer authority unavailable") from exc
    need(isinstance(policy, dict) and
         set(policy) == {"format", "status", "reviewers", "owner"} and
         policy.get("format") == "Permansson.InfrastructureReviewerAuthority.v1"
         and policy.get("owner") == "HMarcusWH" and
         policy.get("status") == "OWNER_AUTHORIZED" and
         isinstance(policy.get("reviewers"), list) and
         bool(policy["reviewers"]),
         "independent security authority has not been owner-configured")
    return policy


def approved_security_review(review_id, author, head, attest, policy, *, paginate):
    need(type(review_id) is int and review_id > 0,
         "security approval must have an actual GitHub PR review ID")
    approved = 0
    rows = paginate("/pulls/113/reviews")
    for review in current_reviews_by_user(rows).values():
        user = (review.get("user") or {}).get("login")
        if not user or user == author or review.get("id") != review_id or \
                review.get("commit_id") != head or \
                review.get("state") != "APPROVED" or \
                not review.get("submitted_at"):
            continue
        roster = [r for r in policy["reviewers"]
                  if isinstance(r, dict) and r.get("login") == user
                  and r.get("independence_disclosed") is True
                  and r.get("approved_by") == "HMarcusWH"]
        if len(roster) != 1:
            continue
        lines = [line.removeprefix(REVIEW_PREFIX).strip()
                 for line in (review.get("body") or "").splitlines()
                 if line.strip().startswith(REVIEW_PREFIX)]
        need(len(lines) == 1, "review missing/duplicated security attestation")
        try:
            rec = json.loads(lines[0])
        except (ValueError, TypeError) as exc:
            raise InfrastructureError("GitHub security attestation malformed") from exc
        need(isinstance(rec, dict) and rec == attest,
             "security reviewer did not accept exact H/config/T/A2 bytes")
        approved += 1
    need(approved == 1, "genuine current-H independent security review absent")
    return True


def check_historical_only(payload, T_bytes, A2_bytes, *,
                          git=real_git, live=real_live,
                          paginate=real_paginate):
    """Noncircular mandatory-check dependency: T/T2+A2 and real review only.

    Both source-bound producing jobs and the independent security review must
    be genuine. No claim is made about the *caller* being a green check, so this
    can be used inside an authorized replacement required-check workflow.
    The complete 12-context aggregate is verified separately afterward.
    """
    need(isinstance(payload, dict) and set(payload) == EVIDENCE_FIELDS
         and payload.get("format") == FORMAT,
         "wrong infrastructure-only evidence type")
    source = payload.get("target")
    release_target.candidate_bindings(source)
    target = release_target.bind(
        source, intent=release_target.exact_intent(
            source["head_sha"], git=git), git=git, live=live)
    need(target["phase"] == "infrastructure_premerge",
         "certification target cannot borrow infrastructure provenance")
    H = target["head_sha"]
    workflow = git("show", H + ":" + ACTIVE_WORKFLOW)
    need(isinstance(workflow, str) and
         workflow.startswith("# Review-pending source-controlled")
         and "historical-T-and-H-unreviewed" in workflow and
         "historical-A2-and-H-unreviewed" in workflow,
         "required source-controlled T/T2+A2 producer workflow not installed")
    workflow_digest = sha(workflow.encode("utf-8"))
    t_auth = authenticate_original_zip(
        "T", payload["historical_T"], T_bytes, H, live=live)
    a_auth = authenticate_original_zip(
        "A2", payload["historical_A2"], A2_bytes, H, live=live)
    t = inspect_T(inspect_zip(T_bytes), H)
    a = inspect_A2(inspect_zip(A2_bytes), H)
    a["dependency_bridge_sha256"] = verify_A2_dependency_bridge(
        inspect_zip(A2_bytes), H,
        manifest_raw=exact_committed_lake_blob(H, git=git))
    policy = authority_policy(H, git=git)
    pr = live("/pulls/113")
    attestation = {
        "head_sha": H,
        "workflow_sha256": workflow_digest,
        "T_artifact_sha256": sha(T_bytes),
        "A2_artifact_sha256": sha(A2_bytes),
        "original_base_sha": release_target.B113,
    }
    approved_security_review(
        payload["security_review_id"],
        (pr.get("user") or {}).get("login"),
        H, attestation, policy, paginate=paginate)
    return {
        "format": "Permansson.PR113.HistoricalDualRequiredSourceReceipt.v1",
        "status": "HISTORICAL_T_AND_A2_GENUINE_WITH_INDEPENDENT_SECURITY_REVIEW",
        "source_head": H,
        "base_sha": release_target.B113,
        "synthetic_sha": target["synthetic_sha"],
        "workflow_sha256": workflow_digest,
        "T_execution": t,
        "A2_execution": a,
        "genuine_artifacts": {"T": t_auth, "A2": a_auth},
        "security_review_id": payload["security_review_id"],
        "historical_source_and_security_review_authenticated": True,
        "required_ci_successful": 0,
        "independent_mathematical_review": False,
        "accepted_original_cases": 0,
        "accepted_new_claims": 0,
        "merged_main_sha": None,
        "merge_authorized": False,
        "publication_authorized": False,
        "full_release_approved": False,
    }


def check_evidence(payload, T_bytes, A2_bytes, *, git=real_git, live=real_live,
                   checks=authenticated_checks, paginate=real_paginate):
    """Infrastructure aggregation only AFTER all twelve genuine checks pass.

    Required historical checks should call check_historical_only, never this
    aggregate, so they do not depend on their own green check-run statuses.
    """
    historical = check_historical_only(
        payload,T_bytes,A2_bytes,git=git,live=live,paginate=paginate)
    H = historical["source_head"]
    actual = checks(H)
    requested = payload.get("source_bound_ci")
    need(isinstance(requested, list) and
         len(requested) == len(REQUIRED) and
         {r.get("name") for r in requested if isinstance(r, dict)} == REQUIRED,
         "infrastructure requires all twelve genuine source checks")
    for row in requested:
        need(isinstance(row, dict) and
             set(row) == {"name", "id", "head_sha"} and
             row.get("head_sha") == H and
             type(row.get("id")) is int and
             row.get("name") in actual and
             row["id"] == actual[row["name"]]["id"],
             "failed/stale/borrowed required source check")
    result = dict(historical)
    result.update({
        "format": "Permansson.PR113.InfrastructureAcceptanceReceipt.v1",
        "status": "INFRASTRUCTURE_READY_FOR_SEPARATE_OWNER_MERGE_DECISION",
        "required_ci_successful": len(REQUIRED),
        "independent_security_review_authenticated": True,
    })
    return result


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--evidence", type=Path, required=True)
    p.add_argument("--historical-T-zip", type=Path, required=True)
    p.add_argument("--historical-A2-zip", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--historical-only", action="store_true",
                   help="Verify both real original legs and independent review without querying the twelve required check statuses")
    args = p.parse_args(argv)
    try:
        out = args.out.absolute()
        need(not out.exists() and not out.is_symlink()
             and not any(z.is_symlink() for z in out.parents)
             and not out.is_relative_to(ROOT.resolve()),
             "infrastructure result must be fresh and detached")
        ev = args.evidence.read_bytes()
        need(0 < len(ev) <= 64 * 1024, "unbounded detached infrastructure envelope")
        checker = check_historical_only if args.historical_only else check_evidence
        result = checker(
            json.loads(ev), args.historical_T_zip.read_bytes(),
            args.historical_A2_zip.read_bytes())
        out.parent.mkdir(parents=True, exist_ok=True)
        with out.open("x", encoding="utf-8") as f:
            json.dump(result, f, sort_keys=True, indent=2)
            f.write("\n")
        print(json.dumps({"status": result["status"],
                          "source_head": result["source_head"]}, sort_keys=True))
        return 0
    except (InfrastructureError, release_target.TargetError,
            AuthenticationError, OSError, KeyError, TypeError, ValueError) as exc:
        print("INFRASTRUCTURE NOT ACCEPTED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
