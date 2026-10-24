"""Independent exact-M postseal GH artifact authentication (review-pending).

The producer workflow path here is an EXPLICIT *future* security-review target.
Do not introduce it into the accepted 25-workflow inventory until authorized.
A successful local postseal_replay.json is never a valid release certificate.
This verifier demands a real completed GitHub run/job/check/artifact SHA256,
actual candidate ZIP and sidecar bytes, and a second full archive replay.

The work order remains BLOCKED until that workflow exists, an independent
security reviewer approves it, and authentic postmerge evidence is available.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile

from final_closure_authenticate import live, paginate
from final_closure_producer_bytes import inspect_zip, ProducerBytesError

WORKFLOW=".github/workflows/pr113-postseal-replay.yml"
JOB="postseal-archive-replay"
ARTIFACT="pr113-complete-postseal-candidate"
FORMAT="Permansson.PR113.GenuinePostsealCI.v1"
SHA40=re.compile(r"^[0-9a-f]{40}$")
SHA256=re.compile(r"^[0-9a-f]{64}$")

class PostsealAuthenticationError(ValueError):
    pass

def demand(ok, reason):
    if not ok:raise PostsealAuthenticationError(reason)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def validate_postseal_payload(members, *, merged, expected_pdf):
    """Replay complete candidate archive, not a source-owned Boolean label."""
    base="candidate/"
    for name in ("Permansson_Mathematical_Closure_CANDIDATE.zip",
                 "SHA256SUMS.txt"):
        demand(base+name in members,
               "postseal producer omitted original released candidate bytes")
    receipt_name="postseal_replay_receipt.json"
    demand(receipt_name in members,"actual postseal execution receipt missing")
    try:
        executed=json.loads(members[receipt_name])
    except (TypeError,UnicodeError,ValueError) as exc:
        raise PostsealAuthenticationError("invalid postseal execution JSON") from exc
    demand(executed.get("format") ==
           "Permansson.MathClosure.PostsealReplayCandidate.v1" and
           executed.get("status") ==
           "CANDIDATE_ARCHIVE_REPLAYED_UNREVIEWED" and
           executed.get("head_sha") and SHA40.fullmatch(executed["head_sha"]) and
           executed.get("source_commit_sha")==merged and
           executed.get("pdf_sha256")==expected_pdf and
           executed.get("complete_original_members_verified") is True and
           executed.get("authenticated_ci_artifact") is False and
           executed.get("independent_review") is False and
           executed.get("full_release_approved") is False,
           "replay claimed approval or omitted required M/PDF/ZIP provenance")
    candidate=members[base+"Permansson_Mathematical_Closure_CANDIDATE.zip"]
    sidecar=members[base+"SHA256SUMS.txt"]
    demand(sha(candidate)==executed.get("archive_sha256"),
           "released candidate ZIP changed after postseal job")
    root=Path(__file__).resolve().parents[2]
    release=root/"release/mathematical-closure-1"
    if str(release) not in sys.path:
        sys.path.insert(0,str(release))
    from postseal_replay import replay
    with tempfile.TemporaryDirectory(prefix="pr113-verified-postseal-") as tmp:
        original=Path(tmp)/"original"
        original.mkdir()
        zip_path=original/"Permansson_Mathematical_Closure_CANDIDATE.zip"
        sums=original/"SHA256SUMS.txt"
        zip_path.write_bytes(candidate)
        sums.write_bytes(sidecar)
        actual=replay(zip_path,sums,Path(tmp)/"detached"/"verified.json")
    demand(all(actual.get(key)==executed.get(key) for key in (
           "format","status","source_commit_sha","head_sha","pdf_sha256",
           "archive_sha256","manifest_sha256",
           "complete_original_members_verified","authenticated_ci_artifact",
           "independent_review","full_release_approved")),
           "independent replay of original candidate bytes differs from job")
    return actual

def authenticate_postseal(merged, expected_pdf, identities, zipped_artifact):
    """Bind archived M/PDF bytes to approved producing-GH job, not a fake flag."""
    demand(isinstance(merged,str) and SHA40.fullmatch(merged) and
           isinstance(expected_pdf,str) and SHA256.fullmatch(expected_pdf) and
           isinstance(identities,dict),
           "postseal needs real merged-M source and PDF identity")
    for key in ("run_id","run_attempt","job_id","check_run_id","artifact_id"):
        demand(type(identities.get(key)) is int and identities[key]>0,
               "missing source-bound postseal GitHub identity: "+key)
    run=live("/actions/runs/"+str(identities["run_id"]))
    demand(run.get("id")==identities["run_id"] and
           run.get("head_sha")==merged and
           run.get("head_branch")=="main" and
           run.get("event")=="workflow_dispatch" and
           run.get("run_attempt")==identities["run_attempt"] and
           run.get("status")=="completed" and
           run.get("conclusion")=="success" and
           (run.get("path")==WORKFLOW or
            str(run.get("path","")).endswith("/"+WORKFLOW)),
           "postseal producing workflow not a genuine exact-M run")
    rows=paginate("/actions/runs/"+str(identities["run_id"])+"/jobs",key="jobs")
    jobs=[row for row in rows if row.get("id")==identities["job_id"] and
          row.get("name")==JOB]
    demand(len(jobs)==1 and jobs[0].get("run_id")==identities["run_id"] and
           jobs[0].get("head_sha")==merged and
           jobs[0].get("run_attempt")==identities["run_attempt"] and
           jobs[0].get("status")=="completed" and
           jobs[0].get("conclusion")=="success" and
           str(jobs[0].get("check_run_url","")).endswith(
               "/check-runs/"+str(identities["check_run_id"])),
           "postseal job/check is not authentic")
    check=live("/check-runs/"+str(identities["check_run_id"]))
    demand(check.get("id")==identities["check_run_id"] and
           check.get("head_sha")==merged and
           check.get("name")==JOB and
           check.get("status")=="completed" and
           check.get("conclusion")=="success" and
           (check.get("app") or {}).get("slug")=="github-actions",
           "producing postseal check-run is missing or failed")
    artifact=live("/actions/artifacts/"+str(identities["artifact_id"]))
    digest=artifact.get("digest")
    demand(artifact.get("id")==identities["artifact_id"] and
           artifact.get("name")==ARTIFACT and
           artifact.get("expired") is False and
           (artifact.get("workflow_run") or {}).get("id")==identities["run_id"] and
           (artifact.get("workflow_run") or {}).get("head_sha")==merged and
           isinstance(digest,str) and digest.startswith("sha256:") and
           SHA256.fullmatch(digest[7:]),
           "GitHub authoritative postseal artifact identity missing")
    raw_path=Path(zipped_artifact)
    demand(raw_path.is_file() and not raw_path.is_symlink() and
           not any(x.is_symlink() for x in raw_path.absolute().parents),
           "postseal evidence artifact is not a regular unsymlinked input")
    raw=raw_path.read_bytes()
    demand(sha(raw)==digest[7:],
           "postseal original uploaded ZIP differs from real GitHub digest")
    try:
        entries=inspect_zip(raw)
    except ProducerBytesError as exc:
        raise PostsealAuthenticationError("unsafe postseal ZIP") from exc
    actual=validate_postseal_payload(
        entries,merged=merged,expected_pdf=expected_pdf)
    return {
        "format":FORMAT,"status":"COMPLETE_ARCHIVE_REPLAY",
        "source_commit_sha":merged,"pdf_sha256":expected_pdf,
        "artifact_sha256":digest[7:],
        "authenticated_ci_artifact":True,
        "archive_sha256":actual["archive_sha256"],
        "run_id":identities["run_id"],"run_attempt":identities["run_attempt"],
        "job_id":identities["job_id"],"check_run_id":identities["check_run_id"],
        "artifact_id":identities["artifact_id"],
        "independent_scholarly_approval":False,
        "mathematical_release_approved":False,
    }
