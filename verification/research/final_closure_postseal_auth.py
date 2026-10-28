"""Independent exact-M postseal GH artifact authentication (review-pending).

The producer workflow path here is an EXPLICIT *future* security-review target.
Do not introduce it into the accepted 25-workflow inventory until authorized.
A successful local postseal_replay.json is never a valid release certificate.
This verifier demands a real completed GitHub run/job/check/artifact SHA256,
actual candidate ZIP and sidecar bytes, and a second full archive replay.

The work order remains BLOCKED until that workflow exists, an independent
security reviewer approves it, and authentic postmerge evidence is available.

The upstream preseal producer is authenticated in its own right: an artifact
digest and run ID are not enough, because an `if: always()` upload from a
failed, cancelled or superseded producer attempt carries an authentic digest.
Its workflow/job/artifact names below are the proposed P1-12 contract, also
pending independent security review.
"""
from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import tempfile
import zipfile

from final_closure_authenticate import live, paginate

WORKFLOW=".github/workflows/pr113-postseal-replay.yml"
JOB="postseal-archive-replay"
ARTIFACT="pr113-complete-postseal-candidate"
UPSTREAM_WORKFLOW=".github/workflows/pr113-preseal-fullscope.yml"
UPSTREAM_JOB="preseal-fullscope-candidate"
UPSTREAM_ARTIFACT="pr113-preseal-fullscope-candidate"
UPSTREAM_EVENTS=("push","workflow_dispatch")
UPSTREAM_METADATA="upstream_source_artifact.json"
IDENTITY_KEYS=("run_id","run_attempt","job_id","check_run_id","artifact_id")
FORMAT="Permansson.PR113.GenuinePostsealCI.v1"
SHA40=re.compile(r"^[0-9a-f]{40}$")
SHA256=re.compile(r"^[0-9a-f]{64}$")
CANDIDATE_MEMBER="candidate/Permansson_Mathematical_Closure_CANDIDATE.zip"
POSTSEAL_MEMBERS=frozenset((CANDIDATE_MEMBER,"candidate/SHA256SUMS.txt",
                            "postseal_replay_receipt.json",UPSTREAM_METADATA))
# Match postseal_replay.MAX_ARCHIVE_BYTES for the single nested candidate.
# Metadata retains the original producer reader's individual 4MiB bound.
MAX_CANDIDATE_BYTES=384*1024*1024
MAX_METADATA_BYTES=4*1024*1024
MAX_EXPANDED_BYTES=MAX_CANDIDATE_BYTES+3*MAX_METADATA_BYTES
# Four ZIP records can add local/central extra fields and comments. Reserve
# a bounded 1MiB above their entire permitted payload, including stored ZIPs.
MAX_POSTSEAL_ZIP_BYTES=MAX_EXPANDED_BYTES+1024*1024

class PostsealAuthenticationError(ValueError):
    pass

def demand(ok, reason):
    if not ok:raise PostsealAuthenticationError(reason)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def read_postseal_zip(path):
    """Bound the transport before allocation, including a changing file."""
    declared=path.stat().st_size
    demand(0<declared<=MAX_POSTSEAL_ZIP_BYTES,
           "missing or oversized postseal ZIP before reading")
    with path.open("rb") as stream:
        raw=stream.read(declared+1)
    demand(0<len(raw)<=MAX_POSTSEAL_ZIP_BYTES and len(raw)==declared,
           "postseal ZIP size changed or exceeded its wire budget")
    return raw


def inspect_postseal_zip(raw):
    """Read the exact four-file producer envelope, not producer-log budgets."""
    demand(type(raw) is bytes and 0<len(raw)<=MAX_POSTSEAL_ZIP_BYTES,
           "missing or oversized postseal ZIP")
    result,seen,total={},set(),0
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as zipped:
            rows=zipped.infolist()
            demand(len(rows)==len(POSTSEAL_MEMBERS),
                   "postseal ZIP must contain exactly four producer members")
            for row in rows:
                name=row.filename
                path=PurePosixPath(name)
                mode=stat.S_IFMT(row.external_attr>>16)
                demand(row.orig_filename==name and name and
                       not row.is_dir() and not (row.flag_bits&1) and
                       not path.is_absolute() and ".." not in path.parts and
                       "\\" not in name and path.as_posix()==name and
                       not any(part in ("", ".") for part in name.split("/")) and
                       mode in (0,stat.S_IFREG) and name.casefold() not in seen,
                       "unsafe, duplicated or nonregular postseal member")
                seen.add(name.casefold())
                limit=MAX_CANDIDATE_BYTES if name==CANDIDATE_MEMBER else MAX_METADATA_BYTES
                total+=row.file_size
                demand(0<row.file_size<=limit and total<=MAX_EXPANDED_BYTES,
                       "unbounded postseal archive expansion")
            demand({row.filename for row in rows}==POSTSEAL_MEMBERS,
                   "postseal ZIP inventory differs from the exact producer files")
            for name in seen:
                parts=name.split("/")
                demand(not any("/".join(parts[:i]) in seen
                               for i in range(1,len(parts))),
                       "postseal ZIP member shadows path ancestor")
            for row in rows:
                with zipped.open(row) as stream:
                    content=stream.read(row.file_size+1)
                demand(len(content)==row.file_size,
                       "postseal ZIP decompression length mismatch")
                result[row.filename]=content
    except (OSError,zipfile.BadZipFile,RuntimeError,NotImplementedError,UnicodeError) as exc:
        raise PostsealAuthenticationError("invalid postseal ZIP") from exc
    return result


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

def authentic_producer(ids, merged, *, workflow, job, artifact_name, events):
    """Authenticate one completed, successful exact-M producer and artifact."""
    run=live("/actions/runs/"+str(ids["run_id"]))
    demand(run.get("id")==ids["run_id"] and
           run.get("head_sha")==merged and
           run.get("head_branch")=="main" and
           run.get("event") in events and
           run.get("run_attempt")==ids["run_attempt"] and
           run.get("status")=="completed" and
           run.get("conclusion")=="success" and
           (run.get("path")==workflow or
            str(run.get("path","")).endswith("/"+workflow)),
           "producing workflow not a genuine successful exact-M run: "+job)
    rows=paginate("/actions/runs/"+str(ids["run_id"])+"/jobs",key="jobs")
    jobs=[row for row in rows if row.get("id")==ids["job_id"] and
          row.get("name")==job]
    demand(len(jobs)==1 and jobs[0].get("run_id")==ids["run_id"] and
           jobs[0].get("head_sha")==merged and
           jobs[0].get("run_attempt")==ids["run_attempt"] and
           jobs[0].get("status")=="completed" and
           jobs[0].get("conclusion")=="success" and
           str(jobs[0].get("check_run_url","")).endswith(
               "/check-runs/"+str(ids["check_run_id"])),
           "producer job/check is not authentic: "+job)
    check=live("/check-runs/"+str(ids["check_run_id"]))
    demand(check.get("id")==ids["check_run_id"] and
           check.get("head_sha")==merged and
           check.get("name")==job and
           check.get("status")=="completed" and
           check.get("conclusion")=="success" and
           (check.get("app") or {}).get("slug")=="github-actions",
           "producing check-run is missing or failed: "+job)
    artifact=live("/actions/artifacts/"+str(ids["artifact_id"]))
    digest=artifact.get("digest")
    demand(artifact.get("id")==ids["artifact_id"] and
           artifact.get("name")==artifact_name and
           artifact.get("expired") is False and
           (artifact.get("workflow_run") or {}).get("id")==ids["run_id"] and
           (artifact.get("workflow_run") or {}).get("head_sha")==merged and
           isinstance(digest,str) and digest.startswith("sha256:") and
           SHA256.fullmatch(digest[7:]),
           "GitHub authoritative artifact identity missing: "+artifact_name)
    # The artifacts API has no attempt field: bind the upload to the window
    # of the authenticated successful job attempt, so an artifact retained
    # from a failed earlier attempt of the same run is not accepted.
    stamps=(jobs[0].get("started_at"),artifact.get("created_at"),
            jobs[0].get("completed_at"))
    demand(all(isinstance(x,str) and
               re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ",x)
               for x in stamps) and stamps[0]<=stamps[1]<=stamps[2],
           "artifact was not uploaded by the successful producer attempt: "+
           artifact_name)
    return run, digest[7:]

def bind_upstream_metadata(entries, merged, upstream_ids, upstream_digest):
    """The postseal job must have replayed exactly the authenticated input."""
    demand(UPSTREAM_METADATA in entries,
           "postseal job did not retain its upstream artifact identity")
    try:
        meta=json.loads(entries[UPSTREAM_METADATA])
    except (TypeError,UnicodeError,ValueError) as exc:
        raise PostsealAuthenticationError("invalid upstream metadata JSON") from exc
    demand(isinstance(meta,dict) and
           meta.get("id")==upstream_ids["artifact_id"] and
           meta.get("name")==UPSTREAM_ARTIFACT and
           meta.get("digest")=="sha256:"+upstream_digest and
           (meta.get("workflow_run") or {}).get("id")==upstream_ids["run_id"] and
           (meta.get("workflow_run") or {}).get("head_sha")==merged,
           "postseal replayed a different upstream preseal artifact")

def authenticate_postseal(merged, expected_pdf, identities, zipped_artifact):
    """Bind archived M/PDF bytes to approved producing-GH job, not a fake flag."""
    demand(isinstance(merged,str) and SHA40.fullmatch(merged) and
           isinstance(expected_pdf,str) and SHA256.fullmatch(expected_pdf) and
           isinstance(identities,dict),
           "postseal needs real merged-M source and PDF identity")
    upstream={key:identities.get("upstream_"+key) for key in IDENTITY_KEYS}
    for key in IDENTITY_KEYS:
        demand(type(identities.get(key)) is int and identities[key]>0,
               "missing source-bound postseal GitHub identity: "+key)
        demand(type(upstream[key]) is int and upstream[key]>0,
               "missing upstream preseal producer identity: "+key)
    demand(upstream["run_id"]!=identities["run_id"] and
           upstream["artifact_id"]!=identities["artifact_id"],
           "postseal cannot be its own upstream preseal producer")
    upstream_run,upstream_digest=authentic_producer(
        upstream,merged,workflow=UPSTREAM_WORKFLOW,job=UPSTREAM_JOB,
        artifact_name=UPSTREAM_ARTIFACT,events=UPSTREAM_EVENTS)
    run,digest=authentic_producer(
        identities,merged,workflow=WORKFLOW,job=JOB,
        artifact_name=ARTIFACT,events=("workflow_dispatch",))
    stamps=(upstream_run.get("updated_at"),run.get("run_started_at"))
    demand(all(isinstance(x,str) for x in stamps) and stamps[0]<=stamps[1],
           "upstream preseal producer had not finished before postseal began")
    raw_path=Path(zipped_artifact)
    demand(raw_path.is_file() and not raw_path.is_symlink() and
           not any(x.is_symlink() for x in raw_path.absolute().parents),
           "postseal evidence artifact is not a regular unsymlinked input")
    raw=read_postseal_zip(raw_path)
    demand(sha(raw)==digest,
           "postseal original uploaded ZIP differs from real GitHub digest")
    entries=inspect_postseal_zip(raw)
    bind_upstream_metadata(entries,merged,upstream,upstream_digest)
    actual=validate_postseal_payload(
        entries,merged=merged,expected_pdf=expected_pdf)
    return {
        "format":FORMAT,"status":"COMPLETE_ARCHIVE_REPLAY",
        "source_commit_sha":merged,"pdf_sha256":expected_pdf,
        "artifact_sha256":digest,
        "authenticated_ci_artifact":True,
        "archive_sha256":actual["archive_sha256"],
        "run_id":identities["run_id"],"run_attempt":identities["run_attempt"],
        "job_id":identities["job_id"],"check_run_id":identities["check_run_id"],
        "artifact_id":identities["artifact_id"],
        "upstream_preseal":{**upstream,"artifact_sha256":upstream_digest},
        "independent_scholarly_approval":False,
        "mathematical_release_approved":False,
    }
