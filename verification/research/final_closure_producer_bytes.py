"""Exact source-bound 21-artifact verification; never mathematical approval."""
from __future__ import annotations
import hashlib
import io
import re
import stat
import zipfile
from pathlib import PurePosixPath

from final_closure_authenticate import live, paginate
from final_closure_candidate_artifact_auth import KINDS
from final_closure_producer_v2_bridge import verified_producer_index

FORMAT = "Permansson.PR113.ProducerBytesRevalidated.v1"

class ProducerBytesError(ValueError):
    pass

def demand(ok, reason):
    if not ok:
        raise ProducerBytesError(reason)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inspect_zip(raw):
    demand(type(raw) is bytes and 0 < len(raw) <= 64*1024*1024,
           "missing or oversized producer ZIP")
    result, seen, total = {}, set(), 0
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            rows = z.infolist()
            demand(len(rows) <= 512, "too many producer members")
            for row in rows:
                name = row.filename
                path = PurePosixPath(name)
                mode = (row.external_attr >> 16) & 0o170000
                demand(name and not row.is_dir() and
                       not path.is_absolute() and ".." not in path.parts and
                       "\\" not in name and path.as_posix() == name and
                       not any(x in ("", ".") for x in name.split("/")) and
                       mode in (0, stat.S_IFREG) and
                       name.casefold() not in seen,
                       "unsafe, duplicated or nonregular producer member")
                seen.add(name.casefold())
                total += row.file_size
                demand(row.file_size <= 4*1024*1024 and total <= 64*1024*1024,
                       "unbounded producer archive expansion")
            for name in seen:
                segments = name.split("/")
                demand(not any("/".join(segments[:i]) in seen
                               for i in range(1, len(segments))),
                       "producer ZIP member shadows path ancestor")
            for row in rows:
                content = z.read(row)
                demand(len(content) == row.file_size,
                       "ZIP member decompression length mismatch")
                result[row.filename] = content
    except (OSError, zipfile.BadZipFile, RuntimeError) as exc:
        raise ProducerBytesError("invalid producer archive") from exc
    return result

def authenticate(head, attestations, zip_bytes):
    """All 4+9+8 genuine job, check and SHA-256 bindings must match."""
    try:
        indexed = verified_producer_index(head, attestations)
    except (ValueError, TypeError, KeyError) as exc:
        raise ProducerBytesError("incomplete/untrusted 21-shard index") from exc
    demand(type(zip_bytes) is dict and set(zip_bytes) ==
           {x["artifact_id"] for x in indexed.values()},
           "missing or borrowed producer ZIP")
    verified = {}
    total = 0
    for (kind, shard), row in indexed.items():
        spec = KINDS[kind]
        run = live("/actions/runs/" + str(row["run_id"]))
        demand(run.get("id") == row["run_id"] and
               run.get("head_sha") == head and
               run.get("run_attempt") == row["run_attempt"] and
               run.get("status") == "completed" and
               run.get("conclusion") == "success" and
               run.get("event") in ("push", "workflow_dispatch") and
               run.get("head_branch") == "research/final-mathematical-closure" and
               (run.get("path") == spec["workflow"] or
                str(run.get("path", "")).endswith("/" + spec["workflow"])),
               "GitHub producer workflow identity not authenticated")
        jobs = paginate("/actions/runs/"+str(row["run_id"])+"/jobs", key="jobs")
        expected_name = spec["job"] + f" ({shard})"
        matched = [j for j in jobs if
                   j.get("id") == row["job_id"] and
                   j.get("name") == expected_name]
        demand(len(matched) == 1 and
               matched[0].get("head_sha") == head and
               matched[0].get("run_attempt") == row["run_attempt"] and
               matched[0].get("run_id") == row["run_id"] and
               matched[0].get("status") == "completed" and
               matched[0].get("conclusion") == "success" and
               str(matched[0].get("check_run_url","")).endswith(
                   "/check-runs/" + str(row["actual_check_run_id"])),
               "producer job/check identity mismatch")
        check = live("/check-runs/" + str(row["actual_check_run_id"]))
        demand(check.get("id") == row["actual_check_run_id"] and
               check.get("head_sha") == head and
               check.get("name") == expected_name and
               check.get("status") == "completed" and
               check.get("conclusion") == "success" and
               (check.get("app") or {}).get("slug") == "github-actions",
               "producer check must be actual successful shard, not research")
        artifact = live("/actions/artifacts/" + str(row["artifact_id"]))
        demand(artifact.get("id") == row["artifact_id"] and
               artifact.get("name") == spec["artifact"]+str(shard) and
               artifact.get("expired") is False and
               (artifact.get("workflow_run") or {}).get("id") == row["run_id"] and
               (artifact.get("workflow_run") or {}).get("head_sha") == head and
               artifact.get("digest") == "sha256:" + row["artifact_sha256"],
               "GitHub authoritative producer ZIP metadata mismatch")
        data = zip_bytes[row["artifact_id"]]
        demand(type(data) is bytes and sha(data) == row["artifact_sha256"],
               "source ZIP bytes do not equal GitHub sha256")
        total += len(data)
        demand(total <= 256*1024*1024, "aggregate producer ZIP budget exceeded")
        members = inspect_zip(data)
        manifest = spec["manifest"]
        demand(manifest in members and sha(members[manifest]) ==
               row["manifest_sha256"],
               "original producer manifest not retained")
        verified[row["artifact_id"]] = {
            "check_run_id":row["actual_check_run_id"],
            "head_sha":head, "kind":kind, "shard":shard, "members":members}
    return {"format":FORMAT,"status":"REAL_PRODUCING_BYTES_UNREVIEWED",
            "head_sha":head,"producers":verified,
            "producer_count":21,"accepted_cases":0,"accepted_claims":0,
            "independent_review":False,"release_approved":False}

def original_member(record, artifact_id, check_run_id, member, digest):
    """Bind an individual receipt byte string to original producing ZIP."""
    demand(record.get("format") == FORMAT and
           type(artifact_id) is int and type(check_run_id) is int and
           isinstance(member,str) and isinstance(digest,str) and
           re.fullmatch("[0-9a-f]{64}",digest),
           "malformed receipt producing identity")
    entry = record.get("producers",{}).get(artifact_id)
    demand(entry is not None and entry.get("check_run_id") == check_run_id and
           entry.get("head_sha") == record.get("head_sha"),
           "wrong producing job for receipt")
    data = entry["members"].get(member)
    demand(data is not None and sha(data) == digest,
           "receipt member not present in true producing archive")
    return data
