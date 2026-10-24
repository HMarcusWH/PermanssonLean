"""Authenticate and unpack an untrusted exact-M preseal input carrier.

The input carrier is a transport, never mathematical or security approval:
the subsequent seal_approved --full path independently authenticates the
real 12/12 H/M CI, original 21 producer ZIPs, all 76 v3.1 controls,
nonauthor source/scholarly reviews, and exact merged-M reproduction.

A genuine GitHub artifact digest does NOT prove an accepted release.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import zipfile

SOURCE = Path(__file__).resolve().parents[2]
NAME = "pr113-preseal-review-inputs"
FORMAT = "Permansson.PR113.PresealInputCarrier.v1"
SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
ID = re.compile(r"^[1-9][0-9]*$")
EXPECTED_FILES = frozenset((
    "reviewed/approved_claim_manifest.json",
    "reviewed/source_receipts.json",
    "reviewed/evidence_bundle.zip",
    "reviewed/reproduction.zip",
    "reviewed/reproduction_ids.json",
    "reviewed/additional_contract.json",
    "reviewed/workflow_blob_candidates.json",
))
MAX_ZIP_BYTES = 256 * 1024 * 1024
MAX_MEMBER_BYTES = 64 * 1024 * 1024
MAX_TOTAL_UNCOMPRESSED = 320 * 1024 * 1024
MAX_MEMBERS = 100
CI_APP = "github-actions"


class PresealInputError(ValueError):
    pass


def demand(condition, reason):
    if not condition:
        raise PresealInputError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json_file(path):
    p = Path(path)
    demand(p.is_file() and not p.is_symlink(),
           "mandatory original GitHub API source JSON missing")
    raw = p.read_bytes()
    demand(0 < len(raw) <= 4*1024*1024, "invalid GitHub API response size")
    try:
        obj = json.loads(raw)
    except (UnicodeError, TypeError, ValueError) as exc:
        raise PresealInputError("GitHub API JSON invalid") from exc
    demand(isinstance(obj, dict), "GitHub API source is not an object")
    return obj


def verified_transport(*, merged, run_id, attempt, job_id, check_id,
                       artifact_id, meta, run, jobs, check, raw):
    """Authenticate real completed success + correct attempt + artifact bytes."""
    demand(isinstance(merged, str) and SHA40.fullmatch(merged),
           "exact real merged main M SHA missing")
    for label, number in (("run",run_id), ("attempt",attempt),
                          ("job",job_id), ("check",check_id),
                          ("artifact",artifact_id)):
        demand(type(number) is int and number > 0, "invalid numeric " + label)
    demand(isinstance(meta, dict) and isinstance(run, dict)
           and isinstance(jobs, dict) and isinstance(check, dict)
           and type(raw) is bytes and 0 < len(raw) <= MAX_ZIP_BYTES,
           "missing original preseal carrier and GH identity responses")
    demand(run.get("id") == run_id and
           run.get("head_sha") == merged and
           run.get("head_branch") == "main" and
           run.get("status") == "completed" and
           run.get("conclusion") == "success" and
           run.get("event") in ("push", "workflow_dispatch") and
           run.get("run_attempt") == attempt and
           isinstance(run.get("path"), str) and
           run["path"].endswith(".yml") and
           (run["path"].startswith(".github/workflows/") or
            "/.github/workflows/" in run["path"]),
           "review-input run is not successful exact-M GitHub Actions source")
    rows = jobs.get("jobs")
    demand(isinstance(rows, list), "successful original GitHub job inventory absent")
    selected = [j for j in rows if isinstance(j, dict)
                and j.get("id") == job_id]
    demand(len(selected) == 1, "review-input producing job ID missing/ambiguous")
    job = selected[0]
    demand(job.get("run_id") == run_id and
           job.get("run_attempt") == attempt and
           job.get("head_sha") == merged and
           job.get("status") == "completed" and
           job.get("conclusion") == "success" and
           str(job.get("check_run_url", "")).endswith(
               "/check-runs/" + str(check_id)),
           "review-input job not successful in the claimed run attempt")
    demand(check.get("id") == check_id and
           check.get("head_sha") == merged and
           check.get("name") == job.get("name") and
           check.get("status") == "completed" and
           check.get("conclusion") == "success" and
           (check.get("app") or {}).get("slug") == CI_APP,
           "review-input original check-run not authentic/successful")
    expected = "sha256:" + digest(raw)
    demand(meta.get("id") == artifact_id and
           meta.get("name") == NAME and
           meta.get("expired") is False and
           meta.get("digest") == expected and
           (meta.get("workflow_run") or {}).get("id") == run_id and
           (meta.get("workflow_run") or {}).get("head_sha") == merged,
           "review-input original GitHub artifact SHA/name/source mismatch")
    stamps = [job.get("started_at"), meta.get("created_at"),
              job.get("completed_at")]
    demand(all(isinstance(x, str) and
               re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", x)
               for x in stamps) and stamps[0] <= stamps[1] <= stamps[2],
           "input artifact not uploaded during successful exact attempt")
    return {
        "transport_run_id": run_id,
        "transport_run_attempt": attempt,
        "transport_job_id": job_id,
        "transport_check_run_id": check_id,
        "transport_artifact_id": artifact_id,
        "transport_artifact_sha256": digest(raw),
        "source_commit_sha": merged,
        "status": "TRANSPORT_BYTES_BOUND_NOT_APPROVED",
    }


def inspect_original_carrier(raw):
    """Reject paths, ZIP bombs, aliasing, unexpected files, unbounded entries."""
    demand(type(raw) is bytes and 0 < len(raw) <= MAX_ZIP_BYTES,
           "original preseal input ZIP missing/oversized")
    entries = {}
    seen = set()
    total = 0
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            infos = z.infolist()
            demand(len(infos) >= len(EXPECTED_FILES) + 1 and
                   len(infos) <= MAX_MEMBERS,
                   "preseal carrier lacks required evidence or has too many members")
            for info in infos:
                name = info.filename
                rel = PurePosixPath(name)
                mode = (info.external_attr >> 16) & 0o170000
                demand(isinstance(name, str) and
                       name == rel.as_posix() and
                       not rel.is_absolute() and
                       not info.is_dir() and
                       "\\" not in name and
                       ".." not in rel.parts and
                       not any(x in (".", "") for x in name.split("/")) and
                       mode in (0, stat.S_IFREG) and
                       name.casefold() not in seen,
                       "unsafe or duplicate original carrier member")
                allowed = name in EXPECTED_FILES
                if name.startswith("reviewed/additional_zips/") and name.endswith(".zip"):
                    stem = name[len("reviewed/additional_zips/"):-4]
                    allowed = bool(ID.fullmatch(stem))
                demand(allowed, "foreign/unapproved preseal input member")
                seen.add(name.casefold())
                demand(0 < info.file_size <= MAX_MEMBER_BYTES and
                       info.compress_size > 0 and
                       info.file_size <= 200 * info.compress_size,
                       "unbounded evidence input/ZIP compression ratio")
                total += info.file_size
                demand(total <= MAX_TOTAL_UNCOMPRESSED,
                       "aggregate evidence input exceeds bounded size")
            # Name aliasing (file/child) and all required original source files
            demand(EXPECTED_FILES <= set(x.filename for x in infos) and
                   any(x.filename.startswith("reviewed/additional_zips/")
                       for x in infos),
                   "full v3.1 reviewed producer inputs absent")
            for info in infos:
                with z.open(info) as handle:
                    content = handle.read(info.file_size + 1)
                demand(len(content) == info.file_size,
                       "original GH ZIP decompression length mismatch")
                entries[info.filename] = content
    except (OSError, RuntimeError, zipfile.BadZipFile, zipfile.LargeZipFile) as exc:
        raise PresealInputError("unreadable original GitHub review carrier ZIP") from exc
    return entries


def extract(artifact_zip, output, *, merged, run_id, attempt, job_id,
            check_id, artifact_id, meta, run, jobs, check):
    src = Path(artifact_zip).absolute()
    target = Path(output).absolute()
    demand(src.is_file() and not any(x.is_symlink() for x in (src, *src.parents))
           and not target.exists() and
           not any(x.is_symlink() for x in target.parents)
           and not target.is_relative_to(SOURCE.resolve()) and
           not SOURCE.resolve().is_relative_to(target),
           "original GH artifact/read-only target path invalid")
    raw = src.read_bytes()
    transport = verified_transport(
        merged=merged, run_id=run_id, attempt=attempt, job_id=job_id,
        check_id=check_id, artifact_id=artifact_id, meta=meta,
        run=run, jobs=jobs, check=check, raw=raw)
    contents = inspect_original_carrier(raw)
    target.mkdir(parents=True, exist_ok=False)
    members = {}
    for name, data in sorted(contents.items()):
        rel = name.removeprefix("reviewed/")
        path = target / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        members[rel] = digest(data)
    manifest = {
        "format": FORMAT,
        **transport,
        # The transport status must not replace the outer result contract.
        "status": "GH_SOURCE_TRANSPORT_VERIFIED__RELEASE_REVIEW_PENDING",
        "members_sha256": members,
        "independent_review": False,
        "mathematical_acceptance": False,
        "publication_authorized": False,
    }
    (target / "transport_diagnostics.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    return manifest


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--merged", required=True)
    for arg in ("run-id", "attempt", "job-id", "check-id", "artifact-id"):
        p.add_argument("--" + arg, type=int, required=True)
    for arg in ("zip", "metadata", "run", "jobs", "check", "out"):
        p.add_argument("--" + arg, type=Path, required=True)
    a = p.parse_args(argv)
    try:
        report = extract(
            a.zip, a.out, merged=a.merged, run_id=a.run_id,
            attempt=a.attempt, job_id=a.job_id, check_id=a.check_id,
            artifact_id=a.artifact_id, meta=read_json_file(a.metadata),
            run=read_json_file(a.run), jobs=read_json_file(a.jobs),
            check=read_json_file(a.check))
    except (PresealInputError, ValueError, KeyError, OSError, TypeError) as exc:
        print("PRESEAL REVIEW INPUT BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({"status": report["status"],
                      "source": report["source_commit_sha"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
