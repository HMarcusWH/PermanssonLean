"""Fail-closed detached replay of an actual full-scope candidate seal.

This re-opens real ZIP bytes and the original sidecar. It is not an
independently authenticated GitHub check, review or release approval.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys
import zipfile
from seal_approved import verify_approved_archive, SealError, ROOT as ROOT_DIR
from pr113_boundary_io import strict_json_object, detached_destination

FORMAT = "Permansson.MathClosure.PostsealReplayCandidate.v1"
# Intake must be bounded *before* z.read("approved_seal.json"). The full
# independently implemented archive verifier runs afterward.
MAX_ARCHIVE_BYTES = 64 * 1024 * 1024
MAX_MANIFEST_BYTES = 2 * 1024 * 1024

def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()

def no_symlink_input(raw: Path, *, exists: bool) -> Path:
    """Check each unresolved path component before any symlink resolution."""
    return detached_destination(raw, ROOT_DIR, must_exist=exists)


def replay(archive: Path, sidecar: Path, output: Path) -> dict:
    archive = no_symlink_input(archive, exists=True)
    sidecar = no_symlink_input(sidecar, exists=True)
    output = no_symlink_input(output, exists=False)
    if (output.exists() or output.is_relative_to(archive.parent) or
            output.is_relative_to(ROOT_DIR)):
        raise SealError("replay output must be new and detached from source/candidate")
    if archive.stat().st_size > MAX_ARCHIVE_BYTES:
        raise SealError("unbounded candidate archive before seal intake")
    with zipfile.ZipFile(archive) as z:
        matching = [info for info in z.infolist()
                    if info.filename.casefold() == "approved_seal.json"]
        if len(matching) != 1 or matching[0].filename != "approved_seal.json":
            raise SealError("missing, duplicated or case-colliding seal member")
        info = matching[0]
        if (info.is_dir() or (info.flag_bits & 1) or
            info.file_size <= 0 or info.file_size > MAX_MANIFEST_BYTES or
            info.compress_size <= 0 or info.file_size > 300 * info.compress_size):
            raise SealError("unbounded or unsafe original seal member")
        with z.open(info) as reader:
            seal_bytes = reader.read(MAX_MANIFEST_BYTES + 1)
        if len(seal_bytes) != info.file_size:
            raise SealError("partial or overexpanded seal member")
        manifest = strict_json_object(seal_bytes, max_bytes=MAX_MANIFEST_BYTES)
    if (manifest.get("format") != "Permansson.MathClosure.CandidateSeal.v2" or
        manifest.get("status") != "CANDIDATE_SEAL_BUILT" or
        manifest.get("full45_claimed") is not True or
        manifest.get("accepted_case_count") != 45 or
        manifest.get("accepted_claim_count") != 11):
        raise SealError("full 45/11 preseal candidate not present")
    verify_approved_archive(archive, manifest)
    raw = archive.read_bytes()
    expected = (sha(raw) + "  " + archive.name + "\n" +
                sha(seal_bytes) + "  approved_seal.json\n")
    if sidecar.read_text(encoding="utf-8") != expected:
        raise SealError("actual archive and detached checksums disagree")
    result = {
        "format": FORMAT,
        "status": "CANDIDATE_ARCHIVE_REPLAYED_UNREVIEWED",
        "source_commit_sha": manifest["source_commit_sha"],
        "head_sha": manifest["head_sha"],
        "pdf_sha256": manifest["pdf_sha256"],
        "archive_sha256": sha(raw),
        "manifest_sha256": sha(seal_bytes),
        "complete_original_members_verified": True,
        "authenticated_ci_artifact": False,
        "independent_review": False,
        "full_release_approved": False,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8") as writer:
        writer.write(json.dumps(result, sort_keys=True, indent=2) + "\n")
    return result

def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--archive", required=True, type=Path)
    p.add_argument("--sidecar", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args(argv)
    try:
        print(json.dumps(replay(args.archive, args.sidecar, args.output),
                         sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError, zipfile.BadZipFile) as exc:
        print("POSTSEAL REPLAY BLOCKED:", exc, file=sys.stderr)
        return 2

if __name__ == "__main__":
    raise SystemExit(main())
