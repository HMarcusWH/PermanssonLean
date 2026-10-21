"""Only externally authenticated postmerge case/claim and PDF approvals seal an archive.

This never relabels the earlier DRAFT manifest. Approval requires:
real ordered Git merge M, integrated CI, detached source+mutation receipts,
reviewed claim scope and genuinely non-author scholarly/page-byte signoff.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verification/research"))
from final_closure_verify import strict as strict_acceptance

THIS = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("permansson_draft_verifier",
                                              THIS / "verify_release.py")
draft_verifier = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(draft_verifier)


class SealError(ValueError):
    pass


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def render_page_digests(directory: Path, expected_count: int):
    directory = directory / "pages"
    if not directory.is_dir():
        raise SealError("all draft PDF pages must be rendered")
    pages = sorted(p for p in directory.iterdir() if p.suffix == ".png")
    if not pages or expected_count != len(pages):
        raise SealError("missing or extra draft PDF rendered page")
    if any(p.is_symlink() or not p.is_file() or
           not p.name.startswith("page-") for p in pages):
        raise SealError("unsafe rendered page record")
    return {p.name: sha(p.read_bytes()) for p in pages}


def prepare_approved_manifest(draft_directory: Path, approved: dict):
    draft = json.loads((draft_directory / "manifest.lock.json").read_text())
    if draft.get("status") != "DRAFT_NOT_ACCEPTED" or draft.get("mode") != "DRAFT":
        raise SealError("input must be the genuine untouched draft artifact")
    sha_pdf = sha((draft_directory/"Permansson_Mathematical_Closure.pdf").read_bytes())
    if draft["pdf_sha256"] != sha_pdf or approved.get("pdf_sha256") != sha_pdf:
        raise SealError("reviewed PDF bytes differ from actual draft")
    if approved.get("source_commit_sha") != draft.get("source_commit_sha"):
        raise SealError("draft source is not approved merged main")
    pages = render_page_digests(draft_directory, draft["pdf_page_count"])
    if approved.get("pdf_pages") != pages:
        raise SealError("reviewed rendered page digests differ from PDF")
    if approved.get("status") != "APPROVED_SOURCE_BOUND":
        raise SealError("external approved claim manifest absent")
    return draft, pages


def seal(draft_directory: Path, approved: dict, receipts: dict,
         evidence_bundle: Path, output: Path):
    if output.resolve().is_relative_to(ROOT.resolve()):
        raise SealError("release archive output must be detached from checkout")
    if output.resolve().is_relative_to(draft_directory.resolve()):
        raise SealError("approved output cannot overwrite its draft sources")
    # Baseline source integrity is always checked, even before authenticity.
    draft_verifier.verify(draft_directory / "manifest.lock.json")
    draft, pages = prepare_approved_manifest(draft_directory, approved)
    result = strict_acceptance(receipts, "scoped-release-strict", approved,
                               bundle_path=evidence_bundle)
    if draft.get("source_commit_sha") != result["source"]:
        raise SealError("PDF was not built from genuine merged commit M")
    manifest = {
        "format": "Permansson.MathClosure.ApprovedSeal.v2",
        "status": "APPROVED_SOURCE_BOUND",
        "source_commit_sha": result["source"],
        "head_sha": result["frozen_head"],
        "draft_manifest_sha256": sha(
            (draft_directory/"manifest.lock.json").read_bytes()),
        "pdf_sha256": draft["pdf_sha256"],
        "pdf_pages": pages,
        "claims": approved["claims"],
        "scientific_limitations": approved["scientific_limitations"],
        "empirical_identification_status": "NOT_ESTABLISHED",
        "review_binding": "AUTHENTICATED_LIVE_EXACT_H_SOURCE_AND_POSTMERGE_SCHOLARLY",
        "accepted_case_count": result["accepted_case_count"],
        "accepted_claim_count": result["accepted_claim_count"],
        "full45_claimed": False,
    }
    output.mkdir(parents=True, exist_ok=True)
    members = {
        "Permansson_Mathematical_Closure.pdf":
            (draft_directory/"Permansson_Mathematical_Closure.pdf").read_bytes(),
        "Permansson_Mathematical_Closure.tex":
            (draft_directory/"Permansson_Mathematical_Closure.tex").read_bytes(),
        "original_draft_manifest.lock.json":
            (draft_directory/"manifest.lock.json").read_bytes(),
        "approved_claims_manifest.json":
            (json.dumps(approved, indent=2, sort_keys=True)+"\n").encode(),
        "approved_seal.json":
            (json.dumps(manifest, indent=2, sort_keys=True)+"\n").encode(),
    }
    for page in pages:
        members["pages/" + page] = (draft_directory/"pages"/page).read_bytes()
    archive = output/"Permansson_Mathematical_Closure_APPROVED.zip"
    with zipfile.ZipFile(archive, "w") as zipout:
        for name, payload in sorted(members.items()):
            entry = zipfile.ZipInfo(name, (1980,1,1,0,0,0))
            entry.external_attr = 0o100644 << 16
            entry.compress_type = zipfile.ZIP_DEFLATED
            zipout.writestr(entry, payload, compress_type=zipfile.ZIP_DEFLATED,
                            compresslevel=9)
    (output/"approved_seal.json").write_bytes(members["approved_seal.json"])
    (output/"SHA256SUMS.txt").write_text(
        sha(archive.read_bytes()) + "  " + archive.name + "\n" +
        sha(members["approved_seal.json"]) + "  approved_seal.json\n")
    verify_approved_archive(archive, manifest)
    return {"status": manifest["status"], "source": manifest["source_commit_sha"],
            "approved_pdf_sha256": manifest["pdf_sha256"],
            "archive_sha256": sha(archive.read_bytes())}


def verify_approved_archive(archive: Path, manifest: dict):
    if not archive.is_file():
        raise SealError("approved archive missing")
    with zipfile.ZipFile(archive) as z:
        if z.testzip() is not None:
            raise SealError("approved archive CRC mismatch")
        names = z.namelist()
        expected = {
            "Permansson_Mathematical_Closure.pdf",
            "Permansson_Mathematical_Closure.tex",
            "original_draft_manifest.lock.json",
            "approved_claims_manifest.json", "approved_seal.json",
            *["pages/" + p for p in manifest["pdf_pages"]],
        }
        if len(names) != len(expected) or set(names) != expected:
            raise SealError("approved archive has extra/missing members")
        if sha(z.read("Permansson_Mathematical_Closure.pdf")) != manifest["pdf_sha256"]:
            raise SealError("approved archive replaced PDF")
        for page, expected_sha in manifest["pdf_pages"].items():
            if sha(z.read("pages/"+page)) != expected_sha:
                raise SealError("approved page bytes changed")
        if json.loads(z.read("approved_seal.json")) != manifest:
            raise SealError("approved source metadata changed")
    return True


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--draft-dir", required=True, type=Path)
    ap.add_argument("--approved-claim-manifest", required=True, type=Path)
    ap.add_argument("--source-receipts", required=True, type=Path)
    ap.add_argument("--bundle", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args(argv)
    try:
        approved = json.loads(args.approved_claim_manifest.read_text())
        receipts = json.loads(args.source_receipts.read_text())
        outcome = seal(args.draft_dir, approved, receipts,
                       args.bundle, args.out)
    except (OSError, ValueError, KeyError, zipfile.BadZipFile) as exc:
        print("APPROVED SEAL BLOCKED:", exc)
        return 2
    print(json.dumps(outcome, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
