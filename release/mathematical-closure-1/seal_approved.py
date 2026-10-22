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
from final_closure_full_contract import ORIGINAL_CLAIMS
from archive_integrity import SOURCE_FILES

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
         evidence_bundle: Path, output: Path, *, full: bool = False):
    if output.resolve().is_relative_to(ROOT.resolve()):
        raise SealError("release archive output must be detached from checkout")
    if output.resolve().is_relative_to(draft_directory.resolve()):
        raise SealError("approved output cannot overwrite its draft sources")
    # Baseline source integrity is always checked, even before authenticity.
    draft_verifier.verify(draft_directory / "manifest.lock.json")
    draft, pages = prepare_approved_manifest(draft_directory, approved)
    accepted_scope = "full-release-strict" if full else "scoped-release-strict"
    result = strict_acceptance(receipts, accepted_scope, approved,
                               bundle_path=evidence_bundle)
    if full and (set(approved.get("claims", [])) != ORIGINAL_CLAIMS or
                 approved.get("approved_manuscript_claims") !=
                 approved.get("claims")):
        raise SealError("full seal must explicitly approve all original eleven claims")
    if full and (result.get("accepted_case_count") != 45 or
                 result.get("accepted_claim_count") != 11 or
                 result.get("status") !=
                     "FULL_MATHEMATICAL_CLOSURE_RELEASE_READY"):
        raise SealError("full-release seal lacks the exact effective 45+11 certificate")
    if draft.get("source_commit_sha") != result["source"]:
        raise SealError("PDF was not built from genuine merged commit M")
    # Complete source files are included in the *approved* artifact too.
    # A detached reviewer must be able to reconstruct the candidate from
    # the released archive without accessing the operator's checkout.
    src_zip = draft_directory/"Permansson_Mathematical_Closure_E2E.zip"
    if not src_zip.is_file():
        raise SealError("original 13-source draft archive missing")
    complete_sources = {}
    with zipfile.ZipFile(src_zip) as draft_zip:
        for relative in SOURCE_FILES:
            original = "research_papers/mathematical_closure/" + relative
            name = "manuscript/" + relative
            expected = draft.get("source_tree_files", {}).get(original)
            if not isinstance(expected, str):
                raise SealError("draft omitted source input " + relative)
            raw = draft_zip.read(name)
            if sha(raw) != expected:
                raise SealError("draft source hash does not match " + relative)
            complete_sources[name] = raw
    original_ci = (draft_directory/"source_ci_receipts.lock.json").read_bytes()
    original_log = (draft_directory/"latex_build.log").read_bytes()
    original_sums = (draft_directory/"SHA256SUMS.txt").read_bytes()
    if sha(original_log) != draft.get("latex_log_sha256"):
        raise SealError("draft compiler log changed before sealing")
    manifest = {
        "format": "Permansson.MathClosure.ApprovedSeal.v2",
        "status": "APPROVED_SOURCE_BOUND",
        "source_commit_sha": result["source"],
        "head_sha": result["frozen_head"],
        "draft_manifest_sha256": sha(
            (draft_directory/"manifest.lock.json").read_bytes()),
        "manuscript_sources": draft["source_tree_files"],
        "original_draft_archive_sha256": sha(src_zip.read_bytes()),
        "original_draft_ci_sha256": sha(original_ci),
        "original_draft_log_sha256": sha(original_log),
        "original_draft_checksums_sha256": sha(original_sums),
        "pdf_sha256": draft["pdf_sha256"],
        "pdf_pages": pages,
        "claims": approved["claims"],
        "scientific_limitations": approved["scientific_limitations"],
        "empirical_identification_status": "NOT_ESTABLISHED",
        "review_binding": "AUTHENTICATED_LIVE_EXACT_H_SOURCE_AND_POSTMERGE_SCHOLARLY",
        "accepted_case_count": result["accepted_case_count"],
        "accepted_claim_count": result["accepted_claim_count"],
        "full45_claimed": full,
    }
    output.mkdir(parents=True, exist_ok=True)
    members = {
        "Permansson_Mathematical_Closure.pdf":
            (draft_directory/"Permansson_Mathematical_Closure.pdf").read_bytes(),
        "Permansson_Mathematical_Closure.tex":
            (draft_directory/"Permansson_Mathematical_Closure.tex").read_bytes(),
        "original_draft_manifest.lock.json":
            (draft_directory/"manifest.lock.json").read_bytes(),
        "original_draft_E2E.zip": src_zip.read_bytes(),
        "original_draft_source_ci_receipts.lock.json": original_ci,
        "original_draft_latex_build.log": original_log,
        "original_draft_SHA256SUMS.txt": original_sums,
        "approved_claims_manifest.json":
            (json.dumps(approved, indent=2, sort_keys=True)+"\n").encode(),
        "approved_seal.json":
            (json.dumps(manifest, indent=2, sort_keys=True)+"\n").encode(),
    }
    members.update(complete_sources)
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
            "original_draft_E2E.zip",
            "original_draft_source_ci_receipts.lock.json",
            "original_draft_latex_build.log",
            "original_draft_SHA256SUMS.txt",
            "approved_claims_manifest.json", "approved_seal.json",
            *["manuscript/" + source for source in SOURCE_FILES],
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
        source_index = manifest.get("manuscript_sources")
        if not isinstance(source_index, dict) or len(source_index) != len(SOURCE_FILES):
            raise SealError("approved seal lost canonical 13-source index")
        for path in SOURCE_FILES:
            name = "research_papers/mathematical_closure/" + path
            expected_sha = source_index.get(name)
            if not isinstance(expected_sha, str) or sha(
                z.read("manuscript/" + path)) != expected_sha:
                raise SealError("approved seal replaced manuscript: " + path)
        originals = {
            "original_draft_E2E.zip": "original_draft_archive_sha256",
            "original_draft_source_ci_receipts.lock.json": "original_draft_ci_sha256",
            "original_draft_latex_build.log": "original_draft_log_sha256",
            "original_draft_SHA256SUMS.txt": "original_draft_checksums_sha256",
            "original_draft_manifest.lock.json": "draft_manifest_sha256",
        }
        for name, field in originals.items():
            if sha(z.read(name)) != manifest.get(field):
                raise SealError("approved archive replaced provenance bytes: " + name)
        # A second complete retained copy must independently agree with all
        # direct source members. Neither source set may disappear silently.
        import io
        with zipfile.ZipFile(io.BytesIO(z.read("original_draft_E2E.zip"))) as inner:
            expected_inner = {"manuscript/" + p for p in SOURCE_FILES}
            expected_inner.update({
                "Permansson_Mathematical_Closure.pdf",
                "Permansson_Mathematical_Closure.tex",
                "manifest.lock.json", "source_ci_receipts.lock.json",
                "latex_build.log",
            })
            if set(inner.namelist()) != expected_inner or len(inner.namelist()) != len(expected_inner):
                raise SealError("nested original draft archive is incomplete")
            for path in SOURCE_FILES:
                name = "manuscript/" + path
                if inner.read(name) != z.read(name):
                    raise SealError("nested/detached manuscript bytes diverged: " + path)
            if inner.read("Permansson_Mathematical_Closure.pdf") != z.read(
                    "Permansson_Mathematical_Closure.pdf"):
                raise SealError("approved PDF differs from exact draft PDF")
            if inner.read("Permansson_Mathematical_Closure.tex") != z.read(
                    "Permansson_Mathematical_Closure.tex"):
                raise SealError("approved TeX differs from original draft")
            if inner.read("manifest.lock.json") != z.read(
                    "original_draft_manifest.lock.json"):
                raise SealError("nested draft manifest changed")
            if inner.read("source_ci_receipts.lock.json") != z.read(
                    "original_draft_source_ci_receipts.lock.json"):
                raise SealError("nested draft source CI receipts changed")
            if inner.read("latex_build.log") != z.read(
                    "original_draft_latex_build.log"):
                raise SealError("nested draft compiler log changed")
    return True


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--draft-dir", required=True, type=Path)
    ap.add_argument("--approved-claim-manifest", required=True, type=Path)
    ap.add_argument("--source-receipts", required=True, type=Path)
    ap.add_argument("--bundle", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--full", action="store_true",
                    help="require the complete full-release-strict certificate")
    args = ap.parse_args(argv)
    try:
        approved = json.loads(args.approved_claim_manifest.read_text())
        receipts = json.loads(args.source_receipts.read_text())
        outcome = seal(args.draft_dir, approved, receipts,
                       args.bundle, args.out, full=args.full)
    except (OSError, ValueError, KeyError, zipfile.BadZipFile) as exc:
        print("APPROVED SEAL BLOCKED:", exc)
        return 2
    print(json.dumps(outcome, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
