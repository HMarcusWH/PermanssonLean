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
import stat
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verification/research"))
from final_closure_verify import strict as strict_acceptance
from final_closure_full_contract import ORIGINAL_CLAIMS
from archive_integrity import SOURCE_FILES
from pr113_boundary_io import strict_json_object, detached_destination

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
    draft = strict_json_object((draft_directory / "manifest.lock.json").read_bytes())
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



def external_evidence_children(reproduction_attachment, v31_attachment):
    """Retain unmodified full-scope reproduction and all 76 owner inputs."""
    if not isinstance(reproduction_attachment, dict) or not isinstance(v31_attachment, dict):
        raise SealError("full seal requires original reproduction and owner evidence")
    source_files = {
        "external/reproduction.zip": reproduction_attachment.get("zip_file"),
        "external/additional_contract.json": v31_attachment.get("additional_contract"),
        "external/workflow_blob_candidates.json": v31_attachment.get("workflow_blob_candidates"),
    }
    identities = reproduction_attachment.get("identities")
    if not isinstance(identities, dict):
        raise SealError("original reproduction identities missing")
    children = {
        "external/reproduction_ids.json":
            (json.dumps(identities, indent=2, sort_keys=True) + "\n").encode(),
    }
    for key, file in source_files.items():
        if file is None:
            raise SealError("missing full-scope source " + key)
        p = Path(file)
        if not p.is_file() or p.is_symlink() or not 0 < p.stat().st_size <= 64*1024*1024:
            raise SealError("external input missing, oversized or symlinked")
        children[key] = p.read_bytes()
    directory = v31_attachment.get("additional_zips")
    if directory is None or not Path(directory).is_dir() or Path(directory).is_symlink():
        raise SealError("missing original 76-owner directory")
    files = list(Path(directory).iterdir())
    if len(files) != 76:
        raise SealError("full-scope original owners must number 76")
    import re
    total = 0
    for p in files:
        if (not p.is_file() or p.is_symlink()
                or not re.fullmatch(r"[1-9][0-9]*\.zip", p.name)
                or not 0 < p.stat().st_size <= 64*1024*1024):
            raise SealError("invalid original owner artifact")
        total += p.stat().st_size
        if total > 256*1024*1024:
            raise SealError("original owner ZIP budget exceeded")
        children["external/owners/" + p.name] = p.read_bytes()
    return children


def bounded_zip_members(z, expected, *, total_limit, member_limit):
    """Validate ZIP directory and budgets before any decompression."""
    infos = z.infolist()
    if len(infos) != len(expected) or len(infos) > 256:
        raise SealError("wrong ZIP member count")
    seen = set()
    total = 0
    for entry in infos:
        name = entry.filename
        mode = entry.external_attr >> 16
        if (name not in expected or name.casefold() in seen
                or name.startswith("/") or "\\" in name or
                any(x in ("", ".", "..") for x in name.split("/"))
                or entry.is_dir() or entry.flag_bits & 1
                or (mode != 0 and not stat.S_ISREG(mode))
                or entry.file_size > member_limit or entry.compress_size <= 0
                or entry.file_size > max(entry.compress_size*500, 1024*1024)):
            raise SealError("unsafe/duplicate/overexpanded ZIP member")
        seen.add(name.casefold())
        total += entry.file_size
        if total > total_limit:
            raise SealError("excess nested ZIP expansion")
    if {x.filename for x in infos} != set(expected):
        raise SealError("missing expected ZIP member")


def read_bounded(z, name, max_bytes):
    info = z.getinfo(name)
    if info.file_size > max_bytes:
        raise SealError("oversized ZIP member: " + name)
    with z.open(info) as reader:
        value = reader.read(max_bytes + 1)
    if len(value) != info.file_size:
        raise SealError("incomplete ZIP member: " + name)
    return value


def seal(draft_directory: Path, approved: dict, receipts: dict,
         evidence_bundle: Path, output: Path, *, full: bool = False,
         reproduction_attachment: dict | None = None,
         v31_attachment: dict | None = None):
    output = detached_destination(output, ROOT, forbidden=(draft_directory,))
    # Baseline source integrity is always checked, even before authenticity.
    draft_verifier.verify(draft_directory / "manifest.lock.json")
    draft, pages = prepare_approved_manifest(draft_directory, approved)
    accepted_scope = "postmerge-preseal-strict" if full else "scoped-release-strict"
    authentic_input = ({"reproduction_attachment": reproduction_attachment}
                       if reproduction_attachment is not None else {})
    if v31_attachment is not None:
        authentic_input["v31_attachment"] = v31_attachment
    result = strict_acceptance(receipts, accepted_scope, approved,
                               bundle_path=evidence_bundle,
                               **authentic_input)
    if full and (set(approved.get("claims", [])) != ORIGINAL_CLAIMS or
                 approved.get("approved_manuscript_claims") !=
                 approved.get("claims")):
        raise SealError("full seal must explicitly approve all original eleven claims")
    if full and (result.get("accepted_case_count") != 45 or
                 result.get("accepted_claim_count") != 11 or
                 result.get("status") !=
                     "POSTMERGE_PRESEAL_READY"):
        raise SealError("candidate seal lacks authenticated preseal 45/11 certificate")
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
        expected_inner = {"manuscript/" + path for path in SOURCE_FILES}
        expected_inner.update({"Permansson_Mathematical_Closure.pdf",
                               "Permansson_Mathematical_Closure.tex",
                               "manifest.lock.json", "source_ci_receipts.lock.json",
                               "latex_build.log"})
        bounded_zip_members(draft_zip, expected_inner,
                            total_limit=128*1024*1024, member_limit=48*1024*1024)
        for relative in SOURCE_FILES:
            original = "research_papers/mathematical_closure/" + relative
            name = "manuscript/" + relative
            expected = draft.get("source_tree_files", {}).get(original)
            if not isinstance(expected, str):
                raise SealError("draft omitted source input " + relative)
            raw = read_bounded(draft_zip, name, 48*1024*1024)
            if sha(raw) != expected:
                raise SealError("draft source hash does not match " + relative)
            complete_sources[name] = raw
    original_ci = (draft_directory/"source_ci_receipts.lock.json").read_bytes()
    original_log = (draft_directory/"latex_build.log").read_bytes()
    original_sums = (draft_directory/"SHA256SUMS.txt").read_bytes()
    if not evidence_bundle.is_file() or evidence_bundle.is_symlink():
        raise SealError("authenticated detached proof/mutation evidence bundle unavailable")
    retained_bundle = evidence_bundle.read_bytes()
    if not retained_bundle or len(retained_bundle) > 32*1024*1024:
        raise SealError("detached proof/mutation bundle missing or oversized")
    retained_receipts = (json.dumps(
        receipts, indent=2, sort_keys=True, ensure_ascii=False)+"\n").encode("utf-8")
    original_case_map = (ROOT/"research/paper_closures/post_merge_112/acceptance_case_source_map.json").read_bytes()
    original_claim_map = (ROOT/"research/paper_closures/post_merge_112/claim_declaration_map.json").read_bytes()
    effective_report = (json.dumps({
        "scope": accepted_scope, "frozen_head": result["frozen_head"],
        "merged_source": result["source"],
        "accepted_cases": result.get("effective_cases", {}),
        "accepted_claims": result.get("effective_claims", []),
        "accepted_case_count": result["accepted_case_count"],
        "accepted_claim_count": result["accepted_claim_count"],
        "receipt_contract": result.get("receipt_contract"),
        "status": result.get("status", "SCOPED_SOURCE_ONLY")
    }, indent=2, sort_keys=True)+"\n").encode("utf-8")
    if sha(retained_bundle) != receipts.get("evidence_bundle_sha256"):
        raise SealError("retained original proof bundle differs from strict acceptance")
    if sha(original_log) != draft.get("latex_log_sha256"):
        raise SealError("draft compiler log changed before sealing")
    approved_bytes = (json.dumps(approved, indent=2, sort_keys=True)+"\n").encode()
    children = (external_evidence_children(reproduction_attachment, v31_attachment)
                if full else {})
    manifest = {
        "format": ("Permansson.MathClosure.CandidateSeal.v2" if full
                   else "Permansson.MathClosure.ApprovedSeal.v3"),
        "status": "CANDIDATE_SEAL_BUILT" if full else "APPROVED_SOURCE_BOUND",
        "source_commit_sha": result["source"],
        "head_sha": result["frozen_head"],
        "draft_manifest_sha256": sha(
            (draft_directory/"manifest.lock.json").read_bytes()),
        "manuscript_sources": draft["source_tree_files"],
        "original_draft_archive_sha256": sha(src_zip.read_bytes()),
        "original_draft_ci_sha256": sha(original_ci),
        "original_draft_log_sha256": sha(original_log),
        "original_draft_checksums_sha256": sha(original_sums),
        "evidence_bundle_sha256": sha(retained_bundle),
        "source_receipts_sha256": sha(retained_receipts),
        "approved_claims_manifest_sha256": sha(approved_bytes),
        "external_evidence_members":
            {key: sha(data) for key, data in sorted(children.items())},
        "original_case_map_sha256": sha(original_case_map),
        "original_claim_map_sha256": sha(original_claim_map),
        "effective_acceptance_report_sha256": sha(effective_report),
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
    if output.exists():
        raise SealError("output must be a fresh detached directory")
    output.mkdir(parents=True, exist_ok=False)
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
        "detached_proof_mutation_bundle.zip": retained_bundle,
        "source_acceptance_receipts.json": retained_receipts,
        "original_case_acceptance_map.json": original_case_map,
        "original_claim_declaration_map.json": original_claim_map,
        "effective_acceptance_report.json": effective_report,
        "approved_claims_manifest.json": approved_bytes,
        "approved_seal.json":
            (json.dumps(manifest, indent=2, sort_keys=True)+"\n").encode(),
    }
    members.update(complete_sources)
    members.update(children)
    for page in pages:
        members["pages/" + page] = (draft_directory/"pages"/page).read_bytes()
    archive = output / ("Permansson_Mathematical_Closure_CANDIDATE.zip"
                        if full else "Permansson_Mathematical_Closure_APPROVED.zip")
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
    if archive.is_symlink() or archive.stat().st_size > 64*1024*1024:
        raise SealError("approved ZIP path or size unsafe")
    with zipfile.ZipFile(archive) as z:
        infos = z.infolist()
        if len(infos) > 256 or sum(i.file_size for i in infos) > 512*1024*1024:
            raise SealError("approved ZIP expanded member bound exceeded")
        seen = set()
        for info in infos:
            mode = info.external_attr >> 16
            low = info.filename.casefold()
            if (low in seen or
                info.filename.startswith("/") or
                ".." in info.filename.split("/") or
                "\\" in info.filename or
                (mode != 0 and not stat.S_ISREG(mode)) or
                info.is_dir() or
                info.file_size > 64*1024*1024 or
                info.flag_bits & 1):
                raise SealError("unsafe or nonportable approved ZIP member")
            seen.add(low)
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
            "detached_proof_mutation_bundle.zip",
            "source_acceptance_receipts.json",
            "original_case_acceptance_map.json",
            "original_claim_declaration_map.json",
            "effective_acceptance_report.json",
            "approved_claims_manifest.json", "approved_seal.json",
            *["manuscript/" + source for source in SOURCE_FILES],
            *["pages/" + p for p in manifest["pdf_pages"]],
        }
        extra = manifest.get("external_evidence_members")
        if not isinstance(extra, dict):
            raise SealError("missing versioned evidence inventory")
        if manifest.get("format") == "Permansson.MathClosure.CandidateSeal.v2":
            if (len(extra) != 80 or
                {n for n in extra if n.startswith("external/owners/")} !=
                {n for n in extra if n.startswith("external/owners/") and n.endswith(".zip")} or
                len([n for n in extra if n.startswith("external/owners/")]) != 76 or
                not {"external/reproduction.zip", "external/reproduction_ids.json",
                     "external/additional_contract.json",
                     "external/workflow_blob_candidates.json"} <= set(extra)):
                raise SealError("full original evidence closure incomplete")
        elif manifest.get("format") == "Permansson.MathClosure.ApprovedSeal.v3":
            if extra:
                raise SealError("scoped release cannot assert full owner evidence")
        else:
            raise SealError("obsolete or unknown seal format")
        expected.update(extra)
        if len(names) != len(expected) or set(names) != expected:
            raise SealError("approved archive has extra/missing members")
        for child, digest in extra.items():
            if not isinstance(digest, str) or sha(read_bounded(z, child, 64*1024*1024)) != digest:
                raise SealError("original full evidence bytes changed: " + child)
        approved_bytes = read_bounded(z, "approved_claims_manifest.json", 4*1024*1024)
        if sha(approved_bytes) != manifest.get("approved_claims_manifest_sha256"):
            raise SealError("approved claims bytes not bound by seal")
        approved = strict_json_object(approved_bytes)
        if (approved.get("status") != "APPROVED_SOURCE_BOUND"
                or approved.get("source_commit_sha") != manifest.get("source_commit_sha")
                or approved.get("pdf_sha256") != manifest.get("pdf_sha256")
                or approved.get("pdf_pages") != manifest.get("pdf_pages")
                or approved.get("claims") != manifest.get("claims")):
            raise SealError("approved claims contradict sealed review/source")
        if manifest.get("full45_claimed") is True and (
                approved.get("approved_manuscript_claims") != manifest.get("claims")):
            raise SealError("full paper claims differ from approved claim list")
        if sha(z.read("Permansson_Mathematical_Closure.pdf")) != manifest["pdf_sha256"]:
            raise SealError("approved archive replaced PDF")
        for page, expected_sha in manifest["pdf_pages"].items():
            if sha(z.read("pages/"+page)) != expected_sha:
                raise SealError("approved page bytes changed")
        if strict_json_object(z.read("approved_seal.json")) != manifest:
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
        originals.update({
            "detached_proof_mutation_bundle.zip": "evidence_bundle_sha256",
            "source_acceptance_receipts.json": "source_receipts_sha256",
            "original_case_acceptance_map.json": "original_case_map_sha256",
            "original_claim_declaration_map.json": "original_claim_map_sha256",
            "effective_acceptance_report.json": "effective_acceptance_report_sha256",
        })
        for name, field in originals.items():
            if sha(z.read(name)) != manifest.get(field):
                raise SealError("approved archive replaced provenance bytes: " + name)
        bound_receipts = strict_json_object(z.read("source_acceptance_receipts.json"))
        if bound_receipts.get("evidence_bundle_sha256") != manifest["evidence_bundle_sha256"]:
            raise SealError("detached compiler bundle no longer matches reviewed receipts")
        effective = strict_json_object(z.read("effective_acceptance_report.json"))
        if (effective.get("frozen_head") != manifest["head_sha"] or
            effective.get("merged_source") != manifest["source_commit_sha"] or
            effective.get("accepted_case_count") != manifest["accepted_case_count"] or
            effective.get("accepted_claim_count") != manifest["accepted_claim_count"] or
            manifest.get("full45_claimed") is True and
            (effective.get("receipt_contract") != "ALL_45_HISTORICAL_AND_ALL_11_COMPLETE" or
             effective.get("status") != (
                 "POSTMERGE_PRESEAL_READY"
                 if manifest.get("status") == "CANDIDATE_SEAL_BUILT"
                 else "FULL_MATHEMATICAL_CLOSURE_RELEASE_READY"))):
            raise SealError("effective acceptance receipt contradicts approved seal")
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
            bounded_zip_members(inner, expected_inner,
                                total_limit=128*1024*1024, member_limit=48*1024*1024)
            for path in SOURCE_FILES:
                name = "manuscript/" + path
                if read_bounded(inner, name, 48*1024*1024) != z.read(name):
                    raise SealError("nested/detached manuscript bytes diverged: " + path)
            if read_bounded(inner, "Permansson_Mathematical_Closure.pdf", 48*1024*1024) != z.read(
                    "Permansson_Mathematical_Closure.pdf"):
                raise SealError("approved PDF differs from exact draft PDF")
            if read_bounded(inner, "Permansson_Mathematical_Closure.tex", 48*1024*1024) != z.read(
                    "Permansson_Mathematical_Closure.tex"):
                raise SealError("approved TeX differs from original draft")
            if read_bounded(inner, "manifest.lock.json", 48*1024*1024) != z.read(
                    "original_draft_manifest.lock.json"):
                raise SealError("nested draft manifest changed")
            if read_bounded(inner, "source_ci_receipts.lock.json", 48*1024*1024) != z.read(
                    "original_draft_source_ci_receipts.lock.json"):
                raise SealError("nested draft source CI receipts changed")
            if read_bounded(inner, "latex_build.log", 48*1024*1024) != z.read(
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
                    help="require exact-M postmerge preseal 45/11 eligibility; candidate requires separate independent postseal review")
    ap.add_argument("--reproduction-zip", type=Path)
    ap.add_argument("--reproduction-ids", type=Path)
    ap.add_argument("--additional-contract", type=Path)
    ap.add_argument("--additional-zips", type=Path)
    ap.add_argument("--workflow-blob-candidates", type=Path)
    args = ap.parse_args(argv)
    try:
        approved = strict_json_object(args.approved_claim_manifest.read_bytes())
        receipts = strict_json_object(args.source_receipts.read_bytes())
        if bool(args.reproduction_zip) != bool(args.reproduction_ids):
            raise SealError("reproduction ZIP and real producing IDs required together")
        external = ({
            "zip_file": args.reproduction_zip,
            "identities": strict_json_object(args.reproduction_ids.read_bytes())}
            if args.reproduction_zip else None)
        extra_inputs = (args.additional_contract, args.additional_zips,
                        args.workflow_blob_candidates)
        if any(x is not None for x in extra_inputs) and not all(
                x is not None for x in extra_inputs):
            raise SealError(
                "additional source-control evidence requires all three "
                "contract, owner ZIP and workflow-source inputs")
        additional = ({
            "additional_contract": args.additional_contract,
            "additional_zips": args.additional_zips,
            "workflow_blob_candidates": args.workflow_blob_candidates}
            if all(x is not None for x in extra_inputs) else None)
        if args.full and additional is None:
            raise SealError("full candidate seal requires authenticated 76-owner v3.1 source inputs")
        outcome = seal(args.draft_dir, approved, receipts,
                       args.bundle, args.out, full=args.full,
                       reproduction_attachment=external,
                       v31_attachment=additional)
    except (OSError, ValueError, KeyError, zipfile.BadZipFile) as exc:
        print("APPROVED SEAL BLOCKED:", exc)
        return 2
    print(json.dumps(outcome, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
