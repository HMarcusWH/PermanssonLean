"""Bounded source-bound verification of an existing two-root draft CI ZIP.

Read-only offline audit of actual draft bytes; not mathematical acceptance,
scholarly signoff, authentic live CI, or release authorization. This is
intentionally separate from the strict post-merge seal and from postseal replay.
"""
from __future__ import annotations
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import stat
import sys
import zipfile
from pathlib import PurePosixPath

from infrastructure_acceptance import inspect_zip

SOURCE_PATHS = frozenset([
    "README.md", "main.tex", "preamble.tex", "references.bib",
    "sections/01_scope_and_semantics.tex",
    "sections/02_existing_foundations.tex",
    "sections/03_discounted_original_margin.tex",
    "sections/04_measurable_multiagent_recovery.tex",
    "sections/05_nonlinear_occupation.tex",
    "sections/06_counterexamples_and_limits.tex",
    "sections/07_formal_verification.tex",
    "appendices/A_theorem_crosswalk.tex",
    "appendices/B_reproducibility.tex",
])
PREFIX = "research_papers/mathematical_closure/"
FORMAT = "Permansson.PR113.DraftByteRehearsal.v1"
SHA = re.compile(r"^[0-9a-f]{40}$")
HEX = re.compile(r"^[0-9a-f]{64}$")
ROOT = Path(__file__).resolve().parents[2]


class DraftRehearsalError(ValueError):
    pass


def need(ok, msg):
    if not ok:
        raise DraftRehearsalError(msg)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def jsonfile(files, name):
    need(name in files and 0 < len(files[name]) <= 1024*1024,
         "missing or excessive original draft receipt: "+name)
    try:
        data = json.loads(files[name])
    except (ValueError, TypeError) as exc:
        raise DraftRehearsalError("invalid original draft JSON: "+name) from exc
    need(isinstance(data, dict), "draft receipt must be JSON object")
    return data


def bounded_nested_archive(raw):
    """Reject inner archive bombs, symlinks, traversal and duplicate members."""
    need(type(raw) is bytes and 0 < len(raw) <= 64*1024*1024,
         "draft nested archive byte budget exceeded")
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            infos=z.infolist()
            need(1 <= len(infos) <= 100,
                 "nested draft ZIP member count unsafe")
            total=0
            seen=set()
            output={}
            for item in infos:
                name=item.filename
                path=PurePosixPath(name)
                mode=(item.external_attr >> 16) & 0o170000
                need(name==path.as_posix() and
                     not path.is_absolute() and
                     all(part not in ("", ".", "..") for part in name.split("/"))
                     and "\\" not in name and len(name) <= 300
                     and not item.is_dir() and mode in (0,stat.S_IFREG)
                     and name.casefold() not in seen and
                     0 < item.file_size <= 16*1024*1024
                     and item.compress_size > 0 and
                     item.file_size <= item.compress_size * 300 and
                     not (item.flag_bits & 1),
                     "nested draft ZIP member unsafe, duplicate or compressed bomb")
                seen.add(name.casefold())
                total+=item.file_size
                need(total <= 64*1024*1024,
                     "nested original manuscript expands beyond source limit")
                output[name]=z.read(item)
            need(z.testzip() is None,"nested original draft archive CRC invalid")
            return output
    except (OSError,RuntimeError,ValueError,zipfile.BadZipFile,
            zipfile.LargeZipFile) as exc:
        raise DraftRehearsalError("invalid actual nested draft ZIP") from exc


def audit(artifact_zip, head):
    need(isinstance(head, str) and SHA.fullmatch(head),
         "draft rehearsal needs exact Git H")
    files = inspect_zip(artifact_zip)
    ci = jsonfile(files,"ci_execution_identity.json")
    report = jsonfile(files,"reproduction_receipt.json")
    need(ci.get("status") == "EXECUTED_DRAFT_ONLY_NO_SCHOLARLY_REVIEW" and
         ci.get("format") == "Permansson.CICleanRebuildCandidate.v1" and
         ci.get("source_head") == head and
         ci.get("github_repository") == "HMarcusWH/PermanssonLean" and
         ci.get("github_job") == "clean-paper-rebuild" and
         type(ci.get("github_run_id")) is int and ci["github_run_id"] > 0 and
         type(ci.get("github_run_attempt")) is int and
         ci["github_run_attempt"] > 0 and
         ci.get("authenticated_ci_artifact") is False and
         ci.get("scientific_release_approved") is False,
         "draft source execution identity missing or claiming reviewer approval")
    comparison=report.get("byte_comparison")
    need(report.get("format") == "Permansson.TwoCleanSourceRebuilds.v1" and
         report.get("status") == "REPRODUCIBLE_DRAFT_ONLY" and
         report.get("source_commit_sha") == head and
         report.get("independent_source_roots") == 2 and
         report.get("two_complete_archive_audits") is True and
         report.get("rendered_pages") is True and
         report.get("authenticated_ci_artifact") is False and
         report.get("scientific_release_approved") is False and
         isinstance(report.get("source_tree_sha"),str) and
         SHA.fullmatch(report["source_tree_sha"]) and
         isinstance(comparison,dict) and
         comparison.get("status") == "REPRODUCIBLE_DRAFT_ONLY" and
         comparison.get("source_commit_sha") == head,
         "two-root actual draft execution or comparison was incomplete")
    names=("Permansson_Mathematical_Closure.pdf",
           "Permansson_Mathematical_Closure.tex",
           "Permansson_Mathematical_Closure_E2E.zip",
           "manifest.lock.json", "source_ci_receipts.lock.json",
           "SHA256SUMS.txt", "latex_build.log")
    page_hashes={}
    for side in ("first","second"):
        prefix=side+"/"
        original={name:files.get(prefix+name) for name in names}
        need(all(type(x) is bytes and bool(x) for x in original.values()),
             "two root outputs missing draft PDF, ZIP or checksum metadata")
        manifest=jsonfile(files,prefix+"manifest.lock.json")
        reviews=jsonfile(files,prefix+"source_ci_receipts.lock.json")
        need(manifest.get("format") == "Permansson.MathClosure.BuildReceipt.v1"
             and manifest.get("status") == "DRAFT_NOT_ACCEPTED"
             and manifest.get("source_commit_sha") == head
             and manifest.get("independent_review") == "NOT_RECEIVED"
             and manifest.get("visual_inspection") == "NOT_PERFORMED"
             and manifest.get("source_ci_validation") ==
                 "NOT_BOUND_TO_MERGED_MAIN"
             and reviews == {
                "status":"MISSING_POST_MERGE_SOURCE_AND_REVIEWS",
                "ci_receipts":[], "independent_reviews":[]},
             "draft output falsely reports source review, merged CI or acceptance")
        index=manifest.get("source_tree_files")
        need(isinstance(index,dict) and
             set(index)=={PREFIX+p for p in SOURCE_PATHS} and
             all(isinstance(x,str) and HEX.fullmatch(x) for x in index.values()),
             "draft no longer records exact original thirteen manuscript inputs")
        for name,expected_hash in (
            ("pdf_sha256",original[names[0]]),
            ("tex_sha256",original[names[1]]),
            ("latex_log_sha256",original["latex_build.log"]),
        ):
            need(manifest.get(name)==digest(expected_hash),
                 "draft original artifact hash mismatch: "+name)
        need(original[names[0]].startswith(b"%PDF-"),
             "original two-root draft does not contain a real PDF")
        sums={}
        try:
            for line in original["SHA256SUMS.txt"].decode("utf-8").splitlines():
                hashval,filename=line.split("  ",1)
                need(HEX.fullmatch(hashval) and filename not in sums,
                     "invalid/duplicate source sidecar entry")
                sums[filename]=hashval
        except (UnicodeError, ValueError) as exc:
            raise DraftRehearsalError("invalid actual source SHA256 sidecar") from exc
        required={names[0],names[1],names[2],names[3],names[4]}
        need(set(sums)==required and
             all(digest(original[name])==sums[name] for name in required),
             "incomplete or modified original draft SHA256SUMS.txt")
        page_count=manifest.get("pdf_page_count")
        need(type(page_count) is int and 1<=page_count<=128,
             "missing or invalid rendered PDF page count")
        pages={}
        for number in range(1,page_count+1):
            name=prefix+f"pages/page-{number}.png"
            need(name in files and len(files[name])>0,
                 "missing rendered page from exact PDF build")
            pages[name.removeprefix(prefix)]=digest(files[name])
        extras=[name for name in files
                if name.startswith(prefix+"pages/") and
                name.removeprefix(prefix) not in pages]
        need(not extras,"unexpected or duplicated PDF render page")
        inner=bounded_nested_archive(original[names[2]])
        need(all("manuscript/"+path in inner for path in SOURCE_PATHS),
             "draft nested archive lost manuscript source")
        need(inner.get("manifest.lock.json")==original[names[3]] and
             inner.get("Permansson_Mathematical_Closure.pdf")==original[names[0]] and
             inner.get("source_ci_receipts.lock.json")==original[names[4]],
             "two-root draft nested archive replaced its source outputs")
        for path in SOURCE_PATHS:
            need(digest(inner["manuscript/"+path])==index[PREFIX+path],
                 "actual original draft manuscript source byte mismatch")
        if side=="first":
            first_manifest=original[names[3]]
            first_files={key:digest(val) for key,val in original.items()}
            page_hashes=pages
        else:
            need(original[names[3]]==first_manifest and
                 {key:digest(val) for key,val in original.items()}==first_files
                 and pages==page_hashes,
                 "independent draft outputs/renders differ in actual bytes")
    pdf=digest(files["first/"+names[0]])
    zip_digest=digest(files["first/"+names[2]])
    need(report.get("pdf_sha256")==pdf and
         report.get("archive_sha256")==zip_digest and
         report.get("manifest_sha256")==digest(first_manifest) and
         comparison.get("pdf_sha256")==pdf and
         comparison.get("zip_sha256")==zip_digest and
         comparison.get("page_count")==len(page_hashes) and
         ci.get("pdf_sha256")==pdf and
         ci.get("archive_sha256")==zip_digest,
         "outside reproduction/CI summary does not match actual draft bytes")
    return {
        "format":FORMAT,
        "status":"REPRODUCIBLE_DRAFT_BYTES_AUDITED_NOT_A_RELEASE",
        "source_head":head,
        "pdf_sha256":pdf,
        "archive_sha256":zip_digest,
        "source_member_count":len(SOURCE_PATHS),
        "independent_source_roots":2,
        "rendered_pages_verified":len(page_hashes),
        "original_ci_run_id_reported_unverified":ci["github_run_id"],
        "actual_GitHub_artifact_authentication":False,
        "independent_scholarly_review":False,
        "mathematical_acceptance":False,
        "publication_authorized":False,
    }


def cli(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--artifact-zip",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args(argv)
    try:
        out=a.out.absolute()
        need(not out.exists() and not any(x.is_symlink() for x in (out,*out.parents))
             and not out.is_relative_to(ROOT.resolve()),
             "draft evidence report must be a new detached output")
        raw=a.artifact_zip.read_bytes()
        need(0<len(raw)<=256*1024*1024,
             "unbounded archived draft CI artifact")
        data=audit(raw,a.head)
        out.parent.mkdir(parents=True,exist_ok=True)
        with out.open("x",encoding="utf-8") as stream:
            json.dump(data,stream,indent=2,sort_keys=True)
            stream.write("\n")
        print(json.dumps({"status":data["status"],"head":data["source_head"]}))
        return 0
    except (DraftRehearsalError,OSError,ValueError,TypeError,KeyError,
            zipfile.BadZipFile) as exc:
        print("DRAFT REHEARSAL NOT VERIFIED:",exc,file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(cli())
