"""Authenticate REAL merged-M, two-source-root reproducibility GitHub artifact.

This is not a scholarly signoff. It binds the actual successful Actions run,
job/check, authoritative artifact SHA256, retained receipt and TWO independently
built byte-identical PDFs, archives, manifests and rendered pages. The target
workflow may be dispatched on main only after genuine authorized M exists.
No Boolean claimed inside producer JSON grants authentication.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from final_closure_authenticate import live, paginate
from final_closure_producer_bytes import inspect_zip, ProducerBytesError

FORMAT = "Permansson.PR113.GenuineCleanReproductionCI.v1"
WORKFLOW = ".github/workflows/pr113-clean-paper-rebuild.yml"
JOB = "clean-paper-rebuild"
ARTIFACT = "pr113-clean-paper-rebuild-draft"
SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")


class ReproductionAuthenticationError(ValueError):
    pass


def demand(ok, message):
    if not ok:
        raise ReproductionAuthenticationError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def exact(payload, name):
    demand(name in payload, "missing original clean root artifact: " + name)
    return payload[name]


def validate_clean_root_bytes(members, *, merged, expected_pdf):
    """Check canonical execution metadata AND both actual byte-identical roots."""
    try:
        report = json.loads(exact(members, "reproduction_receipt.json"))
        identity = json.loads(exact(members, "ci_execution_identity.json"))
    except (TypeError, UnicodeDecodeError, ValueError) as exc:
        raise ReproductionAuthenticationError("malformed real reproduction receipt") from exc
    demand(isinstance(report, dict) and
           report.get("format") == "Permansson.TwoCleanSourceRebuilds.v1" and
           report.get("status") == "REPRODUCIBLE_DRAFT_ONLY" and
           report.get("source_commit_sha") == merged and
           report.get("independent_source_roots") == 2 and
           report.get("git_clone_mode") == "local_no_hardlinks_no_checkout" and
           report.get("rendered_pages") is True and
           report.get("two_complete_archive_audits") is True and
           report.get("pdf_sha256") == expected_pdf and
           report.get("authenticated_ci_artifact") is False and
           report.get("scientific_release_approved") is False,
           "actual two-source-root receipt is incomplete or self-approved")
    comparison = report.get("byte_comparison")
    demand(isinstance(comparison,dict) and
           comparison.get("status") == "REPRODUCIBLE_DRAFT_ONLY" and
           comparison.get("source_commit_sha") == merged and
           comparison.get("pdf_sha256") == expected_pdf,
           "clean source-root comparison not genuinely complete")
    demand(identity.get("format") == "Permansson.CICleanRebuildCandidate.v1"
           and identity.get("status") == "EXECUTED_DRAFT_ONLY_NO_SCHOLARLY_REVIEW"
           and identity.get("source_head") == merged
           and identity.get("github_repository") == "HMarcusWH/PermanssonLean"
           and identity.get("github_job") == JOB
           and identity.get("pdf_sha256") == expected_pdf
           and identity.get("authenticated_ci_artifact") is False,
           "uploaded exact-run identity is incorrect or promoted")
    files = {
        "Permansson_Mathematical_Closure.pdf":expected_pdf,
        "Permansson_Mathematical_Closure_E2E.zip":report["archive_sha256"],
        "manifest.lock.json":report["manifest_sha256"],
    }
    for relative,digest in files.items():
        demand(isinstance(digest,str) and SHA256.fullmatch(digest),
               "source-root digest invalid")
        a=exact(members,"first/"+relative)
        b=exact(members,"second/"+relative)
        demand(a == b and sha(a) == digest,
               "two source roots do not contain identical real artifacts")
    import json as _json
    manifest=_json.loads(members["first/manifest.lock.json"])
    demand(manifest.get("source_commit_sha") == merged and
           manifest.get("status") == "DRAFT_NOT_ACCEPTED" and
           manifest.get("pdf_sha256") == expected_pdf and
           isinstance(manifest.get("pdf_page_count"), int) and
           manifest.get("pdf_page_count") > 0,
           "reproduced source manifest malformed or incorrectly approved")
    for item in ("Permansson_Mathematical_Closure.tex",
                 "latex_build.log", "SHA256SUMS.txt", "source_ci_receipts.lock.json"):
        demand(exact(members,"first/"+item) ==
               exact(members,"second/"+item),
               "canonical draft artifact differs between source roots: "+item)
    pagesA={path[len("first/pages/"):]:data
            for path,data in members.items() if path.startswith("first/pages/")
            and path.endswith(".png")}
    pagesB={path[len("second/pages/"):]:data
            for path,data in members.items() if path.startswith("second/pages/")
            and path.endswith(".png")}
    demand(len(pagesA) == manifest["pdf_page_count"] and
           pagesA and pagesA == pagesB and
           all(re.fullmatch(r"page-[0-9]+[.]png", name) for name in pagesA),
           "missing/duplicated/non-identical actual rendered PDF pages")
    return report, identity, pagesA


def authenticate_merged_reproduction(merged, expected_pdf, identities,
                                      zip_path: Path):
    """Verify authentic GitHub run+check+artifact, then retained original bytes."""
    demand(isinstance(merged,str) and SHA40.fullmatch(merged) and
           isinstance(expected_pdf,str) and SHA256.fullmatch(expected_pdf)
           and isinstance(identities,dict),
           "reproduction requires real M/PDF and typed producer identities")
    for key in ("run_id","run_attempt","job_id","check_run_id","artifact_id"):
        demand(type(identities.get(key)) is int and identities[key] > 0,
               "missing real producing GitHub identity: "+key)
    run=live("/actions/runs/"+str(identities["run_id"]))
    demand(run.get("id") == identities["run_id"] and
           run.get("head_sha") == merged and
           run.get("head_branch") == "main" and
           run.get("run_attempt") == identities["run_attempt"] and
           run.get("status") == "completed" and
           run.get("conclusion") == "success" and
           run.get("event") in ("push","workflow_dispatch") and
           (run.get("path") == WORKFLOW or
            str(run.get("path","")).endswith("/"+WORKFLOW)),
           "clean-paper producer is not genuinely successful on merged main M")
    jobs=paginate("/actions/runs/"+str(identities["run_id"])+"/jobs",key="jobs")
    matches=[j for j in jobs if j.get("id") == identities["job_id"]
             and j.get("name") == JOB]
    demand(len(matches)==1 and
           matches[0].get("run_id") == identities["run_id"] and
           matches[0].get("run_attempt") == identities["run_attempt"] and
           matches[0].get("head_sha") == merged and
           matches[0].get("status") == "completed" and
           matches[0].get("conclusion") == "success" and
           str(matches[0].get("check_run_url","")).endswith(
               "/check-runs/"+str(identities["check_run_id"])),
           "producer job/check does not match original clean rebuild")
    check=live("/check-runs/"+str(identities["check_run_id"]))
    demand(check.get("id") == identities["check_run_id"] and
           check.get("head_sha") == merged and
           check.get("name") == JOB and
           check.get("status") == "completed" and
           check.get("conclusion") == "success" and
           (check.get("app") or {}).get("slug") == "github-actions",
           "actual clean rebuild GitHub check not successful")
    artifact=live("/actions/artifacts/"+str(identities["artifact_id"]))
    gh_digest=artifact.get("digest")
    demand(artifact.get("id") == identities["artifact_id"] and
           artifact.get("name") == ARTIFACT and
           artifact.get("expired") is False and
           (artifact.get("workflow_run") or {}).get("id") ==
                identities["run_id"] and
           (artifact.get("workflow_run") or {}).get("head_sha") == merged and
           isinstance(gh_digest,str) and gh_digest.startswith("sha256:") and
           SHA256.fullmatch(gh_digest[7:]),
           "missing genuine GitHub artifact SHA256 at exact merged M")
    input_path=Path(zip_path)
    demand(input_path.is_file() and not input_path.is_symlink() and
           not any(parent.is_symlink() for parent in input_path.absolute().parents),
           "detached clean source-root ZIP must be a regular unsymlinked file")
    raw=input_path.read_bytes()
    demand(sha(raw) == gh_digest[7:],
           "downloaded two-root ZIP bytes differ from GitHub digest")
    try:
        members=inspect_zip(raw)
    except ProducerBytesError as exc:
        raise ReproductionAuthenticationError("unsafe original two-root ZIP") from exc
    report,identity,pages=validate_clean_root_bytes(
        members,merged=merged,expected_pdf=expected_pdf)
    demand(identity.get("github_run_id") == identities["run_id"] and
           identity.get("github_run_attempt") == identities["run_attempt"] and
           identity.get("archive_sha256") == report["archive_sha256"],
           "retained CI execution file belongs to another job/attempt")
    return {
        "format": FORMAT,
        "status":"TWO_CLEAN_SOURCE_BUILDS",
        "source_commit_sha":merged, "pdf_sha256":expected_pdf,
        "artifact_sha256":gh_digest[7:],
        "authenticated_ci_artifact":True,
        "source_tree_sha256":None,
        "rendered_page_count":len(pages),
        "run_id":identities["run_id"],"run_attempt":identities["run_attempt"],
        "job_id":identities["job_id"],"check_run_id":identities["check_run_id"],
        "artifact_id":identities["artifact_id"],
        "scholarly_review_approved":False,
        "mathematical_release_approved":False,
    }
