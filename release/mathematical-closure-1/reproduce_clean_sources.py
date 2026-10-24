"""Two clean, independent Git source roots -> actual TeX PDF/ZIP byte replay.

The older reproduce.py compares two output roots of ONE checkout. This script
makes two independent Git clones without hardlinked objects, detaches BOTH at
one exact commit, verifies their trees, builds both source roots, validates
all thirteen archived manuscript inputs and compares every resulting output.
No independent reviewer, M identity, artifact-attesting CI job, or release
approval is invented by a successful local repetition.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SHA40 = re.compile(r"^[0-9a-f]{40}$")

import reproduce


class CleanReproductionError(ValueError):
    pass


def need(flag, why):
    if not flag:
        raise CleanReproductionError(why)


def cmd(arguments, *, cwd=None, timeout=600):
    try:
        result = subprocess.run(arguments, cwd=cwd, text=True,
                                capture_output=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise CleanReproductionError("source/release command unavailable") from exc
    if result.returncode:
        raise CleanReproductionError(
            "source/release command failed: " + " ".join(map(str, arguments)) +
            "\n" + (result.stdout + result.stderr)[-2500:])
    return result.stdout.strip()


def git_object(args, cwd):
    return cmd(["git", *args], cwd=cwd, timeout=30)


def reproduce_from_clean_source_roots(out: Path, *, head: str,
                                      engine: str = "pdflatex",
                                      render: bool = True) -> dict:
    need(isinstance(head, str) and SHA40.fullmatch(head) is not None,
         "exact source HEAD SHA required")
    need(engine in ("pdflatex", "lualatex", "xelatex"),
         "unapproved TeX engine")
    out = out.resolve()
    need(not out.is_relative_to(ROOT.resolve()) and
         not ROOT.resolve().is_relative_to(out),
         "source/output roots must be filesystem-disjoint")
    need(not out.exists(), "replay output root must be new, not reused")
    need(git_object(["rev-parse", "HEAD"], ROOT) == head,
         "current checkout not at exact requested H/M")
    tree = git_object(["rev-parse", "HEAD^{tree}"], ROOT)
    need(SHA40.fullmatch(tree) is not None,
         "missing authentic Git source tree")
    out.mkdir(parents=True)
    results = []
    with tempfile.TemporaryDirectory(prefix="perm-source-roots-") as td:
        temp = Path(td)
        for index in ("first", "second"):
            checkout = temp / ("source-" + index)
            output = out / index
            cmd(["git", "clone", "--local", "--no-hardlinks", "--no-checkout",
                 str(ROOT), str(checkout)], timeout=180)
            git_object(["checkout", "--detach", head], checkout)
            need(git_object(["rev-parse", "HEAD"], checkout) == head and
                 git_object(["rev-parse", "HEAD^{tree}"], checkout) == tree,
                 "replayed source root did not match H/tree")
            need(not git_object(
                ["status", "--porcelain", "--untracked-files=no"], checkout),
                 "replayed source root was dirty before build")
            script = checkout / "release" / "mathematical-closure-1"
            command = [sys.executable, str(script / "build.py"),
                       "--out", str(output), "--engine", engine]
            if render:
                command.append("--render")
            cmd(command, cwd=checkout, timeout=1200)
            cmd([sys.executable, str(script / "verify_release.py"),
                 "--manifest", str(output / "manifest.lock.json")],
                cwd=checkout, timeout=120)
            receipt = json.loads((output / "manifest.lock.json").read_bytes())
            need(receipt.get("source_commit_sha") == head and
                 receipt.get("status") == "DRAFT_NOT_ACCEPTED",
                 "clean replay manifest claims wrong commit or approval")
            if render:
                need((output / "pages").is_dir() and
                     receipt.get("pdf_page_count") is not None,
                     "clean replay lacks complete rendered pages")
            results.append({"source_head": head, "tree": tree,
                            "pdf_sha256": receipt["pdf_sha256"],
                            "archive_sha256": hashlib.sha256(
                                (output / "Permansson_Mathematical_Closure_E2E.zip")
                                .read_bytes()).hexdigest(),
                            "manifest_sha256": hashlib.sha256(
                                (output / "manifest.lock.json").read_bytes()).hexdigest()})
    if not results or results[0] != results[1]:
        # Report EXACT mismatched fields; do not downgrade byte identity,
        # turn nondeterminism into a green receipt or erase either build root.
        fields = sorted(set(results[0]) | set(results[1])) if len(results) == 2 else []
        mismatches = {
            field: {"first": results[0].get(field),
                    "second": results[1].get(field)}
            for field in fields if results[0].get(field) != results[1].get(field)
        }
        failed = {
            "format": "Permansson.CleanRootMismatchDiagnostic.v1",
            "status": "TWO_CLEAN_SOURCE_BUILDS_BLOCKED",
            "source_commit_sha": head,
            "source_tree_sha": tree,
            "differences": mismatches,
            "authenticated_ci_artifact": False,
            "scientific_release_approved": False,
        }
        (out / "reproduction_failure.json").write_text(
            json.dumps(failed, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
        raise CleanReproductionError(
            "independent source-root manifests differ: " +
            json.dumps(mismatches, sort_keys=True))
    comparison = reproduce.compare_artifacts(out / "first", out / "second")
    need(comparison.get("pdf_sha256") == results[0]["pdf_sha256"] and
         comparison.get("zip_sha256") == results[0]["archive_sha256"],
         "byte comparison disconnected from source roots")
    report = {
        "format": "Permansson.TwoCleanSourceRebuilds.v1",
        "status": "REPRODUCIBLE_DRAFT_ONLY",
        "source_commit_sha": head,
        "source_tree_sha": tree,
        "independent_source_roots": 2,
        "git_clone_mode": "local_no_hardlinks_no_checkout",
        "engine": engine, "rendered_pages": render,
        "pdf_sha256": results[0]["pdf_sha256"],
        "archive_sha256": results[0]["archive_sha256"],
        "manifest_sha256": results[0]["manifest_sha256"],
        "two_complete_archive_audits": True,
        "byte_comparison": comparison,
        "authenticated_ci_artifact": False,
        "scientific_release_approved": False,
    }
    (out / "reproduction_receipt.json").write_text(
        json.dumps(report, sort_keys=True, indent=2) + "\n")
    return report


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--source-head", required=True)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--engine", choices=["pdflatex", "xelatex", "lualatex"],
                    default="pdflatex")
    ap.add_argument("--no-render", action="store_true")
    opts = ap.parse_args(argv)
    try:
        result = reproduce_from_clean_source_roots(
            opts.out, head=opts.source_head, engine=opts.engine,
            render=not opts.no_render)
    except (CleanReproductionError, OSError, ValueError, KeyError) as exc:
        print("TWO CLEAN SOURCE BUILDS BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
