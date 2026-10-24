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
import zipfile
from pathlib import Path
import re
import shutil
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



def _sha_file(path: Path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def _text_delta(left: Path, right: Path) -> dict:
    """Inspect genuine retained log bytes without suppressing any warning."""
    if not left.is_file() or not right.is_file():
        return {"first_exists": left.is_file(), "second_exists": right.is_file()}
    first, second = left.read_bytes(), right.read_bytes()
    offset = next((i for i, (a, b) in enumerate(zip(first, second)) if a != b),
                  min(len(first), len(second)))
    one, two = first.decode("utf-8", errors="replace").splitlines(), \
               second.decode("utf-8", errors="replace").splitlines()
    wrong = next((i for i in range(min(len(one), len(two)))
                  if one[i] != two[i]), min(len(one), len(two)))
    lo, hi = max(0, wrong-2), wrong+3
    return {
        "sha256_first": hashlib.sha256(first).hexdigest(),
        "sha256_second": hashlib.sha256(second).hexdigest(),
        "first_differing_byte_offset": offset,
        "first_differing_line_index": wrong,
        "line_count": [len(one), len(two)],
        "lines_first": [x[:500] for x in one[lo:hi]],
        "lines_second": [x[:500] for x in two[lo:hi]],
    }


def _zip_delta(left: Path, right: Path) -> dict:
    if not left.is_file() or not right.is_file():
        return {"first_exists": left.is_file(), "second_exists": right.is_file()}
    def inventory(path):
        with zipfile.ZipFile(path) as z:
            return {
                name: {
                    "sha256": hashlib.sha256(z.read(name)).hexdigest(),
                    "date_time": list(z.getinfo(name).date_time),
                    "compression": z.getinfo(name).compress_type,
                    "external_attr": z.getinfo(name).external_attr,
                    "raw_bytes": z.getinfo(name).file_size,
                } for name in z.namelist()
            }, z.namelist()
    try:
        a, ao = inventory(left)
        b, bo = inventory(right)
    except (OSError, zipfile.BadZipFile, RuntimeError) as exc:
        return {"invalid_zip": type(exc).__name__}
    names = sorted(set(a) | set(b))
    changed = {
        name: {"first": a.get(name), "second": b.get(name)}
        for name in names if a.get(name) != b.get(name)
    }
    return {
        "member_order_matches": ao == bo,
        "member_count": [len(ao), len(bo)],
        "first_different_members": dict(list(changed.items())[:15]),
        "all_changed_member_count": len(changed),
        "first_order": ao[:10], "second_order": bo[:10],
    }


def diagnose_root_differences(left: Path, right: Path) -> dict:
    """Bounded failure diagnostics; NEVER normalize away a byte difference."""
    fields = {}
    a = left/"manifest.lock.json"
    b = right/"manifest.lock.json"
    if a.is_file() and b.is_file():
        try:
            x, y = json.loads(a.read_bytes()), json.loads(b.read_bytes())
            fields = {name: {"first": x.get(name), "second": y.get(name)}
                      for name in sorted(set(x) | set(y))
                      if x.get(name) != y.get(name)}
        except (ValueError, UnicodeError, TypeError):
            fields = {"unparseable_manifest": True}
    selected = ("Permansson_Mathematical_Closure.pdf",
                "Permansson_Mathematical_Closure.tex", "latex_build.log",
                "latex_build.raw.log", "manifest.lock.json",
                "Permansson_Mathematical_Closure_E2E.zip",
                "SHA256SUMS.txt", "source_ci_receipts.lock.json")
    files = {name: {"first": _sha_file(left/name), "second": _sha_file(right/name)}
             for name in selected}
    logs = {}
    for name in ("latex_build.log", "latex_build.raw.log"):
        if files[name]["first"] != files[name]["second"]:
            logs[name] = _text_delta(left/name, right/name)
    pages_first = {p.name: _sha_file(p) for p in (left/"pages").glob("*.png")}
    pages_second = {p.name: _sha_file(p) for p in (right/"pages").glob("*.png")}
    return {
        "manifest_changed_fields": fields,
        "artifact_sha256": files,
        "differing_logs": logs,
        "draft_archive": _zip_delta(
            left/"Permansson_Mathematical_Closure_E2E.zip",
            right/"Permansson_Mathematical_Closure_E2E.zip"),
        "rendered_pages": {
            "count": [len(pages_first), len(pages_second)],
            "changed": sorted(name for name in set(pages_first) | set(pages_second)
                              if pages_first.get(name) != pages_second.get(name))[:15],
        },
        "byte_identity_waived": False,
        "scientific_release_approved": False,
    }


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
    # Keep independent Git source roots, but use ONE canonical TeX output
    # pathname sequentially. pdfTeX inserts newlines according to the length
    # of the displayed absolute output path, which cannot be fixed by
    # replacing already-wrapped strings in compiler diagnostics.
    #
    # Rename the complete finished stage outside the reused pathname.
    # Do not delete or edit one compiler log, nor share any output/cache
    # between source passes.
    stable_stage = out / "_canonical_tex_stage"
    with tempfile.TemporaryDirectory(prefix="perm-source-roots-") as td:
        temp = Path(td)
        for index in ("first", "second"):
            checkout = temp / ("source-" + index)
            output = out / index
            need(not output.exists() and not stable_stage.exists() and
                 not stable_stage.is_symlink(),
                 "shared TeX build stage or completed output was not fresh")
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
                       "--out", str(stable_stage), "--engine", engine]
            if render:
                command.append("--render")
            cmd(command, cwd=checkout, timeout=1200)
            need(stable_stage.is_dir() and not stable_stage.is_symlink(),
                 "genuine TeX run did not create a regular fresh stage")
            cmd([sys.executable, str(script / "verify_release.py"),
                 "--manifest", str(stable_stage / "manifest.lock.json")],
                cwd=checkout, timeout=120)
            receipt = json.loads((stable_stage / "manifest.lock.json").read_bytes())
            need(receipt.get("source_commit_sha") == head and
                 receipt.get("status") == "DRAFT_NOT_ACCEPTED",
                 "clean replay manifest claims wrong commit or approval")
            if render:
                need((stable_stage / "pages").is_dir() and
                     receipt.get("pdf_page_count") is not None,
                     "clean replay lacks complete rendered pages")
            # All outputs (including the unmodified raw compiler transcript)
            # are moved as a whole; no normalization of diagnostics.
            stable_stage.rename(output)
            need(output.is_dir() and not stable_stage.exists(),
                 "TeX stage not detached/emptied between independent builds")
            results.append({"source_head": head, "tree": tree,
                            "pdf_sha256": receipt["pdf_sha256"],
                            "archive_sha256": hashlib.sha256(
                                (output / "Permansson_Mathematical_Closure_E2E.zip")
                                .read_bytes()).hexdigest(),
                            "manifest_sha256": hashlib.sha256(
                                (output / "manifest.lock.json").read_bytes()).hexdigest()})
    need(not stable_stage.exists(),
         "shared TeX output cache remained after independent source runs")
    if not results or results[0] != results[1]:
        # Report EXACT mismatched fields; do not downgrade byte identity,
        # turn nondeterminism into a green receipt or erase either build root.
        fields = sorted(set(results[0]) | set(results[1])) if len(results) == 2 else []
        mismatches = {
            field: {"first": results[0].get(field),
                    "second": results[1].get(field)}
            for field in fields if results[0].get(field) != results[1].get(field)
        }
        diagnostics = diagnose_root_differences(out/"first", out/"second")
        failed = {
            "format": "Permansson.CleanRootMismatchDiagnostic.v1",
            "status": "TWO_CLEAN_SOURCE_BUILDS_BLOCKED",
            "source_commit_sha": head,
            "source_tree_sha": tree,
            "differences": mismatches,
            "source_root_byte_diagnostics": diagnostics,
            "authenticated_ci_artifact": False,
            "scientific_release_approved": False,
        }
        (out / "reproduction_failure.json").write_text(
            json.dumps(failed, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")
        raise CleanReproductionError(
            "independent source-root manifests differ: " +
            json.dumps(mismatches, sort_keys=True) +
            "; byte-level diagnosis: " +
            json.dumps(diagnostics, sort_keys=True)[:11000])
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
        "output_staging_profile": "two_distinct_git_roots_sequential_fresh_identical_output_path",
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
