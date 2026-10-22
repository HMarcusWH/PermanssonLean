"""Independent byte-complete draft manuscript archive verification.

The build and this verifier intentionally keep independently enumerated
source/output contracts. A checksum of selected files is not enough: a
release archive must contain ALL 13 canonical manuscript inputs and ALL
five generated draft receipt artifacts, with no extra/ambiguous members.
This is byte verification, NOT mathematical or scholarly acceptance.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import stat
import zipfile

SOURCE_FILES = (
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
)
GENERATED = (
    "Permansson_Mathematical_Closure.pdf",
    "Permansson_Mathematical_Closure.tex",
    "manifest.lock.json", "source_ci_receipts.lock.json",
    "latex_build.log",
)
SUMMED = (
    "Permansson_Mathematical_Closure.pdf",
    "Permansson_Mathematical_Closure.tex",
    "manifest.lock.json", "source_ci_receipts.lock.json",
    "Permansson_Mathematical_Closure_E2E.zip",
)
SHA256 = re.compile(r"^[0-9a-f]{64}$")
MEMBER_LIMIT = 32 * 1024 * 1024
TOTAL_LIMIT = 96 * 1024 * 1024
ZIP_BYTES_LIMIT = 48 * 1024 * 1024


class DraftArchiveError(ValueError):
    pass


def demand(test, why):
    if not test:
        raise DraftArchiveError(why)


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def secure_members(archive):
    path = Path(archive)
    demand(path.is_file() and not path.is_symlink() and
           path.stat().st_size <= ZIP_BYTES_LIMIT,
           "missing/unsafe/oversized draft ZIP")
    expected = {"manuscript/" + name for name in SOURCE_FILES}
    expected.update(GENERATED)
    with zipfile.ZipFile(path) as z:
        infos = z.infolist()
        demand(len(infos) == len(expected), "extra/duplicate/missing draft ZIP member")
        checked = set()
        actual = set()
        total = 0
        for i in infos:
            path = i.filename
            norm = path.casefold()
            mode = i.external_attr >> 16
            demand(path in expected and norm not in checked and
                   not path.startswith("/") and "\\" not in path and
                   ".." not in path.split("/") and
                   not i.is_dir() and (mode == 0 or stat.S_ISREG(mode)),
                   "unsafe or unexpected draft ZIP member")
            demand(not (i.flag_bits & 1) and
                   0 <= i.file_size <= MEMBER_LIMIT,
                   "encrypted or oversized draft ZIP member")
            checked.add(norm)
            actual.add(path)
            total += i.file_size
        demand(actual == expected and total <= TOTAL_LIMIT,
               "draft source/output archive not complete")
        data = {}
        for name in sorted(expected):
            raw = z.read(name)
            demand(len(raw) <= MEMBER_LIMIT, "member exceeded declared limit")
            data[name] = raw
        demand(z.testzip() is None, "corrupted ZIP member")
        return data


def verify_draft_archive(directory: Path, manifest: dict):
    directory = Path(directory)
    sources = manifest.get("source_tree_files")
    demand(isinstance(sources, dict) and
           set(sources) == {
               "research_papers/mathematical_closure/" + name
               for name in SOURCE_FILES
           }, "missing/unknown one of 13 canonical manuscript inputs")
    for name, digest in sources.items():
        demand(isinstance(digest, str) and SHA256.fullmatch(digest),
               "invalid manuscript source digest: " + name)
    bundle = secure_members(directory / "Permansson_Mathematical_Closure_E2E.zip")
    for src in SOURCE_FILES:
        key = "research_papers/mathematical_closure/" + src
        demand(sha_bytes(bundle["manuscript/" + src]) == sources[key],
               "source content mismatch: " + src)
    for name in GENERATED:
        real = directory / name
        demand(real.is_file() and not real.is_symlink() and
               sha_bytes(real.read_bytes()) == sha_bytes(bundle[name]),
               "archived artifact differs from draft byte: " + name)
    expected_digests = {
        "Permansson_Mathematical_Closure.pdf": manifest.get("pdf_sha256"),
        "Permansson_Mathematical_Closure.tex": manifest.get("tex_sha256"),
        "latex_build.log": manifest.get("latex_log_sha256"),
    }
    for name, expected in expected_digests.items():
        demand(isinstance(expected, str) and SHA256.fullmatch(expected) and
               sha_bytes(bundle[name]) == expected,
               "draft manifest digest differs: " + name)
    demand(bundle["Permansson_Mathematical_Closure.pdf"].startswith(b"%PDF-"),
           "draft PDF signature missing")
    demand(bundle["manifest.lock.json"] ==
           (directory / "manifest.lock.json").read_bytes(),
           "archived draft manifest was relabeled")
    receipt = json.loads(bundle["source_ci_receipts.lock.json"])
    demand(isinstance(receipt, dict) and
           receipt.get("status") == "MISSING_POST_MERGE_SOURCE_AND_REVIEWS" and
           receipt.get("ci_receipts") == [] and
           receipt.get("independent_reviews") == [],
           "draft may not contain unauthenticated source approvals")
    sums = directory / "SHA256SUMS.txt"
    demand(sums.is_file() and not sums.is_symlink(), "missing SHA256SUMS.txt")
    actual = {}
    for line in sums.read_text(encoding="utf-8").splitlines():
        bits = line.split("  ")
        demand(len(bits) == 2, "noncanonical checksum line")
        h, name = bits
        demand(isinstance(h, str) and SHA256.fullmatch(h) and
               name in SUMMED and name not in actual,
               "unknown/duplicate checksum input")
        actual[name] = h
    demand(set(actual) == set(SUMMED), "checksum inventory incomplete")
    for name, expected in actual.items():
        p = directory / name
        demand(p.is_file() and not p.is_symlink() and
               sha_bytes(p.read_bytes()) == expected,
               "checksum mismatch: " + name)
    page_dir = directory / "pages"
    if page_dir.exists():
        demand(page_dir.is_dir() and not page_dir.is_symlink(),
               "invalid rendered page directory")
        files = list(page_dir.iterdir())
        demand(all(p.is_file() and not p.is_symlink() and
                   re.fullmatch(r"page-[1-9][0-9]*[.]png", p.name)
                   for p in files), "unrelated/malformed page image")
        count = manifest.get("pdf_page_count")
        demand(type(count) is int and count > 0 and
               sorted(int(p.stem[5:]) for p in files) ==
                   list(range(1, count + 1)),
               "PDF render has missing/extra/duplicate pages")
    return {"status": "COMPLETE_UNAPPROVED_DRAFT",
            "canonical_sources": len(SOURCE_FILES),
            "archived_outputs": len(GENERATED),
            "pdf_sha256": manifest["pdf_sha256"],
            "source_commit_sha": manifest.get("source_commit_sha")}
