"""Independent-root draft PDF/ZIP reproducibility audit, NOT publication.

Two complete draft TeX runs are required. A mismatch is a reproducibility
failure, never a reason to rewrite expected checksums in an approval file.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile

MODULE = Path(__file__).with_name("build.py")
spec = importlib.util.spec_from_file_location("permansson_draft_builder", MODULE)
builder = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(builder)

FILES = ("Permansson_Mathematical_Closure.pdf",
         "Permansson_Mathematical_Closure.tex",
         "Permansson_Mathematical_Closure_E2E.zip",
         "manifest.lock.json", "latex_build.log",
         "SHA256SUMS.txt", "source_ci_receipts.lock.json")


class ReproducibilityError(ValueError):
    pass


def digest(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def compare_artifacts(first: Path, second: Path) -> dict:
    differences = {}
    for name in FILES:
        a, b = first/name, second/name
        if not a.is_file() or not b.is_file():
            differences[name] = "MISSING_OUTPUT"
        elif digest(a) != digest(b):
            differences[name] = "NONDETERMINISTIC_BYTES"
    pages_a = sorted(p for p in (first/"pages").glob("*.png"))
    pages_b = sorted(p for p in (second/"pages").glob("*.png"))
    if pages_a or pages_b:
        left = {p.name: digest(p) for p in pages_a}
        right = {p.name: digest(p) for p in pages_b}
        if left != right:
            differences["rendered_pages"] = "NONDETERMINISTIC_RENDER"
    if differences:
        raise ReproducibilityError("independent-root build differs: " +
                                   json.dumps(differences, sort_keys=True))
    manifest = json.loads((first/"manifest.lock.json").read_text())
    if manifest.get("status") != "DRAFT_NOT_ACCEPTED":
        raise ReproducibilityError("repeat build inadvertently claims release")
    return {"status": "REPRODUCIBLE_DRAFT_ONLY",
            "source_commit_sha": manifest.get("source_commit_sha"),
            "pdf_sha256": digest(first/FILES[0]),
            "zip_sha256": digest(first/FILES[2]),
            "page_count": manifest.get("pdf_page_count")}


def reproduce(*, engine: str = "pdflatex", render: bool = True):
    with tempfile.TemporaryDirectory(prefix="permansson-repro-a-") as a, \
         tempfile.TemporaryDirectory(prefix="permansson-repro-b-") as b:
        one, two = Path(a), Path(b)
        builder.build(one, engine, render)
        builder.build(two, engine, render)
        return compare_artifacts(one, two)


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--engine", choices=["pdflatex", "xelatex", "lualatex"],
                        default="pdflatex")
    parser.add_argument("--no-render", action="store_true")
    a = parser.parse_args(argv)
    try:
        result = reproduce(engine=a.engine, render=not a.no_render)
    except (ValueError, OSError, RuntimeError) as exc:
        print("REPRODUCIBILITY BLOCKED:", exc)
        return 2
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
