#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import py_compile
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PDF = ROOT / "paper" / "Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.pdf"
TEX = ROOT / "paper" / "Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.tex"
FROZEN = ROOT / "verification" / "destructive" / "Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE_FROZEN.zip"
PORTABLE = ROOT / "verification" / "destructive" / "Permansson_TestSuite_v0.1.7_WINDOWS_SAFE.zip"
RELEASE_META = ROOT / "docs" / "releases" / "v0.1.8.json"

EXPECTED = {
    PDF: "24f7dd43c8996b6fc8bedf708704969ba2124e159783bbd2ded45db61525df54",
    TEX: "8235f6140bca33e7e3f0e96b4fd3aa2431c476fbdaf7c5d86d6d0b703ea54ed9",
    FROZEN: "7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a",
    PORTABLE: "864e2fec88b345194b0a9dc4ce9431e6a9a754eb88adea75fb8835b6244f41c3",
}

checks: list[tuple[str, bool, str]] = []

def add(name: str, ok: bool, detail: str = "") -> None:
    checks.append((name, bool(ok), detail))

def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

for path, expected in EXPECTED.items():
    add(f"present:{path.relative_to(ROOT)}", path.is_file(), str(path))
    add(f"sha256:{path.relative_to(ROOT)}", path.is_file() and sha256(path) == expected,
        sha256(path) if path.is_file() else "missing")

tex = TEX.read_text(encoding="utf-8", errors="replace") if TEX.is_file() else ""
add("appendix_e_scope_boundary", "Appendix E - Specialized Finite-Certificate and Rigidity Extensions" in tex)
add("formal_snapshot_cited", "c018f79ea4ce46f4f679ad5bca254509778fc53c" in tex)
add("formal_ci_cited", "35808810682" in tex)
add("run34_present", (ROOT / "verification" / "v0.1.8_release_gate" / "run34_editorial_final_release_gate.py").is_file())
add("run17_30_runner_present", (ROOT / "verification" / "destructive" / "suite" / "run_all.py").is_file())

if RELEASE_META.is_file():
    meta = json.loads(RELEASE_META.read_text(encoding="utf-8"))
    paper = meta.get("paper", {})
    add("release_meta_pdf_hash", paper.get("pdf_sha256") == EXPECTED[PDF], str(paper.get("pdf_sha256")))
    add("release_meta_tex_hash", paper.get("tex_sha256") == EXPECTED[TEX], str(paper.get("tex_sha256")))
    gate = meta.get("release_gate", {})
    add("release_meta_run34", gate.get("run") == 34 and gate.get("passed") == 58 and gate.get("total") == 58,
        json.dumps(gate, sort_keys=True))
else:
    add("release_metadata_present", False, str(RELEASE_META))

python_files = sorted((ROOT / "verification").rglob("*.py"))
syntax_failures: list[str] = []
for path in python_files:
    try:
        py_compile.compile(str(path), doraise=True)
    except Exception as exc:
        syntax_failures.append(f"{path.relative_to(ROOT)}: {exc}")
add("python_sources_compile", not syntax_failures, "; ".join(syntax_failures))
add("python_source_count", len(python_files) >= 30, str(len(python_files)))

failed = [(n, d) for n, ok, d in checks if not ok]
for name, ok, detail in checks:
    print(f"{'PASS' if ok else 'FAIL'} {name}" + (f" — {detail}" if detail else ""))
print(f"\nTOTAL {len(checks) - len(failed)}/{len(checks)}")
if failed:
    sys.exit(1)
