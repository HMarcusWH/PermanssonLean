#!/usr/bin/env python3
"""Inventory exact theorem source headers and candidate test SHA digests.

Source names and hashes are not Lean compilation, transitive-axiom checks,
semantic negative evidence, or third-party review. No auto-acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SNAP = ROOT / "research/paper_closures/post_merge_112"
DECLARATION = re.compile(
    r"(?m)^\s*(?:private\s+|protected\s+)?"
    r"(?:(?:noncomputable|unsafe)\s+)?"
    r"(?:theorem|lemma|def)\s+([A-Za-z0-9_']+)(?=\W)"
)

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git_head() -> str | None:
    try:
        return subprocess.check_output(
            ("git", "rev-parse", "HEAD"), cwd=ROOT, text=True,
            stderr=subprocess.DEVNULL, timeout=15).strip()
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None

def exact_statements(path: Path) -> list[dict]:
    """Report definition header hashes, never claim proof execution."""
    content = path.read_text(encoding="utf-8")
    matches = list(DECLARATION.finditer(content))
    rows = []
    for i, match in enumerate(matches):
        limit = matches[i+1].start() if i+1 < len(matches) else len(content)
        end = content.find(":=", match.end(), limit)
        if end < 0:
            continue
        statement = content[match.start():end].strip()
        rows.append({
            "declaration": match.group(1),
            "statement_sha256": hashlib.sha256(statement.encode("utf-8")).hexdigest(),
            "compiler_result": "NOT_VERIFIED",
            "transitive_axioms": None,
            "semantic_negative_receipts": [],
        })
    return rows

def generate(output: Path) -> dict:
    decisions = json.loads((SNAP/"acceptance_decisions.json").read_text())
    crosswalk = json.loads((SNAP/"theorem_crosswalk.json").read_text())
    root_imports = (ROOT/"PermanssonResearch.lean").read_text().splitlines()
    source_rows = []
    for item in crosswalk["closure_additions"]:
        relative = Path(item["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("unsafe acceptance source path")
        path = ROOT/relative
        imported = ("import " + str(relative.with_suffix("")).replace("/", ".")) in root_imports
        exists = path.is_file()
        source_rows.append({
            "id": item["id"], "path": item["path"],
            "imported_by_research_root": imported,
            "source_sha256": sha256(path) if exists else None,
            "declarations": exact_statements(path) if exists else [],
            "status": "SOURCE_PRESENT_UNREVIEWED" if exists and imported else "MISSING_SOURCE_OR_IMPORT",
            "compiled_head_sha": None, "axiom_receipts": [],
            "independent_review_receipts": [],
        })
    tests = []
    for path in sorted((ROOT/"verification/research").glob("test_final*.py")):
        tests.append({
            "path": str(path.relative_to(ROOT)).replace("\\", "/"),
            "source_sha256": sha256(path),
            "status": "SOURCE_PRESENT_EXECUTION_NOT_VERIFIED",
        })
    report = {
        "format": "Permansson.FinalClosureCandidateObservation.v2",
        "source_head_sha": git_head(), "source_rows": source_rows,
        "candidate_test_sources": tests,
        "original_case_count": len(decisions["cases"]),
        "unresolved_original_case_ids": [
            c["case_id"] for c in decisions["cases"] if c["decision"]
            not in ("VERIFIED_SELECTED_SCOPE", "VERIFIED_NEGATIVE")
        ],
        "source_bound_ci": [], "independent_reviews": [],
        "status": "CANDIDATE_UNREVIEWED",
        "trust_boundary": "Hashes show literal source text only, not Lean proof or review.",
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return report

def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    report = generate(args.output)
    print(json.dumps({
        "source_sha": report["source_head_sha"],
        "modules": len(report["source_rows"]),
        "source_files_found": sum(bool(c["source_sha256"]) for c in report["source_rows"]),
        "root_imported": sum(c["imported_by_research_root"] for c in report["source_rows"]),
        "theorem_headers": sum(len(c["declarations"]) for c in report["source_rows"]),
        "tests_indexed": len(report["candidate_test_sources"]),
        "original_cases_pending": len(report["unresolved_original_case_ids"]),
        "output": str(args.output),
    }, indent=2))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
