"""Produce a review-pending, exact-source selection for ALL original 45 case positives.

Never turn a discovered method into an accepted mathematical case.  This
prepares the explicit external selection expected by
final_closure_positive_route_candidate.py; that executor still has to run.
The original 45 criteria and historical candidate ledger stay unchanged.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
MAP = "research/paper_closures/post_merge_112/acceptance_case_source_map.json"
FORMAT = "Permansson.PR113.OriginalPositiveSelection.v1"
SHA40 = re.compile(r"^[0-9a-f]{40}$")
PREFERRED_ROLES = ("COMPILER_SOURCE", "EXACT_CHECK")


class SelectionError(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise SelectionError(reason)


def git_bytes(*args):
    try:
        return subprocess.check_output(
            ["git", *args], cwd=ROOT, stderr=subprocess.DEVNULL,
            timeout=45,
        )
    except (OSError, subprocess.CalledProcessError,
            subprocess.TimeoutExpired) as exc:
        raise SelectionError("source Git object unavailable") from exc


def committed(head, path):
    require(isinstance(path, str) and not path.startswith("/") and
            ".." not in Path(path).parts and "\\" not in path,
            "unsafe source path")
    return git_bytes("show", head + ":" + path)


def method_class(source, name):
    """Recover the actual unittest class, never guess from a filename."""
    try:
        parsed = ast.parse(source.decode("utf-8"))
    except (SyntaxError, UnicodeError) as exc:
        raise SelectionError("original test Python cannot be parsed") from exc
    matches = []
    for node in ast.walk(parsed):
        if isinstance(node, ast.ClassDef):
            if any(isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                   and child.name == name for child in node.body):
                matches.append(node.name)
    require(len(matches) == 1,
            "selected positive method must have a unique unittest class: " +
            name)
    return matches[0]


def choose_role(case):
    routes = case.get("test_method_candidates")
    require(isinstance(routes, list), "missing original method registry")
    available = [r for r in routes if isinstance(r, dict) and
                 r.get("role") in PREFERRED_ROLES]
    require(bool(available), "no source-positive route: " + case["case_id"])
    available.sort(key=lambda r: (
        PREFERRED_ROLES.index(r["role"]), r.get("path", ""),
        r.get("method", ""),
    ))
    chosen = available[0]
    require(isinstance(chosen.get("path"), str) and
            chosen["path"].startswith("verification/research/test_") and
            chosen["path"].endswith(".py") and
            isinstance(chosen.get("method"), str) and
            re.fullmatch(r"test_[a-zA-Z0-9_]+", chosen["method"]),
            "malformed original positive route")
    return chosen


def derive(head, source_map, source_reader=committed):
    """Deterministic candidate route coverage; NEVER semantic acceptance."""
    cases = source_map.get("cases")
    require(isinstance(cases, list) and len(cases) == 45,
            "exactly 45 original case criteria are required")
    ids = [row.get("case_id") for row in cases if isinstance(row, dict)]
    require(len(ids) == 45 and all(isinstance(i, str) and i for i in ids)
            and len(set(ids)) == 45, "duplicate or missing original case ID")
    selections, source_hashes = [], {}
    for case in sorted(cases, key=lambda c: c["case_id"]):
        cid = case["case_id"]
        method = choose_role(case)
        test = method["path"]
        test_raw = source_reader(head, test)
        cls = method_class(test_raw, method["method"])
        providers = case.get("historical_proof_declarations")
        require(isinstance(providers, list) and providers,
                "original theorem provider missing: " + cid)
        paths = sorted({p.get("path") for p in providers
                        if isinstance(p, dict) and isinstance(
                            p.get("path"), str)})
        require(bool(paths), "malformed provider inventory: " + cid)
        # A single route needs a source path for execution, while every
        # supporting declaration stays obligatory in the full acceptance gate.
        proof_path = paths[0]
        for source_path in (test, *paths):
            raw = source_reader(head, source_path)
            source_hashes[source_path] = hashlib.sha256(raw).hexdigest()
        selections.append({
            "case_id": cid,
            "test_path": test,
            "test_class": cls,
            "test_method": method["method"],
            "proof_source_path": proof_path,
        })
    return {
        "format": FORMAT,
        "cases": selections,
    }, {
        "format": "Permansson.PR113.PositiveSelectionReviewCandidate.v1",
        "source_head": head,
        "status": "ROUTES_DERIVED_REQUIRE_INDEPENDENT_CRITERION_RELEVANCE_REVIEW",
        "selected_case_count": 45,
        "reviewed": False,
        "executed": False,
        "accepted_cases": 0,
        "source_sha256": dict(sorted(source_hashes.items())),
        "warnings": [
            "One deterministically selected original registered route per case is NOT a proof of scope relevance.",
            "The full acceptance graph still requires all supporting theorem types, positives and semantic negatives.",
            "Execute the separate real Lean/unittest route runner from the same committed source head.",
        ],
    }


def execute(head, out):
    require(isinstance(head, str) and SHA40.fullmatch(head),
            "full exact source SHA required")
    require(git_bytes("rev-parse", "HEAD").decode().strip() == head,
            "source checkout is not requested head")
    require(not git_bytes("status", "--porcelain=v1",
                          "--untracked-files=all",
                          "--", "verification/research",
                          "research/paper_closures/post_merge_112"),
            "original selection sources are dirty or untracked")
    target = Path(out)
    require(not target.is_symlink(), "symlink output forbidden")
    target = target.resolve()
    require(not target.exists() and
            not target.is_relative_to(ROOT.resolve()) and
            not ROOT.resolve().is_relative_to(target),
            "output must be a new detached external directory")
    mapping = json.loads(committed(head, MAP))
    selection, review = derive(head, mapping)
    target.mkdir(parents=True)
    (target / "selection.json").write_text(
        json.dumps(selection, indent=2, sort_keys=True) + "\n")
    (target / "selection_review_pending.json").write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n")
    return review


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        result = execute(args.head, args.out)
    except (SelectionError, OSError, ValueError, TypeError, KeyError) as exc:
        print("PR113 original positive selection BLOCKED:", exc,
              file=sys.stderr)
        return 2
    print(json.dumps({"status": result["status"],
                      "selected_cases": result["selected_case_count"]},
                     sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
