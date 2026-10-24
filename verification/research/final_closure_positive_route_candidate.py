"""Execute original positive-test method routes for all 45 cases.

This is a genuine, unreviewed *execution candidate*, NOT a v3 producing-CI
receipt, an original-case decision or an independent mathematical review.
A selected positive method MUST be frozen as COMPILER_SOURCE/EXACT_CHECK;
the positive control of a SEMANTIC_NEGATIVE method cannot stand in for it.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from final_closure_mutation_evidence import (
    ROOT, committed_file_bytes, git_head, lean_result,
    pinned_lean_version, MutationEvidenceError,
)
from final_closure_case_receipts import INVALID_DIAGNOSTICS
from final_closure_producer_v2_bridge import SHA40

FORMAT = "Permansson.PR113.Original45PositiveRoutesCandidate.v1"
SELECTION = "Permansson.PR113.OriginalPositiveSelection.v1"
TEST_METHOD = re.compile(r"^test_[A-Za-z0-9_]+$")
CLASS = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
MAX_REPORT = 4 * 1024 * 1024


class PositiveRouteError(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise PositiveRouteError(reason)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def source_method(head, path, cls, method):
    require(isinstance(path, str) and
            path.startswith("verification/research/test_") and
            path.endswith(".py") and
            ".." not in Path(path).parts and
            isinstance(cls, str) and CLASS.fullmatch(cls) and
            isinstance(method, str) and TEST_METHOD.fullmatch(method),
            "not a named original unittest source method")
    raw = committed_file_bytes(head, ROOT / path, root=ROOT)
    try:
        parsed = ast.parse(raw.decode("utf-8"), filename=path)
    except (ValueError, UnicodeError, SyntaxError) as exc:
        raise PositiveRouteError("named original test source is not parseable") from exc
    found = [node for node in parsed.body
             if isinstance(node, ast.ClassDef) and node.name == cls and
             any(isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef))
                 and inner.name == method for inner in node.body)]
    require(len(found) == 1, "original named positive test was not uniquely defined")
    return raw


def parse_selection(payload, case_map):
    cases = case_map.get("cases") if isinstance(case_map, dict) else None
    require(isinstance(cases, list) and len(cases) == 45 and
            isinstance(payload, dict) and
            payload.get("format") == SELECTION and
            isinstance(payload.get("cases"), list),
            "45 original positive source-method selections required")
    canon = {row["case_id"]:row for row in cases}
    require(len(canon) == 45, "original 45 case IDs are not unique")
    chosen = {}
    required = {"case_id", "test_path", "test_class",
                "test_method", "proof_source_path"}
    for row in payload["cases"]:
        require(isinstance(row, dict) and set(row) == required,
                "malformed or unauthorized positive route selection")
        cid = row["case_id"]
        require(cid in canon and cid not in chosen,
                "duplicated/unknown original source case")
        original = canon[cid]
        require(isinstance(row["test_class"], str) and
                CLASS.fullmatch(row["test_class"]) is not None and
                isinstance(row["test_method"], str) and
                TEST_METHOD.fullmatch(row["test_method"]) is not None and
                isinstance(row["test_path"], str) and
                row["test_path"].startswith("verification/research/test_") and
                row["test_path"].endswith(".py"),
                "selected original positive class/method/path is malformed")
        matches = [route for route in original.get("test_method_candidates", [])
                   if route.get("path") == row["test_path"] and
                   route.get("method") == row["test_method"] and
                   route.get("role") in ("COMPILER_SOURCE","EXACT_CHECK")]
        require(len(matches) == 1,
                "positive route is not frozen as COMPILER_SOURCE/EXACT_CHECK")
        proof_path = row["proof_source_path"]
        require(any(x.get("path") == proof_path for x in
                    original.get("historical_proof_declarations", ())),
                "selected successful Lean source does not belong to original case")
        chosen[cid] = row
    require(set(chosen) == set(canon),
            "at least one original case lacks a selected positive role")
    return chosen


def execute(head, selection_path, out):
    require(isinstance(head, str) and SHA40.fullmatch(head) and
            git_head() == head, "stale/not actual exact-H source checkout")
    selected_file = Path(selection_path)
    require(selected_file.is_file() and not selected_file.is_symlink() and
            not selected_file.resolve().is_relative_to(ROOT.resolve()),
            "selection must be an external reviewed input file")
    case_map_file = ROOT/"research/paper_closures/post_merge_112/acceptance_case_source_map.json"
    case_map = json.loads(committed_file_bytes(
        head, case_map_file, root=ROOT))
    chosen = parse_selection(json.loads(selected_file.read_bytes()), case_map)
    target = Path(out)
    require(not target.is_symlink(), "candidate output symlink prohibited")
    target = target.resolve()
    require(not target.exists() and
            not target.is_relative_to(ROOT.resolve()) and
            not target.is_relative_to(selected_file.parent.resolve()),
            "source-method output must be new and disjoint from trusted inputs")
    lean_version = pinned_lean_version(head)
    target.mkdir(parents=True, exist_ok=False)
    results = []
    for cid, row in sorted(chosen.items()):
        test_path = row["test_path"]
        method = row["test_method"]
        cls = row["test_class"]
        test_bytes = source_method(head, test_path, cls, method)
        proof_path = row["proof_source_path"]
        proof_bytes = committed_file_bytes(
            head, ROOT/proof_path, root=ROOT)
        sandbox = target/cid
        sandbox.mkdir()
        # unittest imports by basename. Keep both original research helper
        # directory and repository root on sys.path without touching the Git
        # checkout or inserting source-owned fake test outcomes.
        env = os.environ.copy()
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env["PYTHONPATH"] = (str(ROOT/"verification/research") +
                             os.pathsep + str(ROOT) +
                             os.pathsep + env.get("PYTHONPATH", ""))
        qualified = Path(test_path).stem + "." + cls + "." + method
        try:
            proc = subprocess.run(
                [sys.executable, "-B", "-m", "unittest", qualified, "-v"],
                cwd=ROOT, env=env, capture_output=True, timeout=900)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise PositiveRouteError("registered original positive test unavailable") from exc
        require(proc.returncode == 0 and
                b"Ran 1 test" in proc.stderr and b"OK" in proc.stderr and
                b"skipped=" not in proc.stderr and
                b"expected failures=" not in proc.stderr and
                len(proc.stdout)+len(proc.stderr) <= MAX_REPORT,
                "named positive unittest failed, skipped or ran wrong scope: "+cid)
        original_lean = lean_result(ROOT/proof_path)
        real_log = (original_lean.stdout+"\n"+original_lean.stderr).encode()
        low = real_log.decode("utf-8", errors="replace").lower()
        require(original_lean.returncode == 0 and
                len(real_log) <= MAX_REPORT and
                not any(fragment in low for fragment in INVALID_DIAGNOSTICS) and
                "error:" not in low,
                "original case positive Lean provider does not compile: "+cid)
        # Re-open all source bytes after real method + compiler execution.
        require(committed_file_bytes(head,ROOT/test_path,root=ROOT) == test_bytes and
                committed_file_bytes(head,ROOT/proof_path,root=ROOT) == proof_bytes,
                "source/test changed while running positive controls")
        (sandbox/"unittest_stdout.log").write_bytes(proc.stdout)
        (sandbox/"unittest_stderr.log").write_bytes(proc.stderr)
        (sandbox/"source_positive.log").write_bytes(real_log)
        record = {
            "format":"Permansson.PR113.OriginalCasePositiveCandidate.v1",
            "status":"SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED",
            "head_sha":head, "case_id":cid, "test_path":test_path,
            "test_class":cls, "test_name":method,
            "positive_role":next(x["role"] for x in
                next(y for y in case_map["cases"] if y["case_id"]==cid)
                ["test_method_candidates"]
                if x["path"]==test_path and x["method"]==method),
            "source_sha256":sha(test_bytes),
            "proof_source_path":proof_path,
            "proof_source_sha256":sha(proof_bytes),
            "lean_toolchain":lean_version,
            "unittest_stdout_sha256":sha(proc.stdout),
            "unittest_stderr_sha256":sha(proc.stderr),
            "source_positive_log_sha256":sha(real_log),
            "source_positive_exit_code":original_lean.returncode,
            "registered_method_exit_code":proc.returncode,
            "actual_producing_check_run_id":None,
            "authenticated_ci_artifact":False,
            "independent_case_review":False,
            "scientific_release_approved":False,
        }
        (sandbox/"unreviewed_positive.json").write_text(
            json.dumps(record,sort_keys=True,indent=2)+"\n")
        results.append(record)
    require(len(results)==45,"not all original positives actually executed")
    manifest={
        "format":FORMAT,"status":"EXECUTED_NO_PRODUCING_CI_OR_MATH_REVIEW",
        "head_sha":head,"actual_positive_cases":45,
        "positive_route_records":results,
        "independent_case_reviews":0,
        "authenticated_ci_artifact":False,
        "scientific_release_approved":False,
    }
    (target/"unreviewed_45_positive_routes.json").write_text(
        json.dumps(manifest,sort_keys=True,indent=2)+"\n")
    return manifest


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head",required=True)
    parser.add_argument("--selection",required=True,type=Path)
    parser.add_argument("--out",required=True,type=Path)
    args=parser.parse_args(argv)
    try:
        result=execute(args.head,args.selection,args.out)
    except (PositiveRouteError,MutationEvidenceError,ValueError,
            KeyError,TypeError,OSError) as exc:
        print("ORIGINAL 45 POSITIVE ROUTES BLOCKED:",exc,file=sys.stderr)
        return 2
    print(json.dumps({"status":result["status"],
                      "actual_positive_cases":result["actual_positive_cases"]}))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
