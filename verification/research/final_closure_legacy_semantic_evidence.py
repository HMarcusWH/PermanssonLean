"""Bounded detached execution and retention for the other 20 original cases.

The canonical map contains 45 source-routed semantic negatives. Twenty routes
are older unittest methods rather than direct source append-mutant records.
This runner executes their exact selected methods, retaining the actual Lean
input bytes and compiler results via an opt-in passive capture hook, including
nested Python audit drivers. Output remains UNREVIEWED and is NOT an accepted
semantic-negative receipt or a GitHub-authenticated execution attestation.
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
import tempfile

from final_closure_case_receipts import INVALID_DIAGNOSTICS, SEMANTIC_DIAGNOSTICS, ROOT
from final_closure_mutation_evidence import (
    MutationEvidenceError, committed_file_bytes, git_head
)
from final_closure_original_semantic_batch import SPECS as DETACHED_SPECS

CASE_MAP = ROOT / "research/paper_closures/post_merge_112/acceptance_case_source_map.json"
HOOK = ROOT / "verification/research/pr113_compiler_trace_hook.py"
RUNNER = ROOT / "verification/research/final_closure_legacy_semantic_evidence.py"
CHECKOUT_PATHS = ("PermanssonResearch", "PermanssonLean",
                  "verification/research", "research/paper_closures/post_merge_112")
MAX_CASES = 45
MAX_EVENT_COUNT = 120
MAX_GROUP_BYTES = 64 * 1024 * 1024
MAX_RUN_LOG = 4 * 1024 * 1024
SOURCE_PREFIX = "verification/research/test_"
SHA40 = re.compile(r"^[0-9a-f]{40}$")


def canonical(data):
    return (json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def original_case_map(head):
    committed_file_bytes(head, CASE_MAP, root=ROOT)
    data = json.loads(CASE_MAP.read_bytes())
    cases = data.get("cases")
    if data.get("original_cases") != MAX_CASES or not isinstance(cases, list):
        raise MutationEvidenceError("original 45-case source map unavailable")
    ids = [row.get("case_id") for row in cases if isinstance(row, dict)]
    if len(ids) != MAX_CASES or len(set(ids)) != MAX_CASES:
        raise MutationEvidenceError("original 45 IDs malformed")
    if not isinstance(DETACHED_SPECS, dict) or len(DETACHED_SPECS) != 25:
        raise MutationEvidenceError("detached producer inventory changed")
    missing = sorted(set(ids) - set(DETACHED_SPECS))
    if len(missing) != 20 or set(ids) != set(missing) | set(DETACHED_SPECS):
        raise MutationEvidenceError("25+20 original-case partition violated")
    return {row["case_id"]: row for row in cases}, tuple(missing)


def shard_cases(head, index, count):
    byid, missing = original_case_map(head)
    if not 1 <= count <= len(missing) or not 0 <= index < count:
        raise MutationEvidenceError("invalid original case shard")
    selected = tuple(cid for i, cid in enumerate(missing) if i % count == index)
    if not selected:
        raise MutationEvidenceError("empty original case shard")
    return byid, selected


def selected_methods(head, row):
    if row.get("effective_accepted") is not False:
        raise MutationEvidenceError("legacy candidate was approved without review")
    choices = row.get("test_method_candidates")
    if not isinstance(choices, list):
        raise MutationEvidenceError("legacy case missing method routes")
    seen = set()
    groups = {}
    for route in choices:
        if route.get("role") != "SEMANTIC_NEGATIVE":
            continue
        rel = route.get("path")
        method = route.get("method")
        if (not isinstance(rel, str) or not rel.startswith(SOURCE_PREFIX)
                or not rel.endswith(".py") or ".." in Path(rel).parts
                or not isinstance(method, str) or not re.fullmatch(r"test_[A-Za-z0-9_]+", method)):
            raise MutationEvidenceError("invalid selected semantic method")
        if (rel, method) in seen:
            raise MutationEvidenceError("duplicate semantic method")
        seen.add((rel, method))
        source = ROOT / rel
        raw = committed_file_bytes(head, source, root=ROOT)
        tree = ast.parse(raw.decode("utf-8"), filename=rel)
        owners = [
            node.name for node in tree.body if isinstance(node, ast.ClassDef)
            and any(isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and inner.name == method for inner in node.body)
        ]
        if len(owners) != 1:
            raise MutationEvidenceError("named original unittest method not uniquely owned")
        group = (rel, owners[0])
        groups.setdefault(group, []).append(method)
    if not seen:
        raise MutationEvidenceError("original case missing semantic negative method")
    return tuple((path, cls, tuple(sorted(methods)))
                 for (path, cls), methods in sorted(groups.items()))


def assert_clean_checkout():
    proc = subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all",
         "--", *CHECKOUT_PATHS], cwd=ROOT, text=True, capture_output=True,
        timeout=30)
    if proc.returncode or proc.stdout.strip():
        raise MutationEvidenceError("Git source or selected test tree is dirty")


def test_observations(directory, *, expected_case=None, expected_methods=None):
    events = sorted(directory.glob("event-*/observation.json"))
    if len(events) > MAX_EVENT_COUNT:
        raise MutationEvidenceError("unbounded Lean capture event count")
    total = 0
    results = []
    for item in events:
        root = item.parent
        if item.is_symlink() or root.is_symlink():
            raise MutationEvidenceError("symlink in compiler observation")
        raw = item.read_bytes()
        meta = json.loads(raw)
        if meta.get("format") != "Permansson.LegacyLeanCompilerObservation.v1":
            raise MutationEvidenceError("wrong compiler observation schema")
        if (expected_case is not None and
                meta.get("case_id_unverified") != expected_case):
            raise MutationEvidenceError("cross-case compiler observation substituted")
        observed_method = meta.get("selected_method_unverified")
        ambiguous_method = False
        if expected_methods is not None:
            permitted = expected_methods.split(",")
            if observed_method not in permitted:
                # A class-level setup runs *before* TestCase.run can mark the
                # individual test. Retain the diagnostic for inspection but
                # never count it toward any one semantic-negative method.
                if len(permitted) > 1 and observed_method == expected_methods:
                    ambiguous_method = True
                else:
                    raise MutationEvidenceError(
                        "cross-method compiler observation substituted")
        allowed_members = {"observation.json", "source.lean", "stdout.log", "stderr.log"}
        if (any(p.is_symlink() for p in root.iterdir()) or
                any(p.name not in allowed_members for p in root.iterdir())):
            raise MutationEvidenceError("unsafe or unexpected compiler observation member")
        total += len(raw)
        for label, field in (("source.lean", "source_sha256"),
                             ("stdout.log", "stdout_sha256"),
                             ("stderr.log", "stderr_sha256")):
            target = root / label
            reported = meta.get(field)
            if target.exists():
                if target.is_symlink() or not target.is_file():
                    raise MutationEvidenceError("unsafe compiler observation")
                blob = target.read_bytes()
                total += len(blob)
                if not isinstance(reported, str) or digest(blob) != reported:
                    raise MutationEvidenceError("compiler observation hash mismatch")
            elif reported is not None:
                # A too-large or missing observation cannot be silently certified.
                meta["truncated_or_missing"] = True
        output = b""
        for label in ("stdout.log", "stderr.log"):
            target = root / label
            if target.is_file():
                output += target.read_bytes().lower() + b"\n"
        semantic = (
            isinstance(meta.get("returncode"), int) and meta["returncode"] != 0
            and b"error:" in output
            and any(token.encode() in output for token in SEMANTIC_DIAGNOSTICS)
            and not any(token.encode() in output for token in INVALID_DIAGNOSTICS)
            and meta.get("source_retained") is True
            and not meta.get("truncated_or_missing")
            and not ambiguous_method
        )
        results.append({
            "observation_id": root.name,
            "source_sha256": meta.get("source_sha256"),
            "returncode": meta.get("returncode"),
            "method_observed_unverified": observed_method,
            "method_attribution_ambiguous": ambiguous_method,
            "possible_semantic_diagnostic": semantic,
            "source_retained": meta.get("source_retained"),
            "raw_metadata_sha256": digest(raw),
        })
    if total > MAX_GROUP_BYTES:
        raise MutationEvidenceError("total compiler evidence exceeds bound")
    return results


def run_case(head, case_id, row, output, timeout):
    grouped = selected_methods(head, row)
    case_dir = output / case_id
    case_dir.mkdir(parents=True, exist_ok=False)
    records = []
    with tempfile.TemporaryDirectory(prefix="pr113-tracer-") as td:
        hook_dir = Path(td)
        (hook_dir / "sitecustomize.py").write_text(
            "from pr113_compiler_trace_hook import install\ninstall()\n",
            encoding="utf-8")
        for number, (relative, cls, methods) in enumerate(grouped):
            stem = Path(relative).stem
            target = case_dir / ("test-%02d" % number)
            target.mkdir()
            capture = target / "raw_compiler"
            capture.mkdir()
            env = os.environ.copy()
            env["PR113_CAPTURE_DIR"] = str(capture)
            env["PR113_CASE_ID"] = case_id
            env["PR113_SELECTED_METHOD"] = ",".join(methods)
            env["PYTHONPATH"] = os.pathsep.join(
                [str(hook_dir), str(ROOT / "verification/research"),
                 env.get("PYTHONPATH", "")])
            argv = [sys.executable, "-m", "unittest", "-v"] + [
                stem + "." + cls + "." + method for method in methods
            ]
            try:
                done = subprocess.run(argv, cwd=ROOT, env=env,
                                      capture_output=True, timeout=timeout)
                rc, stdout, stderr = done.returncode, done.stdout, done.stderr
                exception = None
            except subprocess.TimeoutExpired as exc:
                rc = None
                stdout = exc.stdout or b""
                stderr = exc.stderr or b""
                exception = "test timeout; not mathematical evidence"
            if len(stdout) > MAX_RUN_LOG or len(stderr) > MAX_RUN_LOG:
                raise MutationEvidenceError("original unittest stdout/stderr over limit")
            (target / "test_stdout.log").write_bytes(stdout)
            (target / "test_stderr.log").write_bytes(stderr)
            events = test_observations(
                capture, expected_case=case_id,
                expected_methods=",".join(methods))
            record = {
                "format": "Permansson.LegacyCaseTestExecutionCandidate.v1",
                "case_id": case_id,
                "test_file": relative,
                "test_class": cls,
                "selected_methods": list(methods),
                "source_test_sha256": digest(committed_file_bytes(
                    head, ROOT / relative, root=ROOT)),
                "command": argv,
                "test_exit_code": rc,
                "exception": exception,
                "stdout_sha256": digest(stdout),
                "stderr_sha256": digest(stderr),
                "compiler_events": events,
                "compiler_observations_count": len(events),
                "possible_semantic_observations": sum(
                    bool(e["possible_semantic_diagnostic"]) for e in events),
                "status": "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED"
                          if rc == 0 and any(e["possible_semantic_diagnostic"]
                                             for e in events)
                          else "INCOMPLETE_OR_UNVERIFIABLE_UNREVIEWED",
                "independent_review": False,
                "ci_check_run_id": None,
                "release_approved": False,
            }
            (target / "unreviewed_test_manifest.json").write_bytes(canonical(record))
            records.append(record)
    return records


def run_shard(head, index, count, output, timeout):
    if not SHA40.fullmatch(head) or git_head() != head:
        raise MutationEvidenceError("frozen source head mismatch")
    for source in (HOOK, RUNNER, ROOT / "lean-toolchain",
                   ROOT / "lake-manifest.json"):
        committed_file_bytes(head, source, root=ROOT)
    assert_clean_checkout()
    byid, selected = shard_cases(head, index, count)
    output = output.resolve()
    root = ROOT.resolve()
    if (output.exists() or output.is_relative_to(root)
            or root.is_relative_to(output)):
        raise MutationEvidenceError("candidate output cannot overlap checkout")
    tree = subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"],
                                   cwd=ROOT, text=True).strip()
    if not SHA40.fullmatch(tree):
        raise MutationEvidenceError("invalid source tree")
    output.mkdir(parents=True, exist_ok=False)
    rows = []
    for case_id in selected:
        rows.append({"case_id": case_id,
                     "tests": run_case(head, case_id, byid[case_id], output, timeout)})
        assert_clean_checkout()
    failed = [row["case_id"] for row in rows if any(
        entry["status"] != "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED"
        for entry in row["tests"])]
    manifest = {
        "format": "Permansson.OriginalLegacyCompilerShard.v1",
        "status": "INCOMPLETE_UNREVIEWED" if failed
                  else "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED",
        "source_head": head,
        "source_tree": tree,
        "case_ids": list(selected),
        "case_reports": rows,
        "remaining_source_append_producer_cases": len(DETACHED_SPECS),
        "independent_review": False,
        "ci_check_run_id": None,
        "merged_main_sha": None,
        "scientific_release_approved": False,
        "github_run_environment_unverified": {
            k: os.environ.get(k) for k in (
                "GITHUB_REPOSITORY", "GITHUB_SHA", "GITHUB_RUN_ID",
                "GITHUB_RUN_ATTEMPT", "GITHUB_JOB", "GITHUB_WORKFLOW")
        },
    }
    (output / "unreviewed_shard_manifest.json").write_bytes(canonical(manifest))
    return manifest


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--head", required=True)
    parser.add_argument("--shard-index", required=True, type=int)
    parser.add_argument("--shard-count", required=True, type=int)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=2100)
    args = parser.parse_args(argv)
    try:
        if not 60 <= args.timeout <= 3600:
            raise MutationEvidenceError("unbounded original test timeout")
        output = run_shard(args.head, args.shard_index, args.shard_count,
                           args.out, args.timeout)
        print(json.dumps({"status": output["status"],
                          "head": output["source_head"],
                          "cases": output["case_ids"]}, sort_keys=True))
        return 0 if output["status"] == "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED" else 2
    except (MutationEvidenceError, OSError, KeyError, ValueError,
            subprocess.CalledProcessError) as exc:
        print("ORIGINAL LEGACY EVIDENCE BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
