"""Source-preserving real Lean false-mutant evidence, and deterministic ZIP.

Emits candidate diagnostic bytes with explicit head/source/test bindings.
No result here is a verified original case until independently reviewed and
bound to genuine GitHub check-run IDs on the frozen source head.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

from final_closure_case_receipts import (
    INVALID_DIAGNOSTICS, SEMANTIC_DIAGNOSTICS, ROOT as SOURCE_ROOT,
)

ROOT = Path(__file__).resolve().parents[2]
SHA40 = re.compile(r"^[0-9a-f]{40}$")
BAD_LOG = INVALID_DIAGNOSTICS + ("sorryax", "failed to synthesize")
MAX_LOG_BYTES = 4 * 1024 * 1024


class MutationEvidenceError(RuntimeError):
    pass


def hash_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def git_head() -> str:
    p = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                       capture_output=True, text=True, timeout=20)
    if p.returncode:
        raise MutationEvidenceError("missing frozen Git checkout")
    return p.stdout.strip()


def committed_file_bytes(head: str, file: Path, *, root: Path = ROOT) -> bytes:
    """Require the actual committed Git blob and reject local substitution.

    Matching rev-parse HEAD alone does not establish the source file bytes.
    Clean compiler products and independent execution remain separate gates.
    """
    root = root.resolve()
    if not SHA40.fullmatch(head):
        raise MutationEvidenceError("invalid frozen source commit identity")
    if file.is_symlink() or not file.is_file():
        raise MutationEvidenceError("source symlink or missing file")
    target = file.resolve()
    if not target.is_relative_to(root):
        raise MutationEvidenceError("source escapes frozen checkout")
    relative = target.relative_to(root).as_posix()
    if not relative or ":" in relative:
        raise MutationEvidenceError("unsupported tracked source path")
    try:
        record = subprocess.run(
            ["git", "cat-file", "blob", f"{head}:{relative}"],
            cwd=root, capture_output=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise MutationEvidenceError("committed source unavailable") from exc
    if record.returncode:
        raise MutationEvidenceError("source not tracked at frozen Git head")
    actual = target.read_bytes()
    if actual != record.stdout:
        raise MutationEvidenceError("source bytes differ from frozen Git blob")
    return actual

def lean_result(source: Path):
    try:
        return subprocess.run(["lake", "env", "lean", str(source)],
                              cwd=ROOT, capture_output=True,
                              text=True, timeout=900)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise MutationEvidenceError("Lean/Lake unavailable or timed out") from exc


def verify_negative(positive, negative, original_source: bytes,
                    mutant_source: bytes):
    positive_log = (positive.stdout + "\n" + positive.stderr).lower()
    log = (negative.stdout + "\n" + negative.stderr).lower()
    if (positive.returncode != 0 or
        any(x in positive_log for x in BAD_LOG)):
        raise MutationEvidenceError("positive control did not compile cleanly")
    if negative.returncode == 0:
        raise MutationEvidenceError("false mutant accidentally compiled")
    if (not any(x in log for x in SEMANTIC_DIAGNOSTICS) or
        "error:" not in log or
        any(x in log for x in BAD_LOG)):
        raise MutationEvidenceError("invalid negative: parser/import/resource failure")
    if original_source == mutant_source:
        raise MutationEvidenceError("mutant did not change any source bytes")
    def imports(raw):
        return [s.strip() for s in raw.decode("utf-8").splitlines()
                if s.strip().startswith("import ")]
    if imports(original_source) != imports(mutant_source):
        raise MutationEvidenceError("mutation changed imports, not only semantics")
    if len(positive_log.encode()) > MAX_LOG_BYTES or len(log.encode()) > MAX_LOG_BYTES:
        raise MutationEvidenceError("compiler diagnostic too large")
    return True


def produce(head: str, *, true_source: Path, mutant: Path, test_path: Path,
            test_name: str, case_id: str, claim_ids: list[str],
            out: Path) -> dict:
    if head != git_head() or not SHA40.fullmatch(head):
        raise MutationEvidenceError("stale or synthetic Git HEAD")
    if out.resolve().is_relative_to(ROOT.resolve()):
        raise MutationEvidenceError("detached evidence must be out of the source tree")
    if true_source.is_symlink() or test_path.is_symlink():
        raise MutationEvidenceError("symlink source/test cannot certify")
    source = true_source.resolve()
    test = test_path.resolve()
    if (not source.is_relative_to(ROOT.resolve()) or
        not test.is_relative_to(ROOT.resolve()) or
        not source.is_file() or source.suffix != ".lean" or
        not test.is_file() or test.suffix != ".py"):
        raise MutationEvidenceError("source/test must be genuine repo files")
    test_bytes = committed_file_bytes(head, test)
    if not re.search(r"(?m)^\s*def\s+" + re.escape(test_name) + r"\(",
                     test_bytes.decode("utf-8")):
        raise MutationEvidenceError("test name not defined by source")
    if not case_id or not isinstance(claim_ids, list):
        raise MutationEvidenceError("case/review ownership missing")
    original_bytes = committed_file_bytes(head, source)
    mutant_bytes = mutant.read_bytes()
    if not shutil.which("lake"):
        raise MutationEvidenceError("pinned Lean required, cannot skip")
    positive = lean_result(source)
    negative = lean_result(mutant)
    verify_negative(positive, negative, original_bytes, mutant_bytes)
    out.mkdir(parents=True, exist_ok=True)
    prefix = re.sub(r"[^A-Za-z0-9_-]", "_", case_id + "_" + test_name)
    positive_name = prefix + ".positive.log"
    negative_name = prefix + ".negative.log"
    positive_log = (positive.stdout + "\n" + positive.stderr).encode("utf-8")
    negative_log = (negative.stdout + "\n" + negative.stderr).encode("utf-8")
    (out / positive_name).write_bytes(positive_log)
    (out / negative_name).write_bytes(negative_log)
    mutant_name = prefix + ".mutant.lean"
    (out / mutant_name).write_bytes(mutant_bytes)
    return {
        "id": prefix, "head_sha": head,
        "test_path": str(test.relative_to(ROOT)).replace("\\", "/"),
        "test_name": test_name,
        "source_sha256": hash_bytes(test_bytes),
        "case_ids": [case_id], "claim_ids": claim_ids,
        "mutant_source_sha256": hash_bytes(mutant_bytes),
        "mutant_source_member": mutant_name,
        "original_lean_source_sha256": hash_bytes(original_bytes),
        "original_lean_source_path": str(source.relative_to(ROOT)).replace("\\", "/"),
        "positive_control": {
            "compiled": True, "exit_code": 0, "lean_toolchain": "4.34.0",
            "log_member": positive_name, "log_sha256": hash_bytes(positive_log),
        },
        "outcome": "REJECTED_SEMANTIC", "compiler_exit_code": negative.returncode,
        "log_member": negative_name, "log_sha256": hash_bytes(negative_log),
        "check_run_id": None,
        "CI_binding": "AWAITING_REAL_HEAD_CHECK_RUN_AND_REVIEW",
        "review_status": "NOT_RECEIVED",
    }


def seal_logs(source: Path, archive: Path) -> str:
    """Stable member ordering/timestamps, excluding mutable archive itself."""
    files = [p for p in source.rglob("*") if p.is_file()]
    if not files:
        raise MutationEvidenceError("no diagnostic logs to archive")
    if archive.resolve().is_relative_to(source.resolve()):
        raise MutationEvidenceError("archive must be detached from member directory")
    archive.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive, "w") as out:
        for item in sorted(files, key=lambda p: p.relative_to(source).as_posix()):
            rel = item.relative_to(source).as_posix()
            if item.is_symlink() or ".." in Path(rel).parts:
                raise MutationEvidenceError("unsafe evidence member")
            info = zipfile.ZipInfo(rel, (1980, 1, 1, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            out.writestr(info, item.read_bytes(), compress_type=zipfile.ZIP_DEFLATED)
    return hash_bytes(archive.read_bytes())


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True)
    ap.add_argument("--true-source", type=Path, required=True)
    ap.add_argument("--mutant", type=Path, required=True)
    ap.add_argument("--test-path", type=Path, required=True)
    ap.add_argument("--test-name", required=True)
    ap.add_argument("--case-id", required=True)
    ap.add_argument("--claim-id", action="append", default=[])
    ap.add_argument("--output", type=Path, required=True)
    opts = ap.parse_args(argv)
    try:
        record = produce(opts.head, true_source=opts.true_source,
                         mutant=opts.mutant, test_path=opts.test_path,
                         test_name=opts.test_name, case_id=opts.case_id,
                         claim_ids=opts.claim_id, out=opts.output)
    except (MutationEvidenceError, OSError, ValueError) as exc:
        print("SEMANTIC MUTATION EVIDENCE BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps(record, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
