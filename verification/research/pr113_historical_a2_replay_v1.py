"""Replay original A2 in its own immutable checkout, not against current H.

This is mandatory engineering evidence, not migration/security approval.
The same acceptance method also compiles current source with its native
successor, preserving P-02 coverage. The standalone current-source test is
retained. No workflow, historical executor, proof or review is replaced.
"""
from __future__ import annotations

from pathlib import Path
import subprocess
import tempfile

HISTORICAL_A2 = "f71a76032b169aac7bfe0694aa715339a94d4e05"
ORIGINAL_TEST = "verification/research/test_localized_prefix_compiler.py"
ORIGINAL_TEST_BLOB = "c0f49038ea9b590720c78be85968eb63f5ac820f"
EXECUTORS = {
    "verification/research/localized_prefix_gate.py":
        "6f15dca74895e59a4d4bfcb54d38b471a1798be3",
    "verification/research/localized_prefix_support.py":
        "93462e9546ba494e8384d75ce49ff9020f831216",
}
PINS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
FORMAT = "Permansson.PR113.HistoricalA2EngineeringReplay.v1"
STATUS = "HISTORICAL_AND_CURRENT_A2_ENGINEERING_PASSED"


class HistoricalReplayError(ValueError):
    pass


def need(value, message):
    if not value:
        raise HistoricalReplayError(message)


def git(root, *args):
    try:
        process = subprocess.run(
            ["git", "-C", str(root), "-c", "core.hooksPath=/dev/null", *args],
            capture_output=True, timeout=90, check=False)
    except (OSError, subprocess.SubprocessError) as exc:
        raise HistoricalReplayError("historical Git operation unavailable") from exc
    need(process.returncode == 0,
         "historical Git operation failed: " + repr(args[:3]) + ": " +
         process.stderr.decode("utf-8", "replace")[-1200:])
    return process.stdout


def scalar(root, *args):
    return git(root, *args).decode("ascii").strip()


def unchanged(root, expected):
    need(scalar(root, "rev-parse", "HEAD") == expected,
         "source HEAD changed during historical replay")
    need(not git(root, "status", "--porcelain=v1", "--untracked-files=all"),
         "historical replay source contains tracked or untracked changes")


def verify_executors(current, old):
    for path, expected in EXECUTORS.items():
        for root in (current, old):
            raw = git(root, "show", "HEAD:" + path)
            need(scalar(root, "rev-parse", "HEAD:" + path) == expected,
                 "original A2 executor Git identity changed: " + path)
            file = root / path
            need(file.is_file() and not file.is_symlink()
                 and file.read_bytes() == raw,
                 "original A2 executable bytes differ from Git: " + path)
    need(scalar(old, "rev-parse", "HEAD:" + ORIGINAL_TEST) == ORIGINAL_TEST_BLOB,
         "original historical A2 integration source was not preserved")


def dependency_bridge(current, old):
    """Reuse clean pinned dependency packages, NEVER current project oleans."""
    for name in PINS:
        original = git(old, "show", "HEAD:" + name)
        need(original == git(current, "show", "HEAD:" + name)
             and (old / name).read_bytes() == original
             and (current / name).read_bytes() == original,
             "historical/current dependency source differs: " + name)
    from localized_prefix_gate import check_dependencies
    before = check_dependencies(current)
    packages = current / ".lake/packages"
    need(packages.is_dir() and not packages.is_symlink(),
         "current pinned package directory missing or substituted")
    need(not (old / ".lake/build").exists()
         and not (old / ".lake/build").is_symlink(),
         "historical project build objects must start absent")
    link = old / ".lake/packages"
    need(not link.exists() and not link.is_symlink(),
         "historical dependency directory must start absent")
    link.parent.mkdir(parents=True, exist_ok=True)
    link.symlink_to(packages.resolve(), target_is_directory=True)
    need(check_dependencies(old) == before,
         "historical dependency bridge does not match original pins")
    return before


def validate_output(output, source_root, head, prefix, receipt_format, status):
    """Check real original receipts, artifact hashes and semantic diagnostics."""
    from localized_prefix_gate import DECLS, MUTATIONS
    from pr113_dual_a2_compiler_v2 import validate_run
    from pr113_semantic_receipt_v2 import validate_compiler_receipt_v2
    files = {}
    for path in output.iterdir():
        need(path.is_file() and not path.is_symlink()
             and path.stat().st_size <= 16 * 1024 * 1024,
             "unbounded or nonregular historical compiler artifact")
        files[prefix + "/" + path.name] = path.read_bytes()
    try:
        receipt, digest = validate_compiler_receipt_v2(
            files, prefix, status, MUTATIONS)
        validate_run(receipt, status, MUTATIONS, DECLS)
    except (ValueError, KeyError, TypeError) as exc:
        raise HistoricalReplayError(prefix + ": " + str(exc)) from exc
    source = receipt.get("source", {})
    need(source.get("git_head") == head
         and source.get("git_head_tree") == scalar(source_root, "rev-parse", "HEAD^{tree}")
         and receipt.get("mode") == "focused"
         and receipt.get("format") == receipt_format,
         "historical receipt belongs to a different source or compiler mode")
    return receipt, digest


def verify(repo, output, *, mode="focused"):
    """Fresh original AND current compilation; any missing leg fails."""
    need(mode == "focused", "unsupported original A2 engineering replay mode")
    current = Path(repo).resolve(strict=True)
    destination = Path(output).absolute()
    need(not destination.exists() and not destination.is_symlink()
         and not any(p.is_symlink() for p in destination.parents),
         "historical evidence output must be fresh and unsymlinked")
    destination = destination.resolve()
    need(not destination.is_relative_to(current)
         and not current.is_relative_to(destination),
         "historical evidence output overlaps current source")
    need(Path(scalar(current, "rev-parse", "--show-toplevel")).resolve() == current,
         "current replay source must be a real Git checkout root")
    checked = scalar(current, "rev-parse", "HEAD")
    unchanged(current, checked)
    git(current, "merge-base", "--is-ancestor", HISTORICAL_A2, checked)
    tree = scalar(current, "rev-parse", "HEAD^{tree}")
    destination.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix="pr113-original-A2-") as temporary:
        old = Path(temporary) / "checkout"
        added = False
        try:
            git(current, "worktree", "add", "--detach", str(old), HISTORICAL_A2)
            added = True
            unchanged(old, HISTORICAL_A2)
            verify_executors(current, old)
            packages = dependency_bridge(current, old)
            from pr113_dual_a2_compiler_v2 import run_historical_verified
            # Executes old/localized_prefix_gate.py in a NEW process. It
            # cannot import the current compiler or reuse current .lake/build.
            original_output = destination / "historical_original_A2"
            run_historical_verified(old, HISTORICAL_A2, original_output, mode)
            original, receipt_sha = validate_output(
                original_output, old, HISTORICAL_A2, "historical_original_A2",
                "Permansson.A2P02.CompilerReceipt.v2",
                "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING")
            unchanged(current, checked)
            # P-02's registered method must still establish CURRENT-source
            # compiler evidence; historical success alone cannot satisfy it.
            from pr113_a2_compiler_route_v3 import select_compiler
            selected = select_compiler(current)
            need(selected.checked_sha == checked,
                 "current A2 compiler selected for a different checkout")
            current_output = destination / "pr113_successor_A2"
            selected.module.verify(current, current_output, mode=mode)
            current_receipt, current_digest = validate_output(
                current_output, current, checked, "pr113_successor_A2",
                selected.receipt_format, "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING")
            from localized_prefix_gate import check_dependencies
            need(check_dependencies(current) == packages
                 and check_dependencies(old) == packages,
                 "dependency source changed during original A2 compilation")
            unchanged(old, HISTORICAL_A2)
            unchanged(current, checked)
            need(scalar(current, "rev-parse", "HEAD^{tree}") == tree,
                 "current source tree changed during historical replay")
            return {
                "format": FORMAT, "status": STATUS,
                "execution_scope": "HISTORICAL_A2_AND_CURRENT_SOURCE",
                "historical_source_sha": HISTORICAL_A2,
                "current_checked_sha": checked, "current_tree_sha": tree,
                "original_receipt_sha256": receipt_sha,
                "original_compiler_receipt": original,
                "current_compiler_receipt": current_receipt,
                "current_receipt_sha256": current_digest,
                "current_source_compiler_executed": True,
                "pinned_dependency_packages": packages,
                "historical_project_build_imported": False,
                "historical_executor_modified": False,
                "current_compiler_required_separately": True,
                "independent_security_review": False,
                "mathematical_acceptance": False,
                "merge_authorized": False,
            }
        finally:
            if added:
                git(current, "worktree", "remove", "--force", str(old))
