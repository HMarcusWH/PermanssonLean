"""Exact positive PR80 replay baseline; introduction is provenance, not success.

The initial A2 commit is preserved as failed/pre-compilation history. Positive
replay uses PR80's corrected final head, with its own original executor bytes.
A past green run identifies the baseline; it never replaces a fresh execution,
independent review, or permission to merge/publish.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess

INTRODUCER = "f71a76032b169aac7bfe0694aa715339a94d4e05"
REPLAY_HEAD = "55f872abddfbbd8eaa996f3c95f91e15a5ea421a"
REPLAY_TREE = "00f199d7c3e275f76b39d85c9fb5cacd67f5282a"
MERGED_PR80 = "8f807660bcbea3f9d29129d1bb85645ce50c3249"
HISTORICAL_GREEN_RUN = 39166505301
FORMAT = "Permansson.PR113.PositiveHistoricalA2Baseline.v1"
DUAL_FORMAT = "Permansson.PR113.DualA2CompilerCandidate.v4"
EXECUTORS = {
    "verification/research/localized_prefix_gate.py":
        "6f15dca74895e59a4d4bfcb54d38b471a1798be3",
    "verification/research/localized_prefix_support.py":
        "b07bc7d3b9ebe55b131466aebc28149fa2f03228",
}
ORIGINAL_TEST = "verification/research/test_localized_prefix_compiler.py"
ORIGINAL_TEST_BLOB = "c0f49038ea9b590720c78be85968eb63f5ac820f"
PROOF_PATHS = (
    "PermanssonResearch/Probability/GoodHistoryVisit.lean",
    "PermanssonResearch/Probability/LocalizedFinitePrefix.lean",
    "PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean",
    "PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean",
)
PIN_PATHS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")


class HistoricalBaselineError(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise HistoricalBaselineError(message)


def git(root, *args):
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "-c", "core.hooksPath=/dev/null", *args],
            capture_output=True, timeout=90, check=False)
    except (OSError, subprocess.SubprocessError) as exc:
        raise HistoricalBaselineError("historical baseline Git unavailable") from exc
    need(result.returncode == 0,
         "historical baseline Git failed: " + repr(args[:3]) + ": " +
         result.stderr.decode("utf-8", "replace")[-1200:])
    return result.stdout


def text(root, *args):
    return git(root, *args).decode("ascii").strip()


def blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()


def verify_positive_source(root):
    """Authenticate the complete pinned commit/tree and its execution surface."""
    original = Path(root)
    need(not original.is_symlink() and
         not any(p.is_symlink() for p in original.absolute().parents),
         "historical baseline cannot traverse symlinks")
    root = original.resolve(strict=True)
    need(Path(text(root, "rev-parse", "--show-toplevel")).resolve() == root,
         "historical baseline must be the real checkout root")
    need(text(root, "rev-parse", "HEAD") == REPLAY_HEAD,
         "positive A2 replay requires corrected PR80 head, not introduction")
    need(text(root, "rev-parse", "HEAD^{tree}") == REPLAY_TREE,
         "positive historical A2 tree differs from the pinned PR80 tree")
    git(root, "merge-base", "--is-ancestor", INTRODUCER, REPLAY_HEAD)
    need(not git(root, "status", "--porcelain=v1", "--untracked-files=all"),
         "positive historical A2 source is dirty")
    pins = {**EXECUTORS, ORIGINAL_TEST: ORIGINAL_TEST_BLOB}
    paths = (*pins, *PIN_PATHS, *PROOF_PATHS, "PermanssonResearch.lean")
    measured = {}
    for path in paths:
        entry = git(root, "ls-tree", "HEAD", "--", path).rstrip(b"\n")
        need(b"\t" in entry, "historical source missing: " + path)
        meta, member = entry.split(b"\t", 1)
        fields = meta.decode("ascii").split()
        need(len(fields) == 3 and fields[:2] == ["100644", "blob"]
             and member.decode("utf-8") == path,
             "historical source has unexpected type/mode: " + path)
        raw = git(root, "show", "HEAD:" + path)
        file = root / path
        need(file.is_file() and not file.is_symlink()
             and not any(p.is_symlink() for p in file.parents)
             and file.read_bytes() == raw and blob(raw) == fields[2],
             "historical source bytes differ from pinned Git: " + path)
        need(path not in pins or fields[2] == pins[path],
             "original historical executor/test changed: " + path)
        measured[path] = fields[2]
    return {
        "format": FORMAT, "introduction_sha": INTRODUCER,
        "positive_replay_sha": REPLAY_HEAD, "positive_replay_tree": REPLAY_TREE,
        "source_blobs": measured, "fresh_compiler_execution": False,
        "independent_security_review": False, "mathematical_acceptance": False,
    }


def require_runtime_success(returncode, receipt):
    """Expose compiler failures separately from later source-authentication checks."""
    need(type(receipt) is dict, "historical runtime receipt is not an object")
    if type(returncode) is not int or returncode != 0 or receipt.get("status") != "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING":
        commands = receipt.get("commands", [])
        commands = commands if isinstance(commands, list) else []
        expected_negatives = {
            "omit_baseline_reporting_error", "omit_treated_reporting_error",
            "omit_zero_horizon_initial_error", "wrong_reported_effect",
        }
        failed = [c for c in commands if isinstance(c, dict)
                  and type(c.get("returncode")) is int and c["returncode"] != 0
                  and c.get("label") not in expected_negatives]
        last = failed[-1] if failed else {}
        # Preserve the original raw receipt/logs. This is a bounded diagnostic,
        # not a synthetic replacement receipt or an accepted semantic failure.
        reason = str(receipt.get("reason", "missing successful historical compiler receipt"))[:6000]
        raise HistoricalBaselineError(
            "HISTORICAL_A2_COMPILER_FAILED: process_exit=" + str(returncode)
            + "; command=" + str(last.get("label", "unknown"))
            + "; command_exit=" + str(last.get("returncode", "unknown"))
            + "; log=" + str(last.get("log", "unknown")) + "; " + reason)


def verify_receipt_source(receipt):
    need(type(receipt) is dict and type(receipt.get("source")) is dict,
         "historical compiler receipt source missing")
    source = receipt["source"]
    need(receipt.get("format") == "Permansson.A2P02.CompilerReceipt.v2"
         and receipt.get("status") == "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING"
         and source.get("git_head") == REPLAY_HEAD
         and source.get("git_head_tree") == REPLAY_TREE
         and receipt.get("source_unchanged") is True,
         "HISTORICAL_A2_SOURCE_MISMATCH: corrected PR80 head/tree not authenticated")
