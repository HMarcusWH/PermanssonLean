"""Independently recheck C10 release provenance and kernel-checkable data.

A matching self-reported hash is insufficient. The expected source identity
comes from the actual checkout and a trusted GitHub pull-request event, the
numeric receipt is recomputed, the generated Lean source is regenerated, and
the Lean compiler is rerun for the release-grade CLI check.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess

from c10_exact_execution import check_input
from c10_golden import six_input
from c10_emit_golden_bridge import emit_golden_bridge
from c10_verify_receipt import verify_receipt
from c10_release_evidence import (
    ARTIFACTS, SUMMARY_TEXT, EvidenceError, ROOT, axiom_reports, make_manifest,
    require, strict_json, trusted_ci_context, stable_json, verify_source_checkout,
)


def verify_bundle_structure(directory: Path, expected_source: dict,
                            root: Path = ROOT) -> bool:
    """Structural/checker verification; NOT proof of execution by itself."""
    actual = strict_json(directory / "evidence_manifest.json")
    expected = make_manifest(directory, expected_source, root)
    require(actual == expected,
            "manifest identity, fixed trust boundary, source or artifact digest mismatch")
    expected_names = set(ARTIFACTS) | {"evidence_manifest.json"}
    require({entry.name for entry in directory.iterdir()} == expected_names,
            "unexpected or missing source-bound release artifact")
    require((directory / "verification_summary.txt").read_bytes() ==
            SUMMARY_TEXT.encode("utf-8"),
            "human-readable boundary statement does not match the audited release")
    normalized = strict_json(directory / "normalized_input.json")
    raw = strict_json(directory / "input.json")
    receipt = strict_json(directory / "receipt.json")
    require(receipt.get("format") == "Permansson.C10.rational-margin.v2",
            "source-bound release requires complete full-state v2 receipt")
    require(check_input(raw).canonical() == normalized,
            "raw and normalized numeric input disagree")
    require(normalized == check_input(six_input()).canonical(),
            "normalized input differs from original six-state fixture")
    require(receipt["normalized_input"] == normalized,
            "receipt bound to different normalized input")
    require(verify_receipt(receipt), "independent numerical receipt check failed")
    require(
        (directory / "normalized_input.json").read_bytes() == stable_json(normalized),
        "normalized input serialization changed",
    )
    regenerated = emit_golden_bridge(receipt).encode("utf-8")
    require((directory / "C10ReifiedGolden.lean").read_bytes() == regenerated,
            "Lean source does not exactly reify the receipt and original bridge")
    axiom_reports((directory / "lean_check.stdout.txt").read_text(encoding="utf-8"))
    return True


def verify_release_bundle(directory: Path, expected_source: dict,
                          root: Path = ROOT, *, rerun_lean: bool = True) -> bool:
    verify_source_checkout(root, expected_source["synthetic_merge_sha"])
    verify_bundle_structure(directory, expected_source, root)
    if not rerun_lean:
        # Structural integrity only, deliberately NOT release-grade evidence.
        return True
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", str((directory / "C10ReifiedGolden.lean").resolve())],
            cwd=root, capture_output=True, text=True, timeout=600, check=False,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
        raise EvidenceError("Lean compiler unavailable or timed out during recheck") from exc
    require(completed.returncode == 0,
            "independent generated Lean rerun failed: " +
            (completed.stdout + completed.stderr)[-4000:])
    axiom_reports(completed.stdout)
    verify_source_checkout(root, expected_source["synthetic_merge_sha"])
    return True


def main(argv=None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--event-file", type=Path, required=True)
    parser.add_argument("--repository", required=True)
    args = parser.parse_args(argv)
    context = trusted_ci_context(args.event_file, args.repository)
    verify_release_bundle(args.directory, context, rerun_lean=True)
    print("C10 source-bound proof evidence PASS: " + context["head_sha"])


if __name__ == "__main__":
    main()
