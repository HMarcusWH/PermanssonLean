"""Independent exact arithmetic verification of the C10 mixed-law report.

This verifies the full v2 receipt first; the mixed-law arithmetic is
independently recomputed using Fraction, not the producer's mixed_event
or eval_initial_law functions. JSON decoding remains outside Lean.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256

from c10_exact_execution import canonical_bytes, exact_fraction
from c10_verify_receipt import verify_receipt
from c10_eval_initial_law import (
    LAW_FORMAT, REPORT_FORMAT, BOUNDARY, InitialLawError, parse_strict_file,
)


def require(value: bool, message: str):
    if not value:
        raise InitialLawError(message)


def verify_initial_report(receipt: dict, law: dict, report: dict) -> bool:
    verify_receipt(receipt)
    require(receipt["format"] == "Permansson.C10.rational-margin.v2",
            "full-state v2 receipt required")
    require(isinstance(law, dict) and set(law) == {"format", "weights"},
            "invalid initial-law fields")
    require(law["format"] == LAW_FORMAT, "initial-law format mismatch")
    n = receipt["normalized_input"]["n"]
    require(isinstance(law["weights"], list) and len(law["weights"]) == n,
            "initial vector incomplete")
    try:
        weights = [exact_fraction(q) for q in law["weights"]]
    except ValueError as exc:
        raise InitialLawError("noncanonical mixed weight") from exc
    require(all(q >= 0 for q in weights) and sum(weights, Q(0)) == Q(1),
            "initial law invalid")
    normalized = {"format": LAW_FORMAT, "weights": [str(q) for q in weights]}
    require(isinstance(report, dict) and set(report) == {
        "format", "input_sha256", "receipt_sha256",
        "initial_law", "initial_sha256", "baseline_event", "members",
        "claim_boundary",
    }, "mixed-law report fields changed")
    require(report["format"] == REPORT_FORMAT, "mixed report format")
    require(report["input_sha256"] == receipt["input_sha256"], "input SHA changed")
    require(report["receipt_sha256"] == sha256(canonical_bytes(receipt)).hexdigest(),
            "mixed report attached to a different full receipt")
    require(report["initial_law"] == normalized, "mixed initial law changed")
    require(report["initial_sha256"] == sha256(canonical_bytes(normalized)).hexdigest(),
            "initial law digest changed")
    baseline_values = [Q(x) for x in receipt["baseline"]["event"]]
    baseline = sum((weights[i] * baseline_values[i] for i in range(n)), Q(0))
    require(report["baseline_event"] == str(baseline), "baseline mixed value wrong")
    require(isinstance(report["members"], list) and
            len(report["members"]) == len(receipt["members"]),
            "mixed menu incomplete")
    for item, claim in zip(receipt["members"], report["members"]):
        require(isinstance(claim, dict) and set(claim) == {
            "id", "event", "signed_change", "absolute_change",
        }, "mixed member schema")
        vals = [Q(x) for x in item["geometry"]["event"]]
        actual = sum((weights[i] * vals[i] for i in range(n)), Q(0))
        require(claim == {
            "id": item["id"], "event": str(actual),
            "signed_change": str(actual - baseline),
            "absolute_change": str(abs(actual - baseline)),
        }, "wrong mixed probability, effect, or menu identity")
    require(report["claim_boundary"] == BOUNDARY, "mixed query overclaims PR")
    return True


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt")
    parser.add_argument("initial_law")
    parser.add_argument("mixed_report")
    args = parser.parse_args(argv)
    verify_initial_report(
        parse_strict_file(args.receipt),
        parse_strict_file(args.initial_law),
        parse_strict_file(args.mixed_report),
    )
    print("C10 independent exact mixed-law check PASS (Python, not Lean)")


if __name__ == "__main__":
    main()
