"""Strict rational C10 initial-law query; never an original B1 optimizer.

Usage:
  python3 verification/research/c10_eval_initial_law.py RECEIPT INITIAL_LAW -o REPORT
Input schema:
  {"format":"Permansson.C10.initial-law.v1","weights":["1/2","1/2",...]}
A v2 point-start receipt is validated in full before evaluation.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from typing import Any

from c10_exact_execution import canonical_bytes, exact_fraction, strict_object
from c10_verify_receipt import verify_receipt, ReceiptError

LAW_FORMAT = "Permansson.C10.initial-law.v1"
REPORT_FORMAT = "Permansson.C10.mixed-law.v1"
BOUNDARY = (
    "Exact rational initial-law event probabilities only. This mixed-law "
    "difference is NOT the original B1 pointwise constitutive margin "
    "and supplies no original Exact GR or external model identification."
)


class InitialLawError(ValueError):
    pass


def parse_initial_law(obj: Any, n: int) -> tuple[Fraction, ...]:
    if not isinstance(obj, dict) or set(obj) != {"format", "weights"}:
        raise InitialLawError("invalid initial-law object/fields")
    if obj["format"] != LAW_FORMAT:
        raise InitialLawError("unsupported initial-law format")
    raw = obj["weights"]
    if not isinstance(raw, list) or len(raw) != n:
        raise InitialLawError("initial weights must cover every state")
    try:
        weights = tuple(exact_fraction(v) for v in raw)
    except ValueError as exc:
        raise InitialLawError("invalid canonical rational initial weight") from exc
    if any(w < 0 for w in weights) or sum(weights, Fraction(0)) != 1:
        raise InitialLawError("initial law must be nonnegative and sum to exactly 1")
    return weights


def mixed_event(weights: tuple[Fraction, ...], values: list[str]) -> Fraction:
    if len(weights) != len(values):
        raise InitialLawError("law/event-vector dimension mismatch")
    return sum((w * Fraction(value) for w, value in zip(weights, values)),
               Fraction(0))


def eval_initial_law(receipt: dict, law: dict) -> dict:
    verify_receipt(receipt)
    if receipt["format"] != "Permansson.C10.rational-margin.v2":
        raise InitialLawError("mixed-law release requires full-state v2 receipt")
    n = receipt["normalized_input"]["n"]
    weights = parse_initial_law(law, n)
    canonical_law = {"format": LAW_FORMAT, "weights": [str(x) for x in weights]}
    baseline = mixed_event(weights, receipt["baseline"]["event"])
    members = []
    for item in receipt["members"]:
        probability = mixed_event(weights, item["geometry"]["event"])
        members.append({
            "id": item["id"], "event": str(probability),
            "signed_change": str(probability - baseline),
            "absolute_change": str(abs(probability - baseline)),
        })
    return {
        "format": REPORT_FORMAT,
        "input_sha256": receipt["input_sha256"],
        "receipt_sha256": sha256(canonical_bytes(receipt)).hexdigest(),
        "initial_law": canonical_law,
        "initial_sha256": sha256(canonical_bytes(canonical_law)).hexdigest(),
        "baseline_event": str(baseline),
        "members": members,
        "claim_boundary": BOUNDARY,
    }


def parse_strict_file(path: str | Path) -> dict:
    with Path(path).open(encoding="utf-8") as f:
        return json.load(
            f, object_pairs_hook=strict_object,
            parse_float=lambda _: (_ for _ in ()).throw(
                InitialLawError("JSON floating point forbidden")),
        )


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt")
    parser.add_argument("initial_law")
    parser.add_argument("-o", "--output", required=True)
    args = parser.parse_args(argv)
    report = eval_initial_law(parse_strict_file(args.receipt),
                              parse_strict_file(args.initial_law))
    with Path(args.output).open("w", encoding="utf-8") as f:
        json.dump(report, f, sort_keys=True, indent=2, ensure_ascii=False)
        f.write("\n")
    print("C10 exact initial mixture PASS: " +
          str(len(report["members"])) + " listed kernels; not a B1 margin")


if __name__ == "__main__":
    main()
