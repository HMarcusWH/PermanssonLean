"""Fail-closed legacy receipt dialect migration into UNVERIFIED candidates.

Never turn old schema fields, free-form axiom lists or source_ci_receipts
into v2 authenticated evidence. A real compiler run, live CI check ID and
external non-author exact-H review are required after candidate migration.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys

from final_closure_case_receipts import ROOT

SHA256 = re.compile(r"^[0-9a-f]{64}$")


class MigrationError(ValueError):
    pass


def statement_candidate(old: dict):
    if not isinstance(old, dict):
        raise MigrationError("old statement must be an object")
    source = old.get("source_sha256")
    declared = old.get("statement_sha256")
    if not (isinstance(source, str) and SHA256.fullmatch(source) and
            isinstance(declared, str) and SHA256.fullmatch(declared)):
        raise MigrationError("missing authentic historical bytes")
    if not isinstance(old.get("declaration"), str) or not old["declaration"]:
        raise MigrationError("missing named historical declaration")
    axioms = old.get("axiom_allowlist")
    if axioms is not None and not isinstance(axioms, list):
        raise MigrationError("malformed legacy allowed axiom list")
    return {
        "format": "Permansson.LegacyStatementReviewCandidate.v2",
        "declaration": old["declaration"],
        "path": old.get("path"),
        "head_sha_candidate": old.get("reviewed_head_sha"),
        "source_sha256": source,
        "statement_sha256": declared,
        "untrusted_legacy_axiom_allowlist": axioms,
        "untrusted_legacy_compiler_run_url": old.get("compiler_run_url"),
        "transitive_axioms": None,
        "compiler_result": "NOT_VERIFIED",
        "compiler_check": None,
        "check_run_id": None,
        "semantic_negative_receipts": [],
        "independent_review_receipts": [],
        "status": "LEGACY_SOURCE_CANDIDATE_ONLY_NOT_ACCEPTED",
    }


def source_receipt_candidate(old: dict):
    if not isinstance(old, dict) or not old.get("base_sha"):
        raise MigrationError("legacy source template lacks baseline")
    return {
        "format": "Permansson.LegacySourceReceiptCandidate.v2",
        "base_sha_candidate": old["base_sha"],
        "head_sha_candidate": old.get("head_sha"),
        "synthetic_sha_candidate": old.get("synthetic_sha"),
        "merged_sha_candidate": old.get("merged_main_sha"),
        "unverified_legacy_ci_receipts": old.get("source_ci_receipts", []),
        "source_bound_ci": [],
        "compiler_axiom_receipts": [],
        "semantic_negative_receipts": [],
        "independent_source_reviews": [],
        "status": "UNVERIFIED_LEGACY_SOURCE_TEMPLATE",
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--type", choices=["statement", "source"], required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    if args.output.resolve().is_relative_to(ROOT.resolve()):
        print("MIGRATION BLOCKED: output must be detached from source HEAD")
        return 2
    try:
        old = json.loads(args.input.read_text())
        result = (statement_candidate(old) if args.type == "statement"
                  else source_receipt_candidate(old))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    except (OSError, ValueError) as exc:
        print("MIGRATION BLOCKED:", exc)
        return 2
    print(json.dumps({"status": result["status"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
