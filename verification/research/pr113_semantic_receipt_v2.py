"""Stricter current v2 A2 producer receipt validator; not historical source.

Validate the *actual* compiler diagnostics, not merely returncode!=0 and the
literal word "error". The original frozen historical executor is unchanged.
"""
from __future__ import annotations

import hashlib
from pathlib import PurePosixPath

import infrastructure_acceptance as legacy
from localized_prefix_gate import semantic_rejection as historical_rejection
from pr113_a2_successor_compiler import semantic_rejection as successor_rejection


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def validate_compiler_receipt_v2(files, prefix, expected_status, expected_mutations):
    row, receipt_sha = legacy.verify_compiler_receipt(
        files, prefix, expected_status, expected_mutations)
    mandatory = set(expected_mutations) | {
        "compiler_version", "research_build", "signatures_axioms",
        "positive_fixture",
    }
    optional = {"original_default_build"}
    commands = row["commands"]
    names = [entry.get("label") for entry in commands]
    legacy.need(len(names) == len(set(names))
                and mandatory <= set(names)
                and set(names) <= mandatory | optional,
                "A2 command identities are missing, repeated or unrecognized")
    positive_path = prefix + "/PositiveControl.lean"
    legacy.need(positive_path in files
                and len(files[positive_path]) > 0,
                "A2 positive fixture original bytes missing")
    positive_sha = sha(files[positive_path])
    for mutant, substitution in expected_mutations.items():
        entry = row["mutations"][mutant]
        source_path = prefix + "/" + mutant + ".lean"
        legacy.need(source_path in files
                    and entry.get("positive_source_sha256") == positive_sha
                    and entry.get("mutant_source_sha256") == sha(files[source_path])
                    and files[source_path] != files[positive_path],
                    "A2 mutant bytes not bound to the positive source")
    rejection = (historical_rejection if prefix == "historical_original_A2"
                 else successor_rejection)
    for command in commands:
        label = command["label"]
        if label not in expected_mutations:
            legacy.need(command["returncode"] == 0,
                        "A2 positive/setup control not successful")
            continue
        log_path = prefix + "/" + command["log"]
        log = files[log_path].decode("utf-8", errors="replace")
        # Reject unrelated errors from appended or imported source. Lean's
        # diagnostics identify the source filename, which must be this mutant.
        marker = label + ".lean:"
        legacy.need(marker in log,
                    "A2 negative error is not from the named mutant fixture")
        try:
            accepted = rejection(command["returncode"], log)
        except Exception as exc:
            raise legacy.InfrastructureError(
                "A2 negative failed for setup/parser/resource reason") from exc
        legacy.need(accepted, "A2 negative lacked a semantic proof failure")
    return row, receipt_sha
