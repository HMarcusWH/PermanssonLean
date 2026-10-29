"""Source-bound current A2 semantic receipt validation (synthetic fixtures).

Mocks no verifier. Real original historical T/A2 CI and human review remain
separate required evidence and none of these tests authorizes a migration.
"""
from __future__ import annotations

import copy
import hashlib
import json
import unittest

import infrastructure_acceptance as legacy
import pr113_semantic_receipt_v2 as current
from localized_prefix_gate import MUTATIONS as HIST, mutated_source as mutate_hist
from pr113_a2_successor_compiler import (
    MUTATIONS as SUCC, mutated_source as mutate_succ,
)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def fixture(prefix, mutations, mutate, *, mode="focused"):
    # Artificial source containing only the four specific mutation anchors.
    positive = "\n".join(old for old, new in mutations.values()).encode("utf-8")
    all_files = {prefix + "/PositiveControl.lean": positive}
    cmds = []
    items = {}
    labels = (["compiler_version", "research_build", "source_1", "source_2",
               "source_3", "source_4", "signatures_axioms", "positive_fixture"]
              + (["original_default_build"] if mode == "full" else [])
              + list(mutations))
    for i, label in enumerate(labels, 1):
        mutant = label in mutations
        raw = (
            ("/detached/" + label + ".lean:20:5: error: unsolved goals\n"
             + "⊢ False\n").encode("utf-8")
            if mutant else b"source verified\n")
        filename = f"{i:02d}_{label}.log"
        all_files[prefix + "/" + filename] = raw
        cmds.append({
            "label": label, "returncode": 1 if mutant else 0,
            "log": filename, "log_sha256": digest(raw),
        })
    for label in mutations:
        source = mutate(positive.decode("utf-8"), label).encode("utf-8")
        all_files[prefix + "/" + label + ".lean"] = source
        items[label] = {
            "status": "SEMANTICALLY_REJECTED",
            "positive_source_sha256": digest(positive),
            "mutant_source_sha256": digest(source),
        }
    row = {
        "status": ("LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING"
                   if prefix == "historical_original_A2"
                   else "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING"),
        "mode": mode, "source_unchanged": True,
        "declarations": {"synthetic.fixture": ["propext"]},
        "mutations": items, "commands": cmds,
        "artifacts": {},
    }
    for full_path, raw in all_files.items():
        row["artifacts"][full_path.removeprefix(prefix + "/")] = {
            "sha256": digest(raw), "bytes": len(raw),
        }
    all_files[prefix + "/receipt.json"] = (
        json.dumps(row, sort_keys=True) + "\n").encode("utf-8")
    return all_files


class A2ReceiptSemanticTests(unittest.TestCase):
    def _valid(self, prefix="historical_original_A2", *, mode="focused"):
        mutations, mutate = (
            (HIST, mutate_hist) if prefix == "historical_original_A2"
            else (SUCC, mutate_succ))
        return fixture(prefix, mutations, mutate, mode=mode)

    def _check(self, files, prefix="historical_original_A2"):
        expected = HIST if prefix == "historical_original_A2" else SUCC
        return current.validate_compiler_receipt_v2(
            files, prefix,
            ("LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING"
             if prefix == "historical_original_A2"
             else "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING"),
            expected)

    def test_genuine_four_source_probes_are_required_and_accepted(self):
        for prefix in ("historical_original_A2", "pr113_successor_A2"):
            for mode in ("focused", "full"):
                with self.subTest(prefix=prefix, mode=mode):
                    self._check(self._valid(prefix, mode=mode), prefix)

    def test_source_probe_missing_or_duplicate_rejected(self):
        files = self._valid()
        prefix = "historical_original_A2"
        for change in ("drop", "duplicate"):
            bad = copy.deepcopy(files)
            receipt = json.loads(bad[prefix + "/receipt.json"])
            if change == "drop":
                receipt["commands"] = [
                    x for x in receipt["commands"] if x["label"] != "source_4"]
            else:
                receipt["commands"].append(receipt["commands"][0])
            bad[prefix + "/receipt.json"] = json.dumps(receipt).encode()
            with self.subTest(change=change), self.assertRaises(
                    legacy.InfrastructureError):
                self._check(bad)

    def test_mutant_source_must_be_exact_intended_single_change(self):
        files = self._valid()
        prefix = "historical_original_A2"
        name = "wrong_reported_effect"
        filename = prefix + "/" + name + ".lean"
        files[filename] += b"\n-- unrelated source edit\n"
        receipt = json.loads(files[prefix + "/receipt.json"])
        receipt["mutations"][name]["mutant_source_sha256"] = digest(files[filename])
        receipt["artifacts"][name + ".lean"] = {
            "bytes": len(files[filename]), "sha256": digest(files[filename])}
        files[prefix + "/receipt.json"] = json.dumps(receipt).encode()
        with self.assertRaises(legacy.InfrastructureError):
            self._check(files)

    def test_wrong_named_mutant_parser_or_import_error_not_accepted(self):
        for output in (
            b"/detached/wrong_reported_effect.lean:20:5: error: unknown module\n",
            b"/detached/wrong_reported_effect.lean:20:5: error: unexpected token\n",
            b"some_other_file.lean:20:5: error: unsolved goals\n",
            b"/detached/wrong_reported_effect.lean:20:5: error: timeout\n",
        ):
            files = self._valid()
            prefix = "historical_original_A2"
            row = json.loads(files[prefix + "/receipt.json"])
            entry = next(c for c in row["commands"]
                         if c["label"] == "wrong_reported_effect")
            key = prefix + "/" + entry["log"]
            files[key] = output
            entry["log_sha256"] = digest(output)
            row["artifacts"][entry["log"]] = {
                "sha256": digest(output), "bytes": len(output)}
            files[prefix + "/receipt.json"] = json.dumps(row).encode()
            with self.subTest(output=output), self.assertRaises(
                    legacy.InfrastructureError):
                self._check(files)


if __name__ == "__main__":
    unittest.main()
