"""Candidate-only Tranche 3 replay for frozen Q-05, F-01 and D-09 declarations.

This is *not* a research certification decision. The test runs the 30-declaration
source-bound probe under the repository's already-pinned Lean toolchain and
rejects source mutations, compiler errors, sorryAx and unexpected axioms.
No production, mathematical, workflow, or acceptance files are modified.
"""
from __future__ import annotations

import hashlib
import json
from collections import Counter
import re
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / "verification/research/tranche3_source_bound_probe.lean"
ALLOWLIST = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_SHA256 = {
    "PermanssonResearch/MultiAgent/AsymmetricCommonSwapFixture.lean": "4898ab0933ef34e8b253bc0ed060cf566120f7352b1358d655f4e4bea8c83861",
    "PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedProtocols.lean": "f9df90b8620562f1b559f1ad58cd34f322c6af4537cbf1683f379ac0e2bd7767",
    "PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean": "a6cd39ccf977b1b1610eb7657461928d32c937ee6ec757fb2f1cfbe541ab44a9",
    "PermanssonResearch/Quotient/Q05ActualAtomClosure.lean": "c75f429a9f066396e1e9754f85123acfcfa2794d4b3f5995b97dd1bb923417cb",
    "PermanssonResearch/Quotient/Q05ActualOriginalMarginWitnessFixture.lean": "bed57136586bf5f3f82ba30da6aa133d641954c361ed40d17a516510968beeb2",
    "PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean": "1df6e5b930e18de1f7e3922e3cb6abdc977e0cf9405cb678faeeac23b6eac140",
    "PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean": "7be49a5e7102de6fa8660bd1cc9f7545af04749ccaf8aa0209eee9a8550f3494",
}


def parse_axiom_receipt(output: str, expected_names: list[str]) -> dict[str, list[str]]:
    """Require a distinct transitive-axiom result for every requested declaration."""
    found = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
    entries = [(name, [a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()])
               for name, axioms in found]
    entries.extend((name, []) for name in clean)
    observed = [name for name, _ in entries]
    duplicates = sorted(name for name, count in Counter(observed).items() if count != 1)
    missing = sorted(set(expected_names) - set(observed))
    extra = sorted(set(observed) - set(expected_names))
    if duplicates or missing or extra or len(entries) != len(expected_names):
        raise AssertionError(
            f"Incomplete Lean axiom audit: missing={missing} extra={extra} "
            f"duplicates={duplicates} observed={len(entries)} "
            f"expected={len(expected_names)}"
        )
    records = {name: axioms for name, axioms in entries}
    for name, axioms in entries:
        unexpected = set(axioms) - ALLOWLIST
        if unexpected:
            raise AssertionError(f"Unexpected axiom(s) for {name}: {sorted(unexpected)}")
    return records


class Tranche3ParserTests(unittest.TestCase):
    """Fast, compiler-independent regression tests for receipt completeness."""

    def test_complete_with_and_without_axioms(self):
        sample = ("'A' depends on axioms: [propext, Quot.sound]\n"
                  "'B' does not depend on any axioms\n")
        self.assertEqual(parse_axiom_receipt(sample, ["A", "B"]),
                         {"A": ["propext", "Quot.sound"], "B": []})

    def test_missing_duplicate_and_extra_results_rejected(self):
        for output in (
            "'A' depends on axioms: [propext]\n",
            "'A' depends on axioms: [propext]\n'A' depends on axioms: [propext]\n"
            "'B' does not depend on any axioms\n",
            "'A' depends on axioms: [propext]\n'B' depends on axioms: [propext]\n"
            "'C' depends on axioms: [propext]\n",
        ):
            with self.subTest(output=output), self.assertRaises(AssertionError):
                parse_axiom_receipt(output, ["A", "B"])

    def test_unapproved_axiom_rejected(self):
        with self.assertRaisesRegex(AssertionError, "Unexpected axiom"):
            parse_axiom_receipt("'A' depends on axioms: [sorryAx]\n", ["A"])


class Tranche3PinnedReplay(unittest.TestCase):
    def test_probe_structure_and_import_order(self):
        contents = PROBE.read_text(encoding="utf-8")
        self.assertTrue(contents.startswith("import "),
                        "Lean import section must precede executable module comments")
        names = re.findall(r"^#check\s+(\S+)", contents, flags=re.M)
        axiom_names = re.findall(r"^#print axioms\s+(\S+)", contents, flags=re.M)
        self.assertEqual(len(names), 30)
        self.assertEqual(names, axiom_names)

    def test_frozen_sources_and_lean_pin_unchanged(self):
        self.assertEqual((ROOT / "lean-toolchain").read_text().strip(),
                         "leanprover/lean4:v4.34.0")
        for relative, digest in EXPECTED_SHA256.items():
            source = ROOT / relative
            self.assertTrue(source.is_file(), relative)
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(),
                             digest, relative)

    def test_30_declaration_lean_probe(self):
        self.assertTrue(PROBE.is_file(), str(PROBE))
        contents = PROBE.read_text(encoding="utf-8")
        self.assertTrue(contents.startswith("import "),
                        "Lean imports must precede module commands")
        names = re.findall(r"^#check\s+(\S+)", contents, flags=re.M)
        axiom_names = re.findall(r"^#print axioms\s+(\S+)", contents, flags=re.M)
        self.assertEqual(len(names), 30)
        self.assertEqual(names, axiom_names)
        self.assertIsNotNone(shutil.which("lake"), "Pinned Lean compiler is required")
        result = subprocess.run(
            ["lake", "env", "lean", str(PROBE)], cwd=ROOT,
            capture_output=True, text=True, timeout=900, check=False,
        )
        output = result.stdout + "\n" + result.stderr
        # Preserve full compiler output for reviewer diagnostics, including failures.
        print("TRANCHE3_LEAN_COMPILER_TRANSCRIPT_BEGIN", flush=True)
        print(output, flush=True)
        print("TRANCHE3_LEAN_COMPILER_TRANSCRIPT_END", flush=True)
        self.assertEqual(result.returncode, 0, output[-8000:])
        self.assertNotIn("error:", output.lower(), output[-8000:])
        self.assertNotIn("sorryAx", output, output[-8000:])
        for name in names:
            self.assertIn(name, output, name)
        records = parse_axiom_receipt(output, names)
        receipt = {
            "format": "Permansson.CERT.Tranche3.LeanAxiomEvidence.v1",
            "scope": "SOURCE_CANDIDATE_NOT_INDEPENDENT_ACCEPTANCE",
            "probe_sha256": hashlib.sha256(contents.encode("utf-8")).hexdigest(),
            "compiler_output_sha256": hashlib.sha256(output.encode("utf-8")).hexdigest(),
            "compiler_exit_code": result.returncode,
            "declaration_count": len(records),
            "declarations": [{"name": n, "axioms": records[n]} for n in names],
        }
        print("TRANCHE3_LEAN_AXIOM_RECEIPT_BEGIN", flush=True)
        print(json.dumps(receipt, sort_keys=True), flush=True)
        print("TRANCHE3_LEAN_AXIOM_RECEIPT_END", flush=True)


if __name__ == "__main__":
    unittest.main()
