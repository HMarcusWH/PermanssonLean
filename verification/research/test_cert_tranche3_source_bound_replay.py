"""Candidate-only Tranche 3 replay for frozen Q-05, F-01 and D-09 declarations.

This is *not* a research certification decision. The test runs the 30-declaration
source-bound probe under the repository's already-pinned Lean toolchain and
rejects source mutations, compiler errors, sorryAx and unexpected axioms.
No production, mathematical, workflow, or acceptance files are modified.
"""
from __future__ import annotations

import hashlib
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


class Tranche3PinnedReplay(unittest.TestCase):
    def test_frozen_sources_and_lean_pin_unchanged(self):
        self.assertEqual((ROOT / "lean-toolchain").read_text().strip(), "leanprover/lean4:v4.34.0")
        for relative, digest in EXPECTED_SHA256.items():
            source = ROOT / relative
            self.assertTrue(source.is_file(), relative)
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), digest, relative)

    def test_30_declaration_lean_probe(self):
        self.assertTrue(PROBE.is_file(), str(PROBE))
        contents = PROBE.read_text(encoding="utf-8")
        names = re.findall(r"^#check\s+(\S+)", contents, flags=re.M)
        axiom_names = re.findall(r"^#print axioms\s+(\S+)", contents, flags=re.M)
        self.assertEqual(len(names), 30)
        self.assertEqual(names, axiom_names)
        self.assertIsNotNone(shutil.which("lake"), "Pinned Lean compiler is required")
        result = subprocess.run(
            ["lake", "env", "lean", str(PROBE)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=900,
            check=False,
        )
        output = result.stdout + "\n" + result.stderr
        self.assertEqual(result.returncode, 0, output[-8000:])
        self.assertNotIn("error:", output.lower(), output[-8000:])
        self.assertNotIn("sorryAx", output, output[-8000:])
        for name in names:
            self.assertIn(name, output, name)
        groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
        self.assertTrue(groups, "Compiler produced no machine-auditable axiom output")
        for group in groups:
            observed = {name.strip() for name in group.split(",") if name.strip()}
            self.assertLessEqual(observed, ALLOWLIST, f"Unexpected axioms: {observed - ALLOWLIST}")


if __name__ == "__main__":
    unittest.main()
