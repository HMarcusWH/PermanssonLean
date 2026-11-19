"""Candidate-only verification of the conditional original Q-05 margin bridge.

This test NEVER claims that the separate whole-path identification predicates
are proved. The bridge is useful only after their hypotheses are discharged.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / "verification/research/tranche5_q05_conditional_original_margin_bridge.lean"
NAMESPACE = "PermanssonResearch.Quotient.Q05ConditionalExactMargin"
EXPECTED = [
    NAMESPACE + ".fine_original_effect_of_path_identification",
    NAMESPACE + ".coarse_original_effect_of_path_identification",
    NAMESPACE + ".fine_original_margin_of_path_identification",
    NAMESPACE + ".coarse_original_margin_of_path_identification",
    NAMESPACE + ".original_margin_gap_of_path_identification",
]
ALLOWLIST = {"propext", "Classical.choice", "Quot.sound"}
SOURCE_SHA256 = {
    "PermanssonResearch/Quotient/Q05ActualOriginalMarginWitnessFixture.lean":
        "bed57136586bf5f3f82ba30da6aa133d641954c361ed40d17a516510968beeb2",
    "PermanssonResearch/Quotient/Q05ActualOriginalMarginAdapter.lean":
        "1c14ac82af8409ba639db17760fdb53c08ab266ed01cbb25b229f90e92339da8",
    "PermanssonResearch/Quotient/Q05ActualAtomClosure.lean":
        "c75f429a9f066396e1e9754f85123acfcfa2794d4b3f5995b97dd1bb923417cb",
}


def parse_complete_receipt(text: str) -> dict[str, list[str]]:
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    entries = [(name, [x.strip() for x in xs.replace("\n", " ").split(",") if x.strip()])
               for name, xs in matches]
    entries += [(x, []) for x in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    names = [x for x, _ in entries]
    if len(names) != len(EXPECTED) or set(names) != set(EXPECTED) or len(set(names)) != len(names):
        raise AssertionError(f"Incomplete Q-05 conditional audit: {names!r}")
    for name, axioms in entries:
        if not set(axioms) <= ALLOWLIST:
            raise AssertionError(f"Disallowed axioms for {name}: {axioms}")
    return dict(entries)


class Q05ConditionalMarginBridge(unittest.TestCase):
    def test_frozen_source_and_explicit_unproven_hypothesis_scope(self):
        self.assertEqual((ROOT / "lean-toolchain").read_text().strip(),
                         "leanprover/lean4:v4.34.0")
        for p, digest in SOURCE_SHA256.items():
            self.assertEqual(hashlib.sha256((ROOT / p).read_bytes()).hexdigest(), digest, p)
        source = PROBE.read_text()
        self.assertTrue(source.startswith("import "))
        names = re.findall(r"^#check\s+(\S+)", source, flags=re.M)
        audited = re.findall(r"^#print axioms\s+(\S+)", source, flags=re.M)
        self.assertEqual(names, EXPECTED)
        self.assertEqual(audited, EXPECTED)
        for marker in ("def FineWholePathIdentified : Prop", "def CoarseWholePathIdentified : Prop",
                       "(hf : FineWholePathIdentified)", "(hc : CoarseWholePathIdentified)"):
            self.assertIn(marker, source)
        for forbidden in ("sorry", "admit", "axiom "):
            # a comment may describe these terms; inspect code lines only
            code = "\n".join(line for line in source.splitlines() if line.strip().startswith(("theorem ", "def ", "noncomputable def ", "by", "  exact", "  rw", "  simp")))
            self.assertNotIn(forbidden, code)

    def test_compiled_lean_conditional_bridges_and_axioms(self):
        self.assertIsNotNone(shutil.which("lake"), "Pinned Lean compiler required")
        run = subprocess.run(["lake", "env", "lean", str(PROBE)],
                             cwd=ROOT, capture_output=True, text=True,
                             timeout=900, check=False)
        output = run.stdout + "\n" + run.stderr
        print("TRANCHE5_Q05_LEAN_TRANSCRIPT_BEGIN", flush=True)
        print(output, flush=True)
        print("TRANCHE5_Q05_LEAN_TRANSCRIPT_END", flush=True)
        self.assertEqual(run.returncode, 0, output[-10000:])
        self.assertNotIn("error:", output.lower())
        self.assertNotIn("sorryAx", output)
        self.assertIn("FineWholePathIdentified", output)
        self.assertIn("CoarseWholePathIdentified", output)
        records = parse_complete_receipt(output)
        receipt = {"format": "Permansson.CERT.Q05ConditionalMarginBridge.v1",
                   "scope": "UNPROVED_WHOLE_PATH_IDENTIFICATION_REQUIRED",
                   "exit_code": run.returncode,
                   "compiler_output_sha256": hashlib.sha256(output.encode()).hexdigest(),
                   "probe_sha256": hashlib.sha256(PROBE.read_bytes()).hexdigest(),
                   "names": [{"name": n, "axioms": records[n]} for n in EXPECTED]}
        print("TRANCHE5_Q05_RECEIPT_BEGIN", flush=True)
        print(json.dumps(receipt, sort_keys=True), flush=True)
        print("TRANCHE5_Q05_RECEIPT_END", flush=True)


if __name__ == "__main__":
    unittest.main()
