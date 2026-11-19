"""Additive Q-05 source-guard repair and canonical-output compiler evidence.

The historical Tranche 5 files remain unchanged.  These checks supplement its
incomplete line-prefix guard and compile the new whole-path and full-domain
margin proofs.  Successful execution is technical evidence, not independent
case acceptance or an Exact-GR claim.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

from verification.research.test_cert_tranche3_source_bound_replay import parse_axiom_receipt

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path("verification/research")
SOURCE_SHA256 = {
    "PermanssonResearch/Quotient/Q05ActualOriginalMarginWitnessFixture.lean":
        "bed57136586bf5f3f82ba30da6aa133d641954c361ed40d17a516510968beeb2",
    "PermanssonResearch/Quotient/Q05ActualOriginalMarginAdapter.lean":
        "1c14ac82af8409ba639db17760fdb53c08ab266ed01cbb25b229f90e92339da8",
    "PermanssonResearch/Quotient/Q05ActualAtomClosure.lean":
        "c75f429a9f066396e1e9754f85123acfcfa2794d4b3f5995b97dd1bb923417cb",
}
STAGES = (
    ("tranche5_q05_conditional_margin_correction_addendum", "Q05ConditionalExactMargin", (
        "fine_original_effect_of_path_identification",
        "coarse_original_effect_of_path_identification",
        "fine_original_margin_of_path_identification",
        "coarse_original_margin_of_path_identification",
        "original_margin_gap_of_path_identification",
    )),
    ("tranche6_q05_whole_path_identification", "Q05WholePathIdentification", (
        "fine_whole_path_output", "coarse_whole_path_output",
    )),
    ("tranche7_q05_original_margin_addendum", "Q05OriginalMarginClosure", (
        "fine_whole_path_identified", "coarse_whole_path_identified",
        "fine_original_effect", "coarse_original_effect",
        "fine_original_margin", "coarse_original_margin", "original_margin_gap",
    )),
)


def lean_code_without_comments_or_strings(source: str) -> str:
    """Mask nested Lean comments and string literals, preserving line breaks."""
    out = list(source)
    i, depth, in_string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i+2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i:i+2] = "  "
                depth -= 1
                i += 2
            else:
                out[i] = "\n" if source[i] == "\n" else " "
                i += 1
        elif in_string:
            if source[i] == "\\" and i + 1 < len(source):
                out[i:i+2] = "  "
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                out[i] = "\n" if source[i] == "\n" else " "
                i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            j = len(source) if j < 0 else j
            out[i:j] = " " * (j-i)
            i = j
        elif source.startswith("/-", i):
            out[i:i+2] = "  "
            depth = 1
            i += 2
        elif source[i] == '"':
            out[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    if depth or in_string:
        raise AssertionError("Unterminated Lean comment or string")
    return "".join(out)


def require_no_proof_placeholders_or_axiom_commands(source: str) -> None:
    code = lean_code_without_comments_or_strings(source)
    found = re.search(r"(?<![\w'])(sorry|admit|axiom)(?![\w'])", code)
    if found:
        raise AssertionError("Forbidden Lean code token: " + found.group(1))


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class Q05SourceGuardAddendum(unittest.TestCase):
    def test_frozen_sources_and_all_probe_code(self):
        self.assertEqual((ROOT / "lean-toolchain").read_text().strip(),
                         "leanprover/lean4:v4.34.0")
        for name, expected in SOURCE_SHA256.items():
            self.assertEqual(digest((ROOT / name).read_bytes()), expected, name)
        for stem, namespace, declarations in STAGES:
            with self.subTest(probe=stem):
                source = (ROOT / DIRECTORY / (stem + ".lean")).read_text()
                require_no_proof_placeholders_or_axiom_commands(source)
                self.assertTrue(source.startswith("import "))
                expected = ["PermanssonResearch.Quotient." + namespace + "." + d
                            for d in declarations]
                self.assertEqual(re.findall(r"^#check\s+(\S+)", source, re.M), expected)
                self.assertEqual(re.findall(r"^#print axioms\s+(\S+)", source, re.M), expected)

    def test_original_guard_blind_spots_are_rejected(self):
        # These are the concrete layouts missed by the historical prefix filter.
        for source in ("example : True := by\n  sorry\n",
                       "example : True := by\n  admit\n",
                       "axiom invented : False\n",
                       "theorem sample : True := by\n  exact (by sorry)\n"):
            with self.subTest(source=source), self.assertRaisesRegex(AssertionError, "Forbidden"):
                require_no_proof_placeholders_or_axiom_commands(source)
        require_no_proof_placeholders_or_axiom_commands(
            '/- sorry /- axiom -/ admit -/\n-- sorry\n'
            'def description := "sorry and axiom are documentation"\n'
            'theorem sample : True := by trivial\n')


class Q05WholePathCompilerAddendum(unittest.TestCase):
    def test_canonical_outputs_full_domain_margins_and_semantic_controls(self):
        self.assertIsNotNone(shutil.which("lake"), "Pinned Lean compiler required")
        version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                                 capture_output=True, text=True, timeout=60, check=True).stdout.strip()
        self.assertRegex(version, r"Lean \(version 4\.34\.0[,)]")
        evidence = {
            "format": "Permansson.CERT.Q05WholePathAddendum.v1",
            "scope": "TECHNICAL_EVIDENCE_ONLY_NO_INDEPENDENT_ACCEPTANCE_OR_EXACT_GR",
            "compiler": version,
            "checked_git_commit": subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "frozen_source_sha256": SOURCE_SHA256,
            "stages": [], "semantic_controls": [],
        }
        with tempfile.TemporaryDirectory(prefix="q05-addendum-", dir=ROOT / ".lake") as directory:
            build = Path(directory)
            env = os.environ.copy()
            env["LEAN_PATH"] = str(build) + os.pathsep + env.get("LEAN_PATH", "")

            def compile_source(path, output=None):
                command = ["lake", "env", "lean"]
                if output is not None:
                    output.parent.mkdir(parents=True, exist_ok=True)
                    command += ["-o", str(output)]
                command.append(str(path))
                result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                        text=True, timeout=900, check=False)
                transcript = result.stdout + "\n" + result.stderr
                record = {"source": str(path.relative_to(ROOT)),
                          "source_sha256": digest(path.read_bytes()),
                          "exit_code": result.returncode,
                          "stdout": result.stdout, "stderr": result.stderr,
                          "compiler_output_sha256": digest(transcript.encode())}
                return result, transcript, record

            for stem, namespace, declarations in STAGES:
                path = ROOT / DIRECTORY / (stem + ".lean")
                result, transcript, record = compile_source(
                    path, build / DIRECTORY / (stem + ".olean"))
                # One JSON line preserves stream separation and exact transcript bytes.
                print("Q05_ADDENDUM_STAGE " + json.dumps(record, sort_keys=True), flush=True)
                self.assertEqual(result.returncode, 0, transcript[-12000:])
                self.assertNotIn("error:", transcript.lower())
                self.assertNotIn("sorryAx", transcript)
                expected = ["PermanssonResearch.Quotient." + namespace + "." + d
                            for d in declarations]
                record["axioms"] = parse_axiom_receipt(transcript, expected)
                evidence["stages"].append(record)

            preamble = (
                "import verification.research.tranche7_q05_original_margin_addendum\n"
                "open PermanssonLean PermanssonLean.RegimeSpecification\n"
                "open PermanssonResearch.Quotient.Q05ActualOriginalMarginWitnessFixture\n"
                "open PermanssonResearch.Quotient.Q05ConditionalExactMargin\n"
                "open PermanssonResearch.Quotient.Q05OriginalMarginClosure\n"
            )
            controls = {
                "fine_margin_cannot_be_coarse_value":
                    "example : constitutiveMargin (fineModel false) fineSpec fineFamily\n"
                    "  fineOriginalProperty fineComparisonSet fineJ = (1/5 : ℝ) := by\n"
                    "  exact fine_original_margin\n",
                "exact_gap_cannot_be_zero":
                    "example : |constitutiveMargin (fineModel false) fineSpec fineFamily\n"
                    "    fineOriginalProperty fineComparisonSet fineJ -\n"
                    "  constitutiveMargin (coarseModel false) coarseSpec coarseFamily\n"
                    "    coarseOriginalProperty coarseComparisonSet coarseJ| = (0 : ℝ) := by\n"
                    "  exact original_margin_gap\n",
            }
            for name, claim in controls.items():
                path = build / (name + ".lean")
                path.write_text(preamble + claim)
                result, transcript, record = compile_source(path)
                record["control"] = name
                print("Q05_ADDENDUM_CONTROL " + json.dumps(record, sort_keys=True), flush=True)
                self.assertNotEqual(result.returncode, 0, "False numerical claim compiled")
                for invalid in ("unknown identifier", "unknown module", "failed to import",
                                "object file", "unexpected token", "sorryax",
                                "maximum number of heartbeats", "out of memory", "timeout"):
                    self.assertNotIn(invalid, transcript.lower())
                self.assertRegex(transcript.lower(), r"type mismatch|unsolved goals")
                record["classification"] = "EXPECTED_MATHEMATICAL_REJECTION"
                evidence["semantic_controls"].append(record)
        print("Q05_WHOLE_PATH_ADDENDUM_RECEIPT " + json.dumps(evidence, sort_keys=True), flush=True)


if __name__ == "__main__":
    unittest.main()
