"""Source-bound F-01 and D-09 evidence; no certification decision is changed.

The JSON specification fixes named declarations, unchanged source bytes and
deliberately false controls. Existing library sources are built by Research CI;
the verification-only Fin3 fixture is compiled into an isolated import path.
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
from verification.research.test_cert_q05_whole_path_addendum import (
    require_no_proof_placeholders_or_axiom_commands,
)

ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = ROOT / "verification/research/certification_addenda_20261119/Tranche8_F01_D09_Scope_Spec.json"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def specification() -> dict:
    return json.loads(SPEC_PATH.read_text(encoding="utf-8"))


class Tranche8SourceScope(unittest.TestCase):
    def test_exact_source_pins_declaration_sets_and_control_sources(self):
        spec = specification()
        self.assertEqual((ROOT / "lean-toolchain").read_text().strip(),
                         "leanprover/lean4:v4.34.0")
        self.assertEqual([case["id"] for case in spec["cases"]], ["F-01", "D-09"])
        for path, expected in spec["frozen_source_sha256"].items():
            self.assertEqual(sha256((ROOT / path).read_bytes()), expected, path)
        for case in spec["cases"]:
            path = ROOT / case["probe"]
            contents = path.read_text(encoding="utf-8")
            self.assertEqual(sha256(path.read_bytes()), case["probe_sha256"])
            self.assertTrue(contents.startswith("import "))
            require_no_proof_placeholders_or_axiom_commands(contents)
            self.assertEqual(re.findall(r"^#check\s+(\S+)", contents, re.M),
                             case["expected_declarations"])
            self.assertEqual(re.findall(r"^#print axioms\s+(\S+)", contents, re.M),
                             case["expected_declarations"])
            self.assertEqual(len(set(case["expected_declarations"])),
                             len(case["expected_declarations"]))
            for control in case["semantic_controls"]:
                self.assertEqual(sha256(control["code"].encode()), control["source_sha256"])
                require_no_proof_placeholders_or_axiom_commands(control["code"])


class Tranche8CaseCompilerReceipts(unittest.TestCase):
    def replay_case(self, case_id: str) -> None:
        spec = specification()
        case = next(item for item in spec["cases"] if item["id"] == case_id)
        observed_hashes = {}
        for relative, expected in spec["frozen_source_sha256"].items():
            observed_hashes[relative] = sha256((ROOT / relative).read_bytes())
            self.assertEqual(observed_hashes[relative], expected, relative)
        self.assertEqual(sha256((ROOT / case["probe"]).read_bytes()), case["probe_sha256"])
        self.assertIsNotNone(shutil.which("lake"), "Pinned Lean compiler is required")
        version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                                 capture_output=True, text=True, timeout=60, check=True).stdout.strip()
        self.assertRegex(version, r"Lean \(version 4\.34\.0[,)]")
        evidence = {
            "format": "Permansson.CERT.Tranche8CaseReceipt.v1",
            "case_id": case_id,
            "scope": case["scope"],
            "acceptance_changes": 0,
            "compiler": version,
            "checked_git_commit": subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "git_worktree_status": subprocess.check_output(
                ["git", "status", "--porcelain", "--untracked-files=all"],
                cwd=ROOT, text=True).splitlines(),
            "specification_sha256": sha256(SPEC_PATH.read_bytes()),
            "frozen_source_sha256": observed_hashes,
            "prerequisites": [],
            "positive_stage": None,
            "semantic_controls": [],
        }
        with tempfile.TemporaryDirectory(prefix="tranche8-", dir=ROOT / ".lake") as directory:
            build = Path(directory)
            env = os.environ.copy()
            env["LEAN_PATH"] = str(build) + os.pathsep + env.get("LEAN_PATH", "")

            def compile_source(path: Path, output: Path | None = None) -> tuple:
                command = ["lake", "env", "lean"]
                if output is not None:
                    output.parent.mkdir(parents=True, exist_ok=True)
                    command += ["-o", str(output)]
                command.append(str(path))
                result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                        text=True, timeout=900, check=False)
                transcript = result.stdout + "\n" + result.stderr
                record = {
                    "case_id": case_id,
                    "source": str(path.relative_to(ROOT)),
                    "source_sha256": sha256(path.read_bytes()),
                    "exit_code": result.returncode,
                    "stdout": result.stdout,
                    "stderr": result.stderr,
                    "compiler_output_sha256": sha256(transcript.encode()),
                }
                print("TRANCHE8_COMPILER_STAGE " + json.dumps(record, sort_keys=True), flush=True)
                return result, transcript, record

            def assert_positive(result: subprocess.CompletedProcess, transcript: str) -> None:
                self.assertEqual(result.returncode, 0, transcript[-16000:])
                self.assertNotIn("error:", transcript.lower(), transcript[-16000:])
                self.assertNotIn("sorryAx", transcript)

            for relative in case["compile_prerequisites"]:
                result, transcript, record = compile_source(
                    ROOT / relative, (build / relative).with_suffix(".olean"))
                assert_positive(result, transcript)
                evidence["prerequisites"].append(record)

            probe = ROOT / case["probe"]
            result, transcript, record = compile_source(
                probe, (build / case["probe"]).with_suffix(".olean"))
            assert_positive(result, transcript)
            record["axioms"] = parse_axiom_receipt(transcript, case["expected_declarations"])
            evidence["positive_stage"] = record

            for control in case["semantic_controls"]:
                path = build / (control["id"] + ".lean")
                path.write_text(control["code"], encoding="utf-8")
                result, transcript, record = compile_source(path)
                record["control_id"] = control["id"]
                self.assertNotEqual(result.returncode, 0, "The false control compiled")
                for invalid in ("unknown identifier", "unknown module", "failed to import",
                                "object file", "unexpected token", "sorryax",
                                "maximum number of heartbeats", "out of memory", "timeout",
                                "failed to synthesize", "invalid field", "invalid argument name"):
                    self.assertNotIn(invalid, transcript.lower(), transcript[-12000:])
                self.assertRegex(transcript.lower(), r"type mismatch|unsolved goals")
                record["classification"] = "EXPECTED_MATHEMATICAL_REJECTION"
                evidence["semantic_controls"].append(record)
        print("TRANCHE8_CASE_RECEIPT " + json.dumps(evidence, sort_keys=True), flush=True)

    def test_f01_original_swap_private_updates_and_fin3(self):
        self.replay_case("F-01")

    def test_d09_physical_classes_and_distinct_phaseblind_model(self):
        self.replay_case("D-09")


if __name__ == "__main__":
    unittest.main()
