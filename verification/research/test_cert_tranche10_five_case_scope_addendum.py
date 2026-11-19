"""Source-bound five-case repairs; no certification decision is changed.

The JSON specification fixes named declarations, unchanged source bytes and
deliberately false controls. Existing library sources are built by Research CI;
the additive verification sources are compiled into an isolated import path.
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
SPEC_PATH = ROOT / "verification/research/certification_addenda_20261120/Tranche10_Five_Case_Scope_Spec.json"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def specification() -> dict:
    return json.loads(SPEC_PATH.read_text(encoding="utf-8"))


class Tranche10SourceScope(unittest.TestCase):
    def test_exact_source_pins_declaration_sets_and_control_sources(self):
        spec = specification()
        self.assertEqual((ROOT / "lean-toolchain").read_text().strip(),
                         "leanprover/lean4:v4.34.0")
        self.assertEqual([case["id"] for case in spec["cases"]], ["D-05", "B-02", "M-02", "Q-03", "Q-04"])
        self.assertEqual(spec["acceptance_changes"], 0)
        registry = json.loads((ROOT / "research/paper_closures/spec/registries/acceptance_tests.json")
                              .read_text(encoding="utf-8"))
        criteria = {item["id"]: item for item in registry["cases"]}
        for path, expected in spec["frozen_source_sha256"].items():
            self.assertEqual(sha256((ROOT / path).read_bytes()), expected, path)
        for case in spec["cases"]:
            self.assertEqual(case["family"], "original_45")
            self.assertEqual(case["original_registry_criterion"], criteria[case["id"]])
            self.assertEqual(case["frozen_decision"], "PENDING")
            self.assertEqual([name for group in case["declaration_groups"]
                              for name in group["declarations"]],
                             case["expected_declarations"])
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
                self.assertIn(control["positive_declaration"], case["expected_declarations"])
                require_no_proof_placeholders_or_axiom_commands(control["code"])


class Tranche10CaseCompilerReceipts(unittest.TestCase):
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
            "format": "Permansson.CERT.Tranche10CaseReceipt.v1",
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
            "driver_sha256": sha256(Path(__file__).read_bytes()),
            "frozen_source_sha256": observed_hashes,
            "prerequisites": [],
            "positive_stage": None,
            "semantic_controls": [],
        }
        with tempfile.TemporaryDirectory(prefix="tranche10-", dir=ROOT / ".lake") as directory:
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
                print("TRANCHE10_COMPILER_STAGE " + json.dumps(record, sort_keys=True), flush=True)
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
                self.assertIn("error:", transcript.lower(), transcript[-12000:])
                for invalid in ("unknown identifier", "unknown module", "failed to import",
                                "object file", "unexpected token", "sorryax",
                                "maximum number of heartbeats", "out of memory", "timeout",
                                "failed to synthesize", "invalid field", "invalid argument name"):
                    self.assertNotIn(invalid, transcript.lower(), transcript[-12000:])
                self.assertRegex(transcript.lower(), r"type mismatch|unsolved goals")
                record["classification"] = "EXPECTED_MATHEMATICAL_REJECTION"
                evidence["semantic_controls"].append(record)
        # A receipt must describe the inputs that were actually held fixed
        # throughout the replay, including when several workers share a checkout.
        self.assertEqual(sha256(SPEC_PATH.read_bytes()), evidence["specification_sha256"])
        self.assertEqual(sha256(Path(__file__).read_bytes()), evidence["driver_sha256"])
        self.assertEqual(sha256((ROOT / case["probe"]).read_bytes()), case["probe_sha256"])
        for relative, expected in observed_hashes.items():
            self.assertEqual(sha256((ROOT / relative).read_bytes()), expected, relative)
        head_after = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        self.assertEqual(head_after, evidence["checked_git_commit"],
                         "Git HEAD changed during case replay")
        evidence["git_worktree_status_after"] = subprocess.check_output(
            ["git", "status", "--porcelain", "--untracked-files=all"],
            cwd=ROOT, text=True).splitlines()
        evidence["inputs_unchanged_across_replay"] = True
        print("TRANCHE10_CASE_RECEIPT " + json.dumps(evidence, sort_keys=True), flush=True)

    def test_d05_actual_rectangular_game_value(self):
        self.replay_case("D-05")

    def test_b02_incomparable_minima_and_local_transport(self):
        self.replay_case("B-02")

    def test_m02_actual_marked_history_and_autonomy(self):
        self.replay_case("M-02")

    def test_q03_dependent_actual_measure_event_tv(self):
        self.replay_case("Q-03")

    def test_q04_intervention_reaches_bad_row(self):
        self.replay_case("Q-04")


if __name__ == "__main__":
    unittest.main()
