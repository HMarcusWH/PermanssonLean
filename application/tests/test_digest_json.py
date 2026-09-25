"""Regressions for the combined --digest --json CLI contract and entry point."""
from __future__ import annotations

import contextlib
import copy
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from application.validator.validate_application import main, pipeline_digest

APP = Path(__file__).resolve().parents[1]
CLI = APP / "validator" / "validate_application.py"
FIXTURE = APP / "examples" / "grounded_pr_minimal"
REPORT_KEYS = {"contract_valid", "scientific_claims_verified", "errors", "notice"}
DIGEST_KEYS = REPORT_KEYS | {"digest_generated", "proposed_pipeline_id"}


class DigestJsonTests(unittest.TestCase):
    def setUp(self) -> None:
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name) / "bundle"
        shutil.copytree(FIXTURE, self.root)
        self.path = self.root / "application.json"
        self.doc = json.loads(self.path.read_text(encoding="utf-8"))

    def write_document(self) -> None:
        self.path.write_text(json.dumps(self.doc), encoding="utf-8", newline="\n")

    def run_cli(self, *flags: str, path: Path | None = None) -> subprocess.CompletedProcess[str]:
        args = [str(path or self.path), *flags]
        output, errors = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors):
            code = main(args)
        return subprocess.CompletedProcess(args, code, output.getvalue(), errors.getvalue())

    def digest_json(self, expected_exit: int, path: Path | None = None) -> dict:
        process = self.run_cli("--digest", "--json", path=path)
        self.assertEqual(process.returncode, expected_exit, process.stdout + process.stderr)
        self.assertEqual(process.stderr, "")
        result = json.loads(process.stdout)  # Also rejects mixed JSON/plain-text output.
        self.assertEqual(set(result), DIGEST_KEYS)
        self.assertIs(result["scientific_claims_verified"], False)
        self.assertTrue(result["notice"])
        self.assertIs(result["digest_generated"], expected_exit == 0)
        if expected_exit:
            self.assertIsNone(result["proposed_pipeline_id"])
            self.assertIs(result["contract_valid"], False)
        else:
            self.assertEqual(result["proposed_pipeline_id"], pipeline_digest(self.doc))
        return result

    def test_cli_entrypoint_emits_json_on_digest_success(self) -> None:
        process = subprocess.run(
            [sys.executable, str(CLI), str(self.path), "--digest", "--json"],
            cwd=self.root, capture_output=True, text=True, encoding="utf-8",
            timeout=20, check=False,
        )
        self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
        self.assertEqual(process.stderr, "")
        result = json.loads(process.stdout)
        self.assertEqual(set(result), DIGEST_KEYS)
        self.assertIs(result["scientific_claims_verified"], False)
        self.assertIs(result["digest_generated"], True)
        self.assertEqual(result["proposed_pipeline_id"], pipeline_digest(self.doc))

    def test_valid_bundle_returns_json_digest_and_validation_report(self) -> None:
        result = self.digest_json(0)
        self.assertIs(result["contract_valid"], True)
        self.assertEqual(result["errors"], [])

    def test_matching_placeholders_return_proposal_without_claiming_validity(self) -> None:
        for owner in ("certificate", "semantic_pipeline"):
            self.doc[owner]["pipeline_id"] = "sha256:" + "0" * 64
        self.write_document()
        result = self.digest_json(0)
        self.assertIs(result["contract_valid"], False)
        self.assertEqual([e["code"] for e in result["errors"]], ["PIPELINE_DIGEST"])

    def test_matching_stale_ids_preserve_validation_error(self) -> None:
        old_id = self.doc["semantic_pipeline"]["pipeline_id"]
        self.doc["interventions"][0]["replacement_ref"] = "argument"
        self.write_document()
        result = self.digest_json(0)
        self.assertNotEqual(result["proposed_pipeline_id"], old_id)
        self.assertIs(result["contract_valid"], False)
        self.assertEqual([e["code"] for e in result["errors"]], ["PIPELINE_DIGEST"])

    def test_mismatched_certificate_fails_in_json_mode(self) -> None:
        original = copy.deepcopy(self.doc)
        for stale_pipeline in (False, True):
            with self.subTest(stale_pipeline=stale_pipeline):
                self.doc = copy.deepcopy(original)
                self.doc["certificate"]["pipeline_id"] = "sha256:" + "f" * 64
                if stale_pipeline:
                    self.doc["semantic_pipeline"]["pipeline_id"] = "sha256:" + "0" * 64
                self.write_document()
                result = self.digest_json(1)
                self.assertIn("CERTIFICATE_PIPELINE", {e["code"] for e in result["errors"]})

    def test_tampered_artifact_fails_without_a_proposed_digest(self) -> None:
        (self.root / "specification.md").write_bytes(b"tampered")
        result = self.digest_json(1)
        self.assertIn("ARTIFACT_HASH", {e["code"] for e in result["errors"]})

    def test_schema_violation_returns_json_failure(self) -> None:
        self.path.write_text("{}", encoding="utf-8")
        result = self.digest_json(1)
        self.assertEqual({e["code"] for e in result["errors"]}, {"SCHEMA"})

    def test_input_errors_return_json_with_no_proposal(self) -> None:
        for raw in (b"{", b'{"x":1,"x":2}', b"\xff"):
            with self.subTest(raw=raw):
                self.path.write_bytes(raw)
                result = self.digest_json(2)
                self.assertEqual([e["code"] for e in result["errors"]], ["INPUT_OR_CONFIGURATION"])
        result = self.digest_json(2, path=self.root / "missing.json")
        self.assertEqual([e["code"] for e in result["errors"]], ["INPUT_OR_CONFIGURATION"])

    def test_flag_order_does_not_change_json_result(self) -> None:
        first = self.run_cli("--digest", "--json")
        second = self.run_cli("--json", "--digest")
        self.assertEqual((first.returncode, second.returncode), (0, 0))
        self.assertEqual(json.loads(first.stdout), json.loads(second.stdout))

    def test_plain_digest_output_remains_backward_compatible(self) -> None:
        for placeholders in (False, True):
            with self.subTest(placeholders=placeholders):
                if placeholders:
                    for owner in ("certificate", "semantic_pipeline"):
                        self.doc[owner]["pipeline_id"] = "sha256:" + "0" * 64
                    self.write_document()
                process = self.run_cli("--digest")
                self.assertEqual(process.returncode, 0, process.stderr)
                self.assertEqual(process.stdout, pipeline_digest(self.doc) + "\n")
                self.assertEqual(process.stderr, "")

    def test_json_validation_without_digest_keeps_existing_shape_and_exit_codes(self) -> None:
        for placeholders in (False, True):
            with self.subTest(placeholders=placeholders):
                if placeholders:
                    for owner in ("certificate", "semantic_pipeline"):
                        self.doc[owner]["pipeline_id"] = "sha256:" + "0" * 64
                    self.write_document()
                process = self.run_cli("--json")
                self.assertEqual(process.returncode, int(placeholders))
                result = json.loads(process.stdout)
                self.assertEqual(set(result), REPORT_KEYS)
                self.assertIs(result["scientific_claims_verified"], False)
                self.assertIs(result["contract_valid"], not placeholders)

    def test_json_digest_is_read_only_on_success_bootstrap_and_failure(self) -> None:
        for mode, expected_exit in (("sealed", 0), ("bootstrap", 0), ("mismatch", 1)):
            with self.subTest(mode=mode):
                if mode == "bootstrap":
                    for owner in ("certificate", "semantic_pipeline"):
                        self.doc[owner]["pipeline_id"] = "sha256:" + "0" * 64
                elif mode == "mismatch":
                    self.doc["certificate"]["pipeline_id"] = "sha256:" + "f" * 64
                self.write_document()
                before = {p.name: p.read_bytes() for p in self.root.iterdir()}
                self.digest_json(expected_exit)
                self.assertEqual(before, {p.name: p.read_bytes() for p in self.root.iterdir()})

    def test_truthfully_invalid_application_can_still_have_a_conforming_digest(self) -> None:
        self.doc["certificate"]["validity"] = "INVALID"
        self.write_document()
        result = self.digest_json(0)
        self.assertIs(result["contract_valid"], True)
        self.assertEqual(json.loads(self.path.read_text(encoding="utf-8"))["certificate"]["validity"], "INVALID")


if __name__ == "__main__":
    unittest.main()
