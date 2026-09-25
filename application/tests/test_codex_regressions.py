"""Regression tests for PR #32's digest, evidence-byte and chronology review."""
from __future__ import annotations

import contextlib
from decimal import Inexact, Rounded, localcontext
from fractions import Fraction
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from application.examples.build_examples import make_example
from application.validator.validate_application import (
    _timestamp, artifact_digest, main, pipeline_digest, validate_document,
)

ROOT = Path(__file__).resolve().parents[2]


class ReviewRegressionTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        files = make_example("grounded_pr_minimal")
        for name, content in files.items():
            (self.root / name).write_bytes(content.encode("utf-8"))
        self.doc = json.loads(files["application.json"])

    def seal(self):
        digest = pipeline_digest(self.doc)
        self.doc["semantic_pipeline"]["pipeline_id"] = digest
        self.doc["certificate"]["pipeline_id"] = digest

    def codes(self):
        return {e["code"] for e in validate_document(self.doc, self.root)["errors"]}

    def cli(self, *flags):
        path = self.root / "application.json"
        before = json.dumps(self.doc, indent=2).encode("utf-8")
        path.write_bytes(before)
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = main([str(path), *flags])
        self.assertEqual(path.read_bytes(), before, "The CLI must remain read-only")
        return code, output.getvalue()

    def test_digest_rejects_certificate_mismatch_with_current_pipeline(self):
        self.doc["certificate"]["pipeline_id"] = "sha256:" + "f" * 64
        self.assertEqual(self.codes(), {"CERTIFICATE_PIPELINE"})
        code, output = self.cli("--digest")
        self.assertEqual(code, 1)
        self.assertIn("CERTIFICATE_PIPELINE", output)
        self.assertNotEqual(output.strip(), pipeline_digest(self.doc))

    def test_digest_rejects_mismatch_when_both_ids_are_stale(self):
        self.doc["semantic_pipeline"]["pipeline_id"] = "sha256:" + "0" * 64
        self.doc["certificate"]["pipeline_id"] = "sha256:" + "f" * 64
        self.assertEqual(self.codes(), {"PIPELINE_DIGEST", "CERTIFICATE_PIPELINE"})
        code, output = self.cli("--digest", "--json")
        self.assertEqual(code, 1)
        result = json.loads(output)
        self.assertFalse(result["contract_valid"])
        self.assertFalse(result["scientific_claims_verified"])
        self.assertIn("CERTIFICATE_PIPELINE", {e["code"] for e in result["errors"]})

    def test_digest_bootstrap_accepts_matching_placeholder_ids(self):
        placeholder = "sha256:" + "0" * 64
        self.doc["semantic_pipeline"]["pipeline_id"] = placeholder
        self.doc["certificate"]["pipeline_id"] = placeholder
        self.assertEqual(self.codes(), {"PIPELINE_DIGEST"})
        code, output = self.cli("--digest")
        self.assertEqual(code, 0)
        self.assertEqual(output.strip(), pipeline_digest(self.doc))
        code, _ = self.cli()
        self.assertEqual(code, 1, "Digest proposals are not normal validation")

    def test_digest_can_propose_new_id_after_matching_stale_semantics(self):
        self.doc["semantic_pipeline"]["bindings"]["relevance_map"] = "argument"
        self.assertEqual(self.codes(), {"PIPELINE_DIGEST"})
        code, output = self.cli("--digest")
        self.assertEqual(code, 0)
        self.assertEqual(output.strip(), pipeline_digest(self.doc))

    def test_digest_bootstrap_still_rejects_artifact_tampering(self):
        placeholder = "sha256:" + "0" * 64
        self.doc["semantic_pipeline"]["pipeline_id"] = placeholder
        self.doc["certificate"]["pipeline_id"] = placeholder
        (self.root / "specification.md").write_bytes(b"changed evidence\r\n")
        code, output = self.cli("--digest")
        self.assertEqual(code, 1)
        self.assertIn("ARTIFACT_HASH", output)

    def test_late_submicrosecond_freeze_is_rejected(self):
        pipeline = self.doc["semantic_pipeline"]
        for places in (7, 9, 30, 100):
            with self.subTest(places=places):
                zeros = "0" * (places - 1)
                pipeline["evaluation_started_at"] = f"2026-09-02T00:00:00.{zeros}1Z"
                pipeline["frozen_at"] = f"2026-09-02T00:00:00.{zeros}9Z"
                self.seal()
                self.assertEqual(self.codes(), {"FREEZE_CHRONOLOGY"})

    def test_early_submicrosecond_freeze_is_accepted(self):
        pipeline = self.doc["semantic_pipeline"]
        pipeline["frozen_at"] = "2026-09-02T00:00:00.0000001Z"
        pipeline["evaluation_started_at"] = "2026-09-02T00:00:00.0000009Z"
        self.seal()
        self.assertEqual(self.codes(), set())

    def test_fractional_chronology_retains_timezone_order(self):
        pipeline = self.doc["semantic_pipeline"]
        pipeline["frozen_at"] = "2026-09-02T02:00:00.0000009+02:00"
        pipeline["evaluation_started_at"] = "2026-09-01T22:00:00.0000001-02:00"
        self.seal()
        self.assertEqual(self.codes(), {"FREEZE_CHRONOLOGY"})
        pipeline["frozen_at"] = "2026-09-02T02:00:00.0000001+02:00"
        self.seal()
        self.assertEqual(self.codes(), set())

    def test_fractional_equal_instants_with_offsets_and_trailing_zeros(self):
        pipeline = self.doc["semantic_pipeline"]
        for frozen, evaluated in (
            ("2026-09-02T02:00:00.0000001000+02:00", "2026-09-02T00:00:00.0000001Z"),
            ("2026-09-02T00:00:00.000000000Z", "2026-09-01T22:00:00-02:00"),
            ("2026-09-02T00:00:00.12Z", "2026-09-02T00:00:00.120000000000+00:00"),
        ):
            with self.subTest(frozen=frozen, evaluated=evaluated):
                pipeline.update(frozen_at=frozen, evaluation_started_at=evaluated)
                self.seal()
                self.assertEqual(self.codes(), set())
                self.assertEqual(_timestamp(frozen), _timestamp(evaluated))

    def test_fractional_comparison_does_not_round_at_decimal_context_precision(self):
        with localcontext() as ctx:
            ctx.prec = 2
            ctx.traps[Inexact] = True
            ctx.traps[Rounded] = True
            early = "2026-09-02T00:00:00." + "9" * 40 + "1Z"
            late = "2026-09-02T00:00:00." + "9" * 40 + "9Z"
            self.assertLess(_timestamp(early), _timestamp(late))

    def test_fractional_order_matches_exact_rationals(self):
        fractions = ("0", "00", "1", "10", "12", "120", "12001", "01",
                     "009", "0000001", "0000009", "9" * 60, "0" * 59 + "1")
        for left in fractions:
            for right in fractions:
                with self.subTest(left=left, right=right):
                    a = _timestamp(f"2026-09-02T00:00:00.{left}Z")
                    b = _timestamp(f"2026-09-02T00:00:00.{right}Z")
                    x, y = Fraction("0." + left), Fraction("0." + right)
                    self.assertEqual((a > b) - (a < b), (x > y) - (x < y))

    def test_fractional_order_across_whole_second_and_year_boundaries(self):
        pairs = (
            ("2026-09-02T00:00:00.999999999Z", "2026-09-02T00:00:01.000000001Z"),
            ("2026-12-31T23:59:59.999999999Z", "2027-01-01T00:00:00.000000001Z"),
            ("2026-12-31T22:59:59.999999999-01:00", "2027-01-01T01:00:00.000000001+01:00"),
        )
        for before, after in pairs:
            with self.subTest(before=before, after=after):
                self.assertLess(_timestamp(before), _timestamp(after))

    def test_malformed_fraction_and_unknown_offsets_still_fail(self):
        for stamp in ("2026-09-02T00:00:00.Z", "2026-09-02T00:00:00.1.2Z",
                      "2026-09-02T00:00:00.1e-7Z", "2026-09-02T00:00:00.0000001",
                      "2026-09-02T00:00:00.0000001-00:00",
                      "2026-09-02T00:00:00.0000001+24:00",
                      "2026-09-02T00:00:60.0000001Z"):
            with self.subTest(stamp=stamp), self.assertRaises(ValueError):
                _timestamp(stamp)


class EvidenceGitRoundTripTests(unittest.TestCase):
    def test_raw_evidence_survives_git_index_and_checkout_with_all_autocrlf_modes(self):
        git = shutil.which("git")
        self.assertIsNotNone(git, "Git is required for the evidence-byte regression")
        attributes = (ROOT / ".gitattributes").read_bytes()
        # Isolate the temporary repository from caller-specific Git configuration.
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        raw_text = b"unaltered\r\nevidence\nwith mixed endings\r\n"
        binary = b"\x00\xff\x80original\r\nevidence\r\n"
        payloads = {
            "application/artifacts/source.bin": binary,
            "application/bundles/case/source.pdf": binary,
            "application/bundles/case/report.txt": raw_text,
            "application/bundles/case/report.md": raw_text,
            "application/bundles/case/data.json": b'{"raw":true}\r\n',
            "application/bundles/case/source.py": raw_text,
            "application/examples/case/evidence.csv": raw_text,
            "application/examples/case/argument.md": raw_text,
            "application/examples/case/application.json": b'{"raw":true}\r\n',
        }
        source_path = "application/validator/sample.py"
        for autocrlf in ("true", "false", "input"):
            with self.subTest(autocrlf=autocrlf), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                def run(*args):
                    return subprocess.run(
                        [git, "-c", f"core.autocrlf={autocrlf}", "-c", "core.safecrlf=false",
                         "-c", "core.attributesFile=", *args], cwd=root, env=env,
                        check=True, capture_output=True, timeout=30,
                    ).stdout
                run("init", "-q", "--template=")
                (root / ".gitattributes").write_bytes(attributes)
                all_files = {**payloads, source_path: b"# authored source\r\n"}
                for relative, data in all_files.items():
                    path = root / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(data)
                run("add", "--", ".")
                for relative, data in payloads.items():
                    self.assertEqual(run("show", ":" + relative), data, relative)
                self.assertEqual(run("show", ":" + source_path), b"# authored source\n")
                for relative in all_files:
                    (root / relative).unlink()
                run("checkout-index", "--all", "--force")
                for relative, data in payloads.items():
                    self.assertEqual((root / relative).read_bytes(), data, relative)
                    self.assertEqual(artifact_digest(root / relative), hashlib.sha256(data).hexdigest())
                self.assertEqual((root / source_path).read_bytes(), b"# authored source\n")


if __name__ == "__main__":
    unittest.main()
