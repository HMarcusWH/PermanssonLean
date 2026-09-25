"""CLI-boundary regressions: parse errors, output modes, and documented exits."""
from __future__ import annotations

import contextlib
import copy
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import application.validator.validate_application as cli


class ArgumentErrorTests(unittest.TestCase):
    def call(self, argv):
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = cli.main(argv)
        return code, stdout.getvalue(), stderr.getvalue()

    def assertJsonError(self, argv, digest=False):
        original = list(argv)
        with patch.object(cli, "load_json") as load, patch.object(cli, "validate_document") as validate:
            code, output, stderr = self.call(argv)
        load.assert_not_called()
        validate.assert_not_called()
        self.assertEqual(argv, original)
        self.assertEqual(code, 2)
        self.assertEqual(stderr, "")
        result = json.loads(output)
        expected = {"contract_valid", "scientific_claims_verified", "errors", "notice"}
        if digest:
            expected |= {"digest_generated", "proposed_pipeline_id"}
            self.assertIs(result["digest_generated"], False)
            self.assertIsNone(result["proposed_pipeline_id"])
        self.assertEqual(set(result), expected)
        self.assertIs(result["contract_valid"], False)
        self.assertIs(result["scientific_claims_verified"], False)
        self.assertEqual(len(result["errors"]), 1)
        self.assertEqual(result["errors"][0]["code"], "INPUT_OR_CONFIGURATION")
        self.assertTrue(result["errors"][0]["message"])
        self.assertEqual(result["notice"], cli.NOTICE)
        return result

    def test_missing_bundle_json(self):
        self.assertJsonError(["--json"])

    def test_missing_bundle_digest_json_both_orders(self):
        for args in (["--digest", "--json"], ["--json", "--digest"]):
            with self.subTest(args=args):
                self.assertJsonError(args, digest=True)

    def test_unknown_option_json_in_any_position(self):
        for args in (["--unknown", "bundle.json", "--json"],
                     ["--json", "bundle.json", "--unknown"],
                     ["bundle.json", "--unknown", "--json"]):
            with self.subTest(args=args):
                self.assertJsonError(args)

    def test_unknown_option_digest_json_in_any_position(self):
        for args in (["--unknown", "--digest", "--json", "bundle.json"],
                     ["bundle.json", "--json", "--unknown", "--digest"],
                     ["--digest", "bundle.json", "--unknown", "--json"]):
            with self.subTest(args=args):
                self.assertJsonError(args, digest=True)

    def test_extra_positional_argument(self):
        self.assertJsonError(["a.json", "b.json", "--digest", "--json"], digest=True)

    def test_values_attached_to_boolean_flags_fail_as_json(self):
        for flag in ("--digest=false", "--json=true", "--j=true", "--d=false"):
            with self.subTest(flag=flag):
                self.assertJsonError([flag, "bundle.json", "--digest", "--json"], digest=True)

    def test_existing_unambiguous_abbreviations_keep_json_errors(self):
        for args in (["--j"], ["--js", "--dig"], ["bundle.json", "--d", "--j", "--bad"]):
            with self.subTest(args=args):
                self.assertJsonError(args, digest=len(args) > 1)

    def test_mode_detection_respects_end_of_options(self):
        # These are extra positional values, not output-mode requests.
        code, stdout, stderr = self.call(["bundle.json", "--", "--json", "--digest"])
        self.assertEqual(code, 2)
        self.assertEqual(stdout, "")
        self.assertIn("usage:", stderr)
        self.assertNotIn('"contract_valid"', stderr)
        self.assertJsonError(["--json", "bundle.json", "--", "--digest"])
        self.assertJsonError(["--json", "--digest", "--"], digest=True)

    def test_flag_like_unknown_values_do_not_enable_json(self):
        for args in (["--unknown=--json"], ["--json-extra"], ["--jsonish"]):
            with self.subTest(args=args):
                code, stdout, stderr = self.call(args)
                self.assertEqual(code, 2)
                self.assertEqual(stdout, "")
                self.assertIn("usage:", stderr)

    def test_text_mode_parser_errors_keep_usage_on_stderr(self):
        for args in ([], ["--digest"], ["bundle.json", "--unknown"]):
            with self.subTest(args=args):
                code, stdout, stderr = self.call(args)
                self.assertEqual(code, 2)
                self.assertEqual(stdout, "")
                self.assertIn("usage:", stderr)
                self.assertIn("error:", stderr)

    def test_default_argv_entrypoint(self):
        with patch.object(sys, "argv", ["validate_application.py", "--digest", "--json"]):
            code, output, stderr = self.call(None)
        self.assertEqual(code, 2)
        self.assertEqual(stderr, "")
        self.assertIs(json.loads(output)["digest_generated"], False)

    def test_explicit_help_remains_text_and_never_reads_bundle(self):
        for args in (["--help"], ["--json", "--help"], ["--digest", "--json", "-h"]):
            with self.subTest(args=args):
                stdout, stderr = io.StringIO(), io.StringIO()
                with patch.object(cli, "load_json") as load:
                    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                        with self.assertRaises(SystemExit) as stopped:
                            cli.main(args)
                self.assertEqual(stopped.exception.code, 0)
                self.assertIn("usage:", stdout.getvalue())
                self.assertEqual(stderr.getvalue(), "")
                load.assert_not_called()

    def test_process_entrypoint_parse_errors_are_json_and_exit_two(self):
        with tempfile.TemporaryDirectory() as directory:
            for args in (["--json"], ["--digest", "--json"],
                         ["bundle.json", "--unknown", "--digest", "--json"],
                         ["--digest=false", "--json", "bundle.json"]):
                with self.subTest(args=args):
                    result = subprocess.run([sys.executable, str(Path(cli.__file__).resolve()), *args],
                                            cwd=directory, capture_output=True, text=True,
                                            timeout=15, check=False)
                    self.assertEqual(result.returncode, 2)
                    self.assertEqual(result.stderr, "")
                    report = json.loads(result.stdout)
                    self.assertIs(report["contract_valid"], False)
                    self.assertIs(report["scientific_claims_verified"], False)
                    self.assertEqual(report["errors"][0]["code"], "INPUT_OR_CONFIGURATION")
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_input_errors_use_same_json_shape_as_parser_errors(self):
        for digest in (False, True):
            flags = ["--json"] + (["--digest"] if digest else [])
            parse_error = self.assertJsonError(flags, digest=digest)
            with tempfile.TemporaryDirectory() as directory:
                code, output, stderr = self.call([str(Path(directory) / "absent.json"), *flags])
            input_error = json.loads(output)
            self.assertEqual(code, 2)
            self.assertEqual(stderr, "")
            self.assertEqual(set(parse_error), set(input_error))
            self.assertEqual(parse_error["errors"][0]["code"], input_error["errors"][0]["code"])


class DocumentedExitTests(unittest.TestCase):
    """Exercise mode-specific exits independently of scientific validation."""

    def test_exit_table_matches_cli_for_valid_stale_and_invalid_reports(self):
        digest = "sha256:" + "a" * 64
        for codes in ([], ["PIPELINE_DIGEST"], ["CERTIFICATE_PIPELINE"], ["ARTIFACT_HASH"],
                      ["PIPELINE_DIGEST", "CERTIFICATE_PIPELINE"]):
            report = {"contract_valid": not codes, "scientific_claims_verified": False,
                      "errors": [{"code": code, "message": "synthetic CLI test"} for code in codes],
                      "notice": cli.NOTICE}
            for flags in ([], ["--json"], ["--digest"], ["--digest", "--json"]):
                with self.subTest(codes=codes, flags=flags):
                    output, stderr = io.StringIO(), io.StringIO()
                    can_propose = "--digest" in flags and set(codes) <= {"PIPELINE_DIGEST"}
                    with patch.object(cli, "load_json", return_value={}), \
                            patch.object(cli, "validate_document", return_value=copy.deepcopy(report)), \
                            patch.object(cli, "pipeline_digest", return_value=digest) as make_digest, \
                            contextlib.redirect_stdout(output), contextlib.redirect_stderr(stderr):
                        code = cli.main(["bundle.json", *flags])
                    self.assertEqual(code, 0 if can_propose or not codes else 1)
                    self.assertEqual(stderr.getvalue(), "")
                    self.assertEqual(make_digest.call_count, int(can_propose))
                    if "--json" in flags:
                        parsed = json.loads(output.getvalue())
                        self.assertEqual(parsed["contract_valid"], not codes)
                        self.assertEqual(parsed["errors"], report["errors"])
                        self.assertIs(parsed["scientific_claims_verified"], False)
                        if "--digest" in flags:
                            self.assertEqual(parsed["digest_generated"], can_propose)
                            self.assertEqual(parsed["proposed_pipeline_id"], digest if can_propose else None)
                    elif can_propose:
                        self.assertEqual(output.getvalue(), digest + "\n")

    def test_canonical_standard_and_readme_describe_mode_specific_exits(self):
        app = Path(cli.__file__).resolve().parents[1]
        standard = (app / "APPLICATION_STANDARD.md").read_text(encoding="utf-8")
        readme = (app / "validator/README.md").read_text(encoding="utf-8")
        self.assertNotIn("Exit 0: contract passes.", standard)
        for text in (standard, readme):
            for term in ("--digest", "contract_valid=false", "PIPELINE_DIGEST",
                         "--help", "argument-parsing", "INPUT_OR_CONFIGURATION"):
                self.assertIn(term, text)


if __name__ == "__main__":
    unittest.main()
