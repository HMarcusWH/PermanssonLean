"""Non-authorizing counterexamples for PR113 versioned intake hardening."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from pr113_boundary_io import (
    BoundaryError, strict_json_object, detached_destination,
    approved_artifact_url, BoundedArtifactRedirect,
)
from pr113_semantic_receipt_v2 import validate_compiler_receipt_v2
import infrastructure_acceptance as original


class JSONBoundaryTests(unittest.TestCase):
    def test_duplicate_keys_reject_at_every_depth(self):
        for value in (
            b'{"status":"fail","status":"success"}',
            b'{"scope":{"approved":false,"approved":true}}',
            b'{"sources":[{"sha":"a","sha":"b"}]}',
        ):
            with self.subTest(raw=value), self.assertRaises(BoundaryError):
                strict_json_object(value)

    def test_nonfinite_invalid_scalars_and_bounds(self):
        for value in (b'[]', b'null', b'{"v":NaN}', b'{"v":Infinity}', b''):
            with self.subTest(raw=value), self.assertRaises(BoundaryError):
                strict_json_object(value)
        self.assertEqual(strict_json_object(b'{"ok":true}'), {"ok": True})
        with self.assertRaises(BoundaryError):
            strict_json_object(b'{"ok":true}', max_bytes=3)


class DetachedPathTests(unittest.TestCase):
    def test_parent_traversal_never_writes_to_source(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            source.mkdir()
            outside = root / "outside"
            outside.mkdir()
            malicious = outside / ".." / "source" / "unexpected.json"
            with self.assertRaises(BoundaryError):
                detached_destination(malicious, source)
            self.assertFalse((source / "unexpected.json").exists())

    def test_symlink_and_existing_output_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source"
            source.mkdir()
            target = root / "target"
            target.mkdir()
            link = root / "alias"
            link.symlink_to(target)
            with self.assertRaises(BoundaryError):
                detached_destination(link / "receipt.json", source)
            output = target / "receipt.json"
            self.assertEqual(detached_destination(output, source), output.resolve())
            output.write_text("{}")
            with self.assertRaises(BoundaryError):
                detached_destination(output, source)


class RedirectTests(unittest.TestCase):
    def test_every_hop_is_validated(self):
        allowed = "https://something.blob.core.windows.net/path?sig=a"
        self.assertTrue(approved_artifact_url(allowed))
        for url in (
            "http://something.blob.core.windows.net/path",
            "https://evil.example/path",
            "https://api.github.com:444/path",
            "https://name:password@api.github.com/path",
        ):
            self.assertFalse(approved_artifact_url(url), url)
        handler = BoundedArtifactRedirect()
        from urllib.request import Request
        request = Request("https://api.github.com/repos/HMarcusWH/PermanssonLean/a",
                          headers={"Authorization": "Bearer SECRET"})
        child = handler.redirect_request(request, None, 302, "Found", {},
                                         allowed)
        self.assertFalse(any(key.lower() == "authorization"
                             for key in (*child.headers, *child.unredirected_hdrs)))
        with self.assertRaises(BoundaryError):
            handler.redirect_request(child, None, 302, "Found", {},
                                     "http://evil.example/path")
        handler = BoundedArtifactRedirect()
        for count in range(5):
            handler.redirect_request(request, None, 302, "Found", {}, allowed)
        with self.assertRaises(BoundaryError):
            handler.redirect_request(request, None, 302, "Found", {}, allowed)


class A2DiagnosticTests(unittest.TestCase):
    def fixture(self, log):
        prefix = "historical_original_A2"
        raw_positive = b"example theorem valid : True := trivial"
        raw_mutant = b"example theorem invalid : False := by simp"
        artifacts = {
            prefix + "/PositiveControl.lean": raw_positive,
            prefix + "/bad_math.lean": raw_mutant,
            prefix + "/01_bad_math.log": log.encode(),
        }
        row = {
            "commands": [
                {"label": "compiler_version", "returncode": 0},
                {"label": "research_build", "returncode": 0},
                {"label": "signatures_axioms", "returncode": 0},
                {"label": "positive_fixture", "returncode": 0},
                {"label": "bad_math", "returncode": 1,
                 "log": "01_bad_math.log"},
            ],
            "mutations": {
                "bad_math": {
                    "positive_source_sha256": hashlib.sha256(raw_positive).hexdigest(),
                    "mutant_source_sha256": hashlib.sha256(raw_mutant).hexdigest(),
                },
            },
        }
        return prefix, artifacts, row

    def test_import_and_syntax_failures_do_not_count_as_mathematics(self):
        for log in (
            "bad_math.lean:1:0: error: unknown module prefix 'Missing'",
            "bad_math.lean:1:0: error: unexpected token ')'; expected term",
            "Other.lean:1:0: error: unsolved goals",
        ):
            with self.subTest(log=log):
                prefix, files, row = self.fixture(log)
                with patch.object(original, "verify_compiler_receipt",
                                  return_value=(row, "hash")):
                    with self.assertRaises((original.InfrastructureError, ValueError)):
                        validate_compiler_receipt_v2(files, prefix, "OK",
                                                      {"bad_math": None})

    def test_intended_goal_failure_with_correct_filename_is_distinguished(self):
        prefix, files, row = self.fixture(
            "bad_math.lean:1:0: error: unsolved goals\ncase : False")
        with patch.object(original, "verify_compiler_receipt",
                          return_value=(row, "original")):
            verified, identity = validate_compiler_receipt_v2(
                files, prefix, "OK", {"bad_math": None})
        self.assertEqual(verified, row)
        self.assertEqual(identity, "original")


if __name__ == "__main__":
    unittest.main()
