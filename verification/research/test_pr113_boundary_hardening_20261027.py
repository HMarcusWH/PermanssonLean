"""Non-authorizing counterexamples for PR113 versioned intake hardening."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

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
    """Exercise the actual complete v2 A2 validator, without stubbing it.

    Synthetic Lean logs are only diagnostic fixtures: these tests never
    represent an original historical Lean execution or security acceptance.
    """
    PREFIX = "historical_original_A2"
    MUTANT = "wrong_reported_effect"
    EXPECTED_STATUS = "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING"

    def fixture(self, log):
        # Reuse the complete, source-mutated four-negative fixture so all
        # four real source probes, the exact positive, artifacts and command
        # byte digests remain part of the versioned evidence contract.
        from localized_prefix_gate import MUTATIONS, mutated_source
        from test_pr113_semantic_receipt_v2 import fixture as full_fixture
        files = full_fixture(self.PREFIX, MUTATIONS, mutated_source,
                             mode="focused")
        receipt_path = self.PREFIX + "/receipt.json"
        row = json.loads(files[receipt_path])
        matched = [entry for entry in row["commands"]
                   if entry["label"] == self.MUTANT]
        self.assertEqual(len(matched), 1)
        command = matched[0]
        log_path = self.PREFIX + "/" + command["log"]
        original_bytes = log.encode("utf-8")
        files[log_path] = original_bytes
        command["log_sha256"] = hashlib.sha256(original_bytes).hexdigest()
        row["artifacts"][command["log"]] = {
            "sha256": command["log_sha256"], "bytes": len(original_bytes)}
        files[receipt_path] = (
            json.dumps(row, sort_keys=True) + "\n").encode("utf-8")
        return self.PREFIX, files, row

    def _verify(self, files, prefix):
        from localized_prefix_gate import MUTATIONS
        return validate_compiler_receipt_v2(
            files, prefix, self.EXPECTED_STATUS, MUTATIONS)

    def test_import_syntax_resource_and_wrong_file_fail_closed(self):
        for log in (
            "wrong_reported_effect.lean:1:0: error: unknown module prefix 'Missing'",
            "wrong_reported_effect.lean:1:0: error: unexpected token ')'; expected term",
            "Other.lean:1:0: error: unsolved goals",
            "wrong_reported_effect.lean:1:0: error: deterministic timeout",
            "wrong_reported_effect.lean:1:0: error: failed to synthesize",
        ):
            with self.subTest(log=log):
                prefix, files, row = self.fixture(log)
                with self.assertRaises(original.InfrastructureError):
                    self._verify(files, prefix)

    def test_intended_goal_failure_with_correct_filename_is_distinguished(self):
        prefix, files, row = self.fixture(
            "wrong_reported_effect.lean:1:0: error: unsolved goals\n"
            "case : False")
        verified, identity = self._verify(files, prefix)
        self.assertEqual(verified, row)
        self.assertEqual(identity, hashlib.sha256(
            files[prefix + "/receipt.json"]).hexdigest())
        self.assertEqual(verified["mode"], "focused")
        self.assertEqual(len(verified["mutations"]), 4)
        self.assertTrue(all(
            source in {command["label"] for command in verified["commands"]}
            for source in ("source_1", "source_2", "source_3", "source_4")))

    def test_missing_or_duplicated_source_probe_never_passes(self):
        prefix, files, row = self.fixture(
            "wrong_reported_effect.lean:1:0: error: unsolved goals\n"
            "case : False")
        for variant in ("missing", "duplicate"):
            altered = dict(files)
            receipt = json.loads(files[prefix + "/receipt.json"])
            if variant == "missing":
                receipt["commands"] = [
                    command for command in receipt["commands"]
                    if command["label"] != "source_4"]
            else:
                copied = next(command for command in receipt["commands"]
                              if command["label"] == "source_4")
                receipt["commands"].append(dict(copied))
            altered[prefix + "/receipt.json"] = json.dumps(receipt).encode()
            with self.subTest(variant=variant), self.assertRaises(
                    original.InfrastructureError):
                self._verify(altered, prefix)


if __name__ == "__main__":
    unittest.main()
