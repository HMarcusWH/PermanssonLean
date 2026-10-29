"""Corrected-head dependency bridge rejection tests; inputs are synthetic."""
from __future__ import annotations
import copy
import hashlib
import json
import unittest
import pr113_a2_dependency_bridge_v2 as bridge
import pr113_historical_a2_baseline_v1 as baseline

H = "a" * 40


def encoded(value):
    return (json.dumps(value, sort_keys=True) + "\n").encode()


def fixture():
    manifest = encoded({"packagesDir": ".lake/packages", "packages": [
        {"name": "mathlib", "type": "git", "rev": bridge.MATHLIB_REV}]})
    row = {"format": bridge.FORMAT, "status": bridge.STATUS,
           "historical_head": baseline.REPLAY_HEAD,
           "historical_tree_sha": baseline.REPLAY_TREE,
           "historical_introducer": baseline.INTRODUCER,
           "current_head": H, "manifest_sha256": hashlib.sha256(manifest).hexdigest(),
           "pinned_packages": {"mathlib": bridge.MATHLIB_REV},
           "original_verifier_modified": False, "historical_project_proofs_reused": False,
           "independent_security_review": False, "mathematical_acceptance": False}
    return manifest, row


class CorrectedDependencyBridgeTests(unittest.TestCase):
    def verify(self, manifest, row):
        raw = encoded(row)
        return bridge.verify_A2_dependency_bridge(
            {"historical_dependency_bridge.json": raw}, H, manifest_raw=manifest)

    def test_exact_corrected_baseline_roundtrip(self):
        manifest, row = fixture()
        self.assertEqual(self.verify(manifest, row), hashlib.sha256(encoded(row)).hexdigest())

    def test_old_or_mixed_baseline_and_contract_versions_rejected(self):
        manifest, row = fixture()
        for key, value in (("format", "Permansson.PR113.HistoricalA2DependencyBridge.v1"),
                           ("historical_head", baseline.INTRODUCER),
                           ("historical_tree_sha", "f" * 40),
                           ("historical_introducer", baseline.REPLAY_HEAD),
                           ("current_head", "b" * 40), ("manifest_sha256", "0" * 64)):
            with self.subTest(field=key), self.assertRaises(bridge.DependencyBridgeError):
                self.verify(manifest, dict(row, **{key: value}))

    def test_approval_and_project_build_reuse_are_not_inferred(self):
        manifest, row = fixture()
        for key in ("original_verifier_modified", "historical_project_proofs_reused",
                    "independent_security_review", "mathematical_acceptance"):
            for false_like in (True, 0, "false", None):
                with self.subTest(field=key, value=false_like), self.assertRaises(bridge.DependencyBridgeError):
                    self.verify(manifest, dict(row, **{key: false_like}))

    def test_missing_or_extra_bridge_fields_rejected(self):
        manifest, row = fixture()
        for key in row:
            bad = dict(row); bad.pop(key)
            with self.subTest(key=key), self.assertRaises(bridge.DependencyBridgeError):
                self.verify(manifest, bad)
        with self.assertRaises(bridge.DependencyBridgeError):
            self.verify(manifest, dict(row, accepted=True))

    def test_wrong_dependency_set_rejected_even_with_correct_metadata(self):
        manifest, row = fixture()
        with self.assertRaises(bridge.DependencyBridgeError):
            self.verify(manifest, dict(row, pinned_packages={"mathlib": "0" * 40}))

    def test_manifest_corruption_not_solved_by_rehashing(self):
        manifest, row = fixture()
        original = json.loads(manifest)
        cases = []
        bad = copy.deepcopy(original); bad["packagesDir"] = "../packages"; cases.append(bad)
        bad = copy.deepcopy(original); bad["packages"][0]["name"] = "../mathlib"; cases.append(bad)
        bad = copy.deepcopy(original); bad["packages"][0]["rev"] = "f" * 40; cases.append(bad)
        bad = copy.deepcopy(original); bad["packages"].append(dict(bad["packages"][0])); cases.append(bad)
        bad = copy.deepcopy(original); bad["packages"][0]["type"] = "path"; cases.append(bad)
        for value in cases:
            raw = encoded(value)
            forged = dict(row, manifest_sha256=hashlib.sha256(raw).hexdigest())
            with self.subTest(value=value), self.assertRaises(bridge.DependencyBridgeError):
                self.verify(raw, forged)

    def test_duplicate_nonfinite_and_nonobject_json_rejected(self):
        manifest, row = fixture()
        for raw in (b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}',
                    b'{"x":1e999}', b'[]', b'null', b'{}'):
            with self.subTest(raw=raw), self.assertRaises(bridge.DependencyBridgeError):
                bridge.verify_A2_dependency_bridge(
                    {"historical_dependency_bridge.json": raw}, H, manifest_raw=manifest)

    def test_exact_manifest_bytes_not_stripped(self):
        manifest, row = fixture()
        with self.assertRaises(bridge.DependencyBridgeError):
            self.verify(manifest.rstrip(), row)

    def test_missing_or_oversized_bridge_bytes_rejected(self):
        manifest, row = fixture()
        for raw in (None, b"", b" " * (1024 * 1024 + 1)):
            with self.subTest(size=None if raw is None else len(raw)), self.assertRaises(bridge.DependencyBridgeError):
                bridge.verify_A2_dependency_bridge(
                    {"historical_dependency_bridge.json": raw}, H, manifest_raw=manifest)


if __name__ == "__main__":
    unittest.main()
