"""Synthetic 76-owner coverage is independent of ZIP shard count."""
import unittest
from copy import deepcopy

from pr113_owner_partition_v3 import (
    original_owner_artifacts, OwnerPartitionError, FORMAT, CLAIMS,
)


def complete():
    cases = [f"C-{i:02d}" for i in range(1, 46)]
    return {
        "format": FORMAT,
        "source_controls_accepted": False,
        "independent_security_review": False,
        "mathematical_approval": False,
        "producers": [
            {"artifact_id": 101, "owners": [
                {"kind": "original_positive", "owner_id": case} for case in cases]},
            {"artifact_id": 102, "owners": [
                {"kind": "legacy_negative", "owner_id": case} for case in cases[:20]]},
            {"artifact_id": 103, "owners": [
                {"kind": "claim_pair", "owner_id": claim} for claim in sorted(CLAIMS)]},
        ],
    }


class PartitionTests(unittest.TestCase):
    def test_76_real_owner_obligations_can_live_in_three_artifacts(self):
        self.assertEqual(original_owner_artifacts(complete()), [101, 102, 103])

    def test_missing_owner_duplicate_artifact_and_false_approval_fail(self):
        for edit in (
            lambda p: p["producers"][0]["owners"].pop(),
            lambda p: p["producers"][2].update(artifact_id=102),
            lambda p: p["producers"][1]["owners"].append(
                dict(p["producers"][1]["owners"][0])),
            lambda p: p.update(mathematical_approval=True),
            lambda p: p["producers"][0]["owners"][0].update(kind=[]),
            lambda p: p["producers"][1]["owners"][0].update(owner_id="FOREIGN"),
            lambda p: p["producers"][2]["owners"][0].update(owner_id="NOT_A_CLAIM"),
        ):
            candidate=deepcopy(complete())
            edit(candidate)
            with self.subTest(edit=edit), self.assertRaises(OwnerPartitionError):
                original_owner_artifacts(candidate)


if __name__ == "__main__":
    unittest.main()
