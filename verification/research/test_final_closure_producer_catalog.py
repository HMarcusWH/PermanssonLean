"""Pure adversarial producer-catalog tests; none is real GitHub attestation."""
import copy
import unittest

from final_closure_producer_catalog import entries, ProducerCatalogError, FORMAT
from final_closure_candidate_artifact_auth import KINDS

H = "a" * 40


def fixture():
    entries_ = []
    count = 0
    for kind, spec in KINDS.items():
        for shard in range(spec["count"]):
            count += 1
            entries_.append({
                "kind": kind,
                "shard": shard,
                "run_id": 9000 + count,
                "artifact_id": 10000 + count,
                "zip_file": "artifact-%03d.zip" % count,
            })
    return {"format": FORMAT, "head_sha": H, "artifacts": entries_}


class ProducerCatalogTests(unittest.TestCase):
    def test_exact_full_inventory_remains_unapproved_candidate(self):
        items = entries(fixture(), H)
        self.assertEqual(len(items), 21)
        self.assertEqual({x["kind"] for x in items},
                         {"append", "legacy", "compiler"})
        self.assertEqual(len([x for x in items if x["kind"] == "compiler"]), 4)
        self.assertEqual(len([x for x in items if x["kind"] == "append"]), 9)
        self.assertEqual(len([x for x in items if x["kind"] == "legacy"]), 8)

    def test_missing_extra_and_duplicate_shards_fail_closed(self):
        cases = []
        no_one = fixture()
        no_one["artifacts"].pop()
        cases.append(no_one)
        duplicate = fixture()
        duplicate["artifacts"][0] = dict(duplicate["artifacts"][1])
        cases.append(duplicate)
        changed_index = fixture()
        changed_index["artifacts"][0]["shard"] = 100
        cases.append(changed_index)
        for candidate in cases:
            with self.subTest(case=candidate["artifacts"][:2]):
                with self.assertRaises(ProducerCatalogError):
                    entries(candidate, H)

    def test_invalid_head_duplicate_ids_and_unsafe_paths_fail_closed(self):
        base = fixture()
        for value in ("../evil.zip", "/tmp/shadow.zip", "dir/file.zip",
                      "x\\evil.zip", "payload.json", ".zip"):
            payload = copy.deepcopy(base)
            payload["artifacts"][0]["zip_file"] = value
            with self.subTest(name=value), self.assertRaises(ProducerCatalogError):
                entries(payload, H)
        bad = copy.deepcopy(base)
        bad["artifacts"][0]["artifact_id"] = bad["artifacts"][1]["artifact_id"]
        with self.assertRaises(ProducerCatalogError):
            entries(bad, H)
        for wrong in (True, 9, "", "a"*39, "b"*40):
            with self.subTest(head=wrong), self.assertRaises(ProducerCatalogError):
                entries(base, wrong)

    def test_status_or_approval_fields_cannot_be_smuggled(self):
        payload = fixture()
        payload["artifacts"][0]["approved"] = True
        with self.assertRaises(ProducerCatalogError):
            entries(payload, H)
        payload = fixture()
        payload["format"] = "Permansson.FakeApprovedRelease.v1"
        with self.assertRaises(ProducerCatalogError):
            entries(payload, H)


if __name__ == "__main__":
    unittest.main()
