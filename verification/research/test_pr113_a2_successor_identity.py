"""Source-identity successor contract tests; NO simulated compiler approval."""
import copy
import unittest

import localized_prefix_support as inherited
import pr113_a2_successor_identity as successor


def fixture():
    old = {p: ("100644", "a"*40)
           for p in successor.PINNED_MODIFIED_PROVIDERS}
    old.update({
        "PermanssonResearch.lean": ("100644", inherited.ROOT_BLOB),
        "lean-toolchain": ("100644", "b"*40),
        "lake-manifest.json": ("100644", "c"*40),
        "README.md": ("100644", "d"*40),
    })
    new = dict(old)
    for p, sha in successor.PINNED_MODIFIED_PROVIDERS.items():
        new[p] = ("100644", sha)
    new["PermanssonResearch.lean"] = ("100644", "e"*40)
    new["README.md"] = ("100644", "f"*40)
    for p, sha in inherited.ACCEPTED_A2_PROOF_BLOBS.items():
        new[p] = ("100644", sha)
    for p, sha in successor.INHERITED_A2_VERIFIERS.items():
        new[p] = ("100644", sha)
    return old, new


class SuccessorIdentityPolicyTests(unittest.TestCase):
    def test_exact_delta_passes_only_as_candidate(self):
        old, current = fixture()
        result = successor.reconcile(old, current)
        self.assertEqual(len(result["pinned_successor_provider_paths"]), 12)
        self.assertEqual(result["accepted_a2_proof_blobs"], 4)

    def test_any_changed_trusted_provider_fails(self):
        old, current = fixture()
        for p in successor.PINNED_MODIFIED_PROVIDERS:
            bad = dict(current)
            bad[p] = ("100644", "f"*40)
            with self.subTest(path=p), self.assertRaises(inherited.GuardError):
                successor.reconcile(old, bad)

    def test_new_unreviewed_baseline_change_fails(self):
        old, current = fixture()
        old["verification/archive/offline_smoke.py"] = ("100644", "a"*40)
        current["verification/archive/offline_smoke.py"] = ("100644", "b"*40)
        with self.assertRaises(inherited.GuardError):
            successor.reconcile(old, current)

    def test_history_and_mathematics_cannot_be_deleted_or_mutated(self):
        old, current = fixture()
        deleted = dict(current)
        del deleted["lean-toolchain"]
        with self.assertRaises(inherited.GuardError):
            successor.reconcile(old, deleted)
        for p in inherited.ACCEPTED_A2_PROOF_BLOBS:
            changed = dict(current)
            changed[p] = ("100644", "1"*40)
            with self.subTest(proof=p), self.assertRaises(inherited.GuardError):
                successor.reconcile(old, changed)

    def test_historical_verifier_remains_byte_pinned(self):
        old, current = fixture()
        for p in successor.INHERITED_A2_VERIFIERS:
            bad = dict(current)
            bad[p] = ("100644", "2"*40)
            with self.subTest(path=p), self.assertRaises(inherited.GuardError):
                successor.reconcile(old, bad)

    def test_pin_and_reviewable_doc_modes_cannot_change(self):
        old, current = fixture()
        for p in ("lake-manifest.json", "lean-toolchain"):
            changed = dict(current)
            changed[p] = ("100644", "1"*40)
            with self.subTest(path=p), self.assertRaises(inherited.GuardError):
                successor.reconcile(old, changed)
        changed = dict(current)
        changed["README.md"] = ("100755", "f"*40)
        with self.assertRaises(inherited.GuardError):
            successor.reconcile(old, changed)


if __name__ == "__main__":
    unittest.main()
