"""Versioned A2 current-30 source invariants; historical verifiers are untouched."""
import unittest
import localized_prefix_support as frozen
import pr113_a2_successor_identity as legacy
import pr113_a2_successor_identity_v2 as successor


def fixture():
    old={path:("100644","a"*40)
         for path in successor.PINNED_MODIFIED_PROVIDERS}
    old.update({
        "PermanssonResearch.lean":("100644",frozen.ROOT_BLOB),
        "lean-toolchain":("100644","b"*40),
        "lake-manifest.json":("100644","c"*40),
        "README.md":("100644","d"*40),
    })
    newer=dict(old)
    for path,oid in successor.PINNED_MODIFIED_PROVIDERS.items():
        newer[path]=("100644",oid)
    newer["PermanssonResearch.lean"]=("100644","e"*40)
    newer["README.md"]=("100644","f"*40)
    for path,oid in frozen.ACCEPTED_A2_PROOF_BLOBS.items():
        newer[path]=("100644",oid)
    for path,oid in successor.INHERITED_A2_VERIFIERS.items():
        newer[path]=("100644",oid)
    return old,newer


class SuccessorA2Active30Tests(unittest.TestCase):
    def test_exact_thirteen_changed_original_providers_plus_five_additions(self):
        old,current=fixture()
        report=successor.reconcile(old,current)
        self.assertEqual(len(report["pinned_successor_provider_paths"]),13)
        self.assertEqual(len(successor.INHERITED_A2_VERIFIERS),2)
        self.assertEqual(len(legacy.INHERITED_A2_VERIFIERS),3)
        self.assertEqual(len(frozen.ACCEPTED_A2_PROOF_BLOBS),4)
        self.assertEqual(successor.PINNED_MODIFIED_PROVIDERS[
            "verification/research/test_localized_prefix_compiler.py"],
            "8bc0fdd8ae3442844187db6f5787d22011dd899a")
        self.assertNotEqual(
            successor.PINNED_MODIFIED_PROVIDERS[
                "verification/integrity/workflow_contract.py"],
            legacy.PINNED_MODIFIED_PROVIDERS[
                "verification/integrity/workflow_contract.py"])

    def test_a2_source_pin_delta_is_exact_and_no_wildcard(self):
        old,current=fixture()
        for changed in successor.PINNED_MODIFIED_PROVIDERS:
            altered=dict(current)
            altered[changed]=("100644","0"*40)
            with self.subTest(changed=changed),self.assertRaises(frozen.GuardError):
                successor.reconcile(old,altered)
        for protected in successor.INHERITED_A2_VERIFIERS:
            altered=dict(current)
            altered[protected]=("100644","1"*40)
            with self.subTest(protected=protected),self.assertRaises(frozen.GuardError):
                successor.reconcile(old,altered)

    def test_v1_preactivation_receipt_cannot_satisfy_v2(self):
        old,current=fixture()
        previous=dict(current)
        old_pin=legacy.PINNED_MODIFIED_PROVIDERS[
            "verification/integrity/workflow_contract.py"]
        previous["verification/integrity/workflow_contract.py"]=("100644",old_pin)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(old,previous)
        self.assertNotEqual(successor.FORMAT,legacy.FORMAT)

    def test_new_unapproved_mathematical_provider_not_allowed(self):
        old,current=fixture()
        old["PermanssonResearch/InjectedTheorem.lean"]=("100644","1"*40)
        current["PermanssonResearch/InjectedTheorem.lean"]=("100644","2"*40)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(old,current)

    def test_history_cannot_change_toolchain_or_proofs(self):
        old,current=fixture()
        for key in ("lean-toolchain","lake-manifest.json",
                    *frozen.ACCEPTED_A2_PROOF_BLOBS):
            altered=dict(current)
            altered[key]=("100644","0"*40)
            with self.subTest(key=key),self.assertRaises(frozen.GuardError):
                successor.reconcile(old,altered)
