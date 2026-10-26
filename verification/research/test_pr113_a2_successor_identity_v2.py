"""Versioned A2 current-30 source invariants; historical verifiers are untouched."""
import unittest
from unittest import mock
from pathlib import Path
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
    # This test did not exist at original PR79 BASE.
    assert successor.LATE_A2_TEST not in old
    newer[successor.LATE_A2_TEST]=(
        "100644",successor.LATE_A2_TEST_PROPOSED_BLOB)
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
    def test_exact_twelve_original_modified_and_one_historically_late_test(self):
        old,current=fixture()
        report=successor.reconcile(old,current)
        self.assertEqual(len(report["pinned_successor_provider_paths"]),12)
        self.assertNotIn(successor.LATE_A2_TEST,old)
        self.assertEqual(report["late_introduced_A2_test"],successor.LATE_A2_TEST)
        self.assertEqual(report["late_A2_original_introducer"],
                         successor.HISTORICAL_A2_INTRODUCER)
        self.assertEqual(report["late_A2_original_blob"],
                         successor.LATE_A2_TEST_ORIGINAL_BLOB)
        self.assertEqual(len(successor.INHERITED_A2_VERIFIERS),2)
        self.assertEqual(len(legacy.INHERITED_A2_VERIFIERS),3)
        self.assertEqual(len(frozen.ACCEPTED_A2_PROOF_BLOBS),4)
        self.assertEqual(successor.LATE_A2_TEST_PROPOSED_BLOB,
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
        for candidate in ("0000000000000000000000000000000000000000",
                          successor.LATE_A2_TEST_ORIGINAL_BLOB):
            changed=dict(current)
            changed[successor.LATE_A2_TEST]=("100644",candidate)
            with self.assertRaises(frozen.GuardError):
                successor.reconcile(old,changed)
        absent=dict(current)
        absent.pop(successor.LATE_A2_TEST)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(old,absent)
        spoofed=dict(old)
        spoofed[successor.LATE_A2_TEST]=(
            "100644",successor.LATE_A2_TEST_ORIGINAL_BLOB)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(spoofed,current)
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

    def test_ordered_direct_H_and_synthetic_S_identity(self):
        B=successor.PR113_BASE
        H="a"*40
        S="b"*40
        TREE="c"*40
        def authenticated(root,*args):
            mapping={
                ("rev-parse","HEAD"):S,
                ("rev-parse",H+"^{tree}"):TREE,
                ("rev-parse","HEAD^{tree}"):TREE,
                ("show","-s","--format=%P",S):B+" "+H,
            }
            return mapping[args]
        with mock.patch.object(frozen,"git_text",side_effect=authenticated):
            self.assertEqual(
                successor.check_checkout_identity(Path("."),H),(S,TREE))
        def direct(root,*args):
            if args==("rev-parse","HEAD"):
                return H
            return authenticated(root,*args)
        with mock.patch.object(frozen,"git_text",side_effect=direct):
            self.assertEqual(
                successor.check_checkout_identity(Path("."),H),(H,TREE))
        for parents in (H+" "+B,B+" "+"d"*40,B+" "+H+" "+"e"*40):
            def fake(root,*args):
                if args==("show","-s","--format=%P",S):
                    return parents
                return authenticated(root,*args)
            with mock.patch.object(frozen,"git_text",side_effect=fake):
                with self.assertRaises(frozen.GuardError):
                    successor.check_checkout_identity(Path("."),H)
        def false_tree(root,*args):
            if args==("rev-parse","HEAD^{tree}"):
                return "f"*40
            return authenticated(root,*args)
        with mock.patch.object(frozen,"git_text",side_effect=false_tree):
            with self.assertRaises(frozen.GuardError):
                successor.check_checkout_identity(Path("."),H)

    def test_original_historical_a2_test_git_identity_is_not_assumed(self):
        self.assertEqual(successor.HISTORICAL_A2_INTRODUCER,
                         "f71a76032b169aac7bfe0694aa715339a94d4e05")
        self.assertEqual(successor.LATE_A2_TEST_ORIGINAL_BLOB,
                         "c0f49038ea9b590720c78be85968eb63f5ac820f")
        self.assertNotEqual(successor.LATE_A2_TEST_ORIGINAL_BLOB,
                            successor.LATE_A2_TEST_PROPOSED_BLOB)

    def test_history_cannot_change_toolchain_or_proofs(self):
        old,current=fixture()
        for key in ("lean-toolchain","lake-manifest.json",
                    *frozen.ACCEPTED_A2_PROOF_BLOBS):
            altered=dict(current)
            altered[key]=("100644","0"*40)
            with self.subTest(key=key),self.assertRaises(frozen.GuardError):
                successor.reconcile(old,altered)
