"""Review 23 unchanged originals, exact two replacements, five additions."""
import json
from pathlib import Path
import unittest
from unittest import mock

import pr113_atomic_migration_preview as preview
import pr113_workflow_profile_v2 as v2

def active30(root):
    count=len(list((root/".github/workflows").glob("*.yml")))
    if count not in (25,30):
        raise AssertionError("only exact 25 or exact 30 profile is valid")
    return count==30


def fake_source():
    ROOT=Path(__file__).resolve().parents[2]
    head=preview.git("rev-parse","HEAD")
    return head,ROOT

class AtomicMigrationPreviewTests(unittest.TestCase):
    def test_real_source_preview_is_honestly_unapproved(self):
        H,root=fake_source()
        if active30(root):
            actual=v2.audit(root,H,phase="active")
            self.assertEqual(actual["current_reviewed_workflow_count"],30)
            self.assertEqual(actual["retained_historical_count"],23)
            self.assertFalse(actual["independent_security_review"])
            return
        actual=preview.preview(H)
        self.assertEqual(actual["proposed_total_workflows"],30)
        self.assertEqual(actual["historical_preserved_workflows"],23)
        self.assertEqual(actual["review_pending_mandatory_replacements"],2)
        self.assertEqual(actual["review_pending_additional_workflows"],5)
        self.assertEqual(len(actual["virtual_source_members"]),30)
        self.assertEqual(len(actual["additional_original_test_replacements"]),2)
        self.assertEqual(len(actual["review_pending_integrity_tooling_replacements"]),2)
        self.assertEqual(actual["versioned_workflow_allowlist_count"],30)
        self.assertRegex(actual["virtual_profile_sha256"],"^[a-f0-9]{64}$")
        for field in (
            "independent_security_review","owner_activation_authorized",
            "merge_authorized","mathematical_acceptance",
            "publication_authorized","active_workflow_set_modified"):
            self.assertIs(actual[field],False)

    def test_forged_head_or_staged_yaml_modification_is_rejected(self):
        H,_=fake_source()
        root=Path(__file__).resolve().parents[2]
        if active30(root):
            with self.assertRaises(v2.ToolingMigrationError):
                v2.audit(root,"f"*40,phase="active")
            original_blob=v2._blob
            def altered(repo,head,path):
                oid,source=original_blob(repo,head,path)
                if path==".github/workflows/research-lean.yml":
                    return oid,source+"\n# unreviewed exact-active mutation\n"
                return oid,source
            with mock.patch.object(v2,"_blob",side_effect=altered):
                with self.assertRaises(v2.ToolingMigrationError):
                    v2.audit(root,H,phase="active")
            return
        with self.assertRaises(preview.TransitionError):
            preview.preview("f"*40)
        original_git=preview.git
        target="docs/operations/pr113_required_gate_replacement_unapproved/research_lean_full.yml"
        def mutated(*args):
            if args==("show",H+":"+target):
                return original_git(*args)+"\n# unauthorized modification\n"
            return original_git(*args)
        with self.assertRaises(preview.TransitionError):
            preview.preview(H,git=mutated)

    def test_modified_v2_integrity_contract_or_suite_is_rejected(self):
        H,_=fake_source()
        original_git=preview.git
        root=Path(__file__).resolve().parents[2]
        if active30(root):
            from pr113_tooling_migration import git as genuine_git
            def changed(repo,*args):
                if args==("show",H+":"+v2.CONTRACT):
                    return genuine_git(repo,*args)+b"\n# unauthorized contract\n"
                return genuine_git(repo,*args)
            with mock.patch.object(v2,"git",side_effect=changed):
                with self.assertRaises(v2.ToolingMigrationError):
                    v2.audit(root,H,phase="active")
            return
        for name in ("workflow_contract_v2.py","test_workflow_v2.py"):
            target=("docs/operations/pr113_required_gate_replacement_unapproved/"
                    +name)
            def changed(*args):
                if args==("show",H+":"+target):
                    return original_git(*args)+"\n# unauthorized change\n"
                return original_git(*args)
            with self.subTest(name=name),self.assertRaises(
                    preview.TransitionError):
                preview.preview(H,git=changed)

    def test_missing_source_or_invalid_old_profile_rejected(self):
        H,_=fake_source()
        root=Path(__file__).resolve().parents[2]
        if active30(root):
            old=v2._historical(root,H)
            with mock.patch.object(v2,"_historical",
                                   return_value=dict(list(old.items())[:-1])):
                with self.assertRaises(v2.ToolingMigrationError):
                    v2.audit(root,H,phase="active")
            return
        def damaged(h):
            return {"status":"CANDIDATE","original_workflow_count":25}
        with self.assertRaises(preview.TransitionError):
            preview.preview(H,old_audit=damaged)

    def test_staged_executables_must_be_exact_v2_even_when_manifest_is_rehashed(self):
        import hashlib
        H,root=fake_source()
        phase=v2.source_phase(root,H)
        if phase=="active":
            original_blob=v2._blob
            target=".github/workflows/research-lean.yml"
            origin_oid,origin_source=original_blob(root,H,target)
            token="pr113_historical_artifact_delivery_v2.py"
            self.assertEqual(origin_source.count(token),1)
            for variant in ("v1","missing","duplicated"):
                with self.subTest(variant=variant):
                    if variant=="v1":
                        forged=origin_source.replace(token,
                            "pr113_historical_artifact_delivery.py")
                    elif variant=="missing":
                        forged=origin_source.replace(token,
                            "pr113_invalid_transport.py")
                    else:
                        forged=origin_source.replace(
                            token,token+" # pr113_historical_artifact_delivery_v2.py")
                    def wrong_source(repo,head,path):
                        if path==target:
                            return origin_oid,forged
                        return original_blob(repo,head,path)
                    with mock.patch.object(v2,"_blob",side_effect=wrong_source):
                        with self.assertRaisesRegex(v2.ToolingMigrationError,
                                                   "activated workflow differs"):
                            v2.audit(root,H,phase="active")
            return
        real=preview.git
        full_path=preview.FULL
        full=json.loads(preview.raw(H,full_path))
        for variant in ("v1", "missing", "duplicated"):
            with self.subTest(variant=variant):
                candidate=full["full_replacements"][0]
                staged=candidate["staged_source"]
                original=preview.raw(H,staged)
                token=b"pr113_historical_artifact_delivery_v2.py"
                self.assertEqual(original.count(token),1)
                if variant=="v1":
                    source=original.replace(token,b"pr113_historical_artifact_delivery.py")
                elif variant=="missing":
                    source=original.replace(token,b"pr113_invalid_transport.py")
                else:
                    source=original.replace(token,token+b" # pr113_historical_artifact_delivery_v2.py")
                altered=json.loads(json.dumps(full))
                altered["full_replacements"][0]["git_blob_oid"]=preview.git_blob_oid(source)
                def fake(*args):
                    if args==("show",H+":"+staged):
                        return source.decode()
                    if args==("show",H+":"+full_path):
                        return json.dumps(altered)+"\n"
                    return real(*args)
                with self.assertRaisesRegex(preview.TransitionError,
                                            "mandatory candidate source byte drift"):
                    preview.preview(H,git=fake)

    def test_artifact_delivery_module_source_is_checked_independently(self):
        H,root=fake_source()
        phase=v2.source_phase(root,H)
        if phase=="active":
            original_blob=v2._blob
            path="verification/research/pr113_historical_artifact_delivery_v2.py"
            oid,source=original_blob(root,H,path)
            def changed(repo,head,source_path):
                if source_path==path:
                    return oid,source+"\n# tampered artifact deliverer\n"
                return original_blob(repo,head,source_path)
            with mock.patch.object(v2,"_blob",side_effect=changed):
                with self.assertRaisesRegex(v2.ToolingMigrationError,
                                            "versioned transport source"):
                    v2.audit(root,H,phase="active")
            return
        real=preview.git
        path="verification/research/pr113_historical_artifact_delivery_v2.py"
        with self.assertRaisesRegex(preview.TransitionError,
                                    "v2 artifact delivery source"):
            def fake(*args):
                if args==("show",H+":"+path):
                    return real(*args)+"\n# unsigned transport change\n"
                return real(*args)
            preview.preview(H,git=fake)


if __name__=="__main__":
    unittest.main()
