"""Synthetic adversarial review-packet QA; not a substitute for true T/A2 CI."""
import json
import unittest
from unittest import mock

import pr113_dual_review_packet as packet
import test_pr113_infrastructure_acceptance as fixtures

H = "a"*40


def fake_tooling(h):
    return {
        "source_commit_sha": h,
        "original_archive_T": packet.T,
        "original_release_base_B": packet.B113,
        "status": "DRAFT_NEEDS_OWNER_AND_INDEPENDENT_SECURITY_REVIEW",
        "historical_archive_unchanged": True,
        "current_workflow_file_count": 25,
        "changed_canonical_tooling": [
            {"path": "verification/integrity/workflow_contract.py",
             "T_blob": "1"*40, "H_blob": "2"*40},
            {"path": "verification/integrity/tests/test_workflow.py",
             "T_blob": "3"*40, "H_blob": "4"*40},
        ],
        "new_successor_T_approved": False,
        "independent_tooling_review": False,
    }


def fake_workflow(h):
    return {
        "head_sha": h,
        "historical_T": packet.T,
        "original_base": packet.B113,
        "status": "EXACT_25_PLUS_5_SOURCE_PROFILE_CANDIDATE_NOT_ACTIVATED",
        "original_workflow_count": 25,
        "successor_proposal_count": 5,
        "active_profile_changed": False,
        "independent_security_review": False,
        "owner_activation_authorized": False,
        "profile_sha256": "5"*64,
    }


def git(*args):
    if args == ("rev-parse", "HEAD"):
        return H
    if args == ("cat-file", "-t", H):
        return "commit"
    if args == ("show", H+":lake-manifest.json"):
        return json.dumps(fixtures.synthetic_lake_manifest(),sort_keys=True)
    raise AssertionError("untrusted Git op "+repr(args))


class DualPacketTests(unittest.TestCase):
    def blobs(self):
        return (fixtures.zipped(fixtures.historical_files()),
                fixtures.zipped(fixtures.a2_files()))

    def assemble(self, t=None, a=None, *,
                 head=H, tooling=fake_tooling, workflow=fake_workflow,
                 current_git=git):
        tb,ab = self.blobs()
        return packet.assemble(head,t if t is not None else tb,
                               a if a is not None else ab,git=current_git,
                               audit_tooling=tooling,
                               audit_workflows=workflow)

    def test_genuine_payload_shape_not_approval(self):
        report=self.assemble()
        self.assertEqual(report["status"],
                         "BOTH_HISTORICAL_SOURCE_LEGS_VERIFIED_FOR_REVIEW_ONLY")
        self.assertEqual(report["current_head"],H)
        self.assertIn("T_execution",report)
        self.assertIn("A2_execution",report)
        self.assertEqual(len(report["canonical_tooling_changes"]),2)
        for k in ("source_bound_GitHub_job_authenticated",
                  "independent_security_review","owner_activation_authorized",
                  "mathematical_acceptance","merge_authorized",
                  "publication_authorized"):
            self.assertIs(report[k], False)

    def test_refuse_forged_identity_and_missing_historical_reports(self):
        with self.assertRaises(packet.ReviewPacketError):
            self.assemble(head="b"*40)
        t,_=self.blobs()
        with self.assertRaises(packet.InfrastructureError):
            self.assemble(t=fixtures.zipped({"invented.json":b"{}"}))
        with self.assertRaises(packet.InfrastructureError):
            self.assemble(a=fixtures.zipped({"invented.json":b"{}"}))

    def test_staged_profile_and_unreviewed_tooling_are_mandatory(self):
        def activated(h):
            result=fake_workflow(h)
            result["active_profile_changed"]=True
            return result
        with self.assertRaises(packet.ReviewPacketError):
            self.assemble(workflow=activated)
        def forged(h):
            result=fake_tooling(h)
            result["independent_tooling_review"]=True
            return result
        with self.assertRaises(packet.ReviewPacketError):
            self.assemble(tooling=forged)

    def test_dependency_bridge_foreign_manifest_is_rejected(self):
        def wrong_git(*args):
            if args==("show",H+":lake-manifest.json"):
                return "{}"
            return git(*args)
        with self.assertRaises(packet.InfrastructureError):
            self.assemble(current_git=wrong_git)

    def test_extra_or_rewritten_original_artifacts_are_not_accepted(self):
        old,a2=self.blobs()
        damage=fixtures.historical_files()
        damage["original_T_archive.json"]=b'{"status":"PASS"}'
        with self.assertRaises(packet.InfrastructureError):
            self.assemble(t=fixtures.zipped(damage))
        missing=fixtures.a2_files()
        missing.pop("historical_dependency_bridge.json")
        with self.assertRaises(packet.InfrastructureError):
            self.assemble(a=fixtures.zipped(missing))


if __name__ == "__main__":
    unittest.main()
