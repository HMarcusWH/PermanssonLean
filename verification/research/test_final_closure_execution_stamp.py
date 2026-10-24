"""Mocked GitHub runner context is never an authentic CI attestation."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import final_closure_execution_stamp as stamp

H = "a" * 40
T = "b" * 40
CLAIMS = ("Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2",
          "N3", "D8", "D9")
sha = lambda b: hashlib.sha256(b).hexdigest()


class ExecutedCandidateStampTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="perm-run-stamp-")
        self.addCleanup(self.tmp.cleanup)
        self.out = Path(self.tmp.name)
        self.env = {
            "GITHUB_ACTIONS": "true",
            "GITHUB_REPOSITORY": "HMarcusWH/PermanssonLean",
            "GITHUB_EVENT_NAME": "push",
            "GITHUB_SHA": H,
            "GITHUB_RUN_ID": "123456",
            "GITHUB_RUN_ATTEMPT": "2",
            "GITHUB_JOB": "compiler-candidate",
            "GITHUB_WORKFLOW": "PR113 Compiler Evidence Candidate",
        }
        rows = []
        (self.out/"axiom_logs").mkdir()
        for cid in CLAIMS:
            data = ("actual genuine output expected for " + cid).encode()
            name = "axiom_logs/" + cid + ".log"
            (self.out/name).write_bytes(data)
            rows.append({
                "id": cid, "claim_ids": [cid],
                "head_sha": H,
                "compiler_result": "PASS",
                "check_run_id": None,
                "CI_binding": "PENDING_REAL_CHECK_RUN_ID_ON_FROZEN_H",
                "axiom_log_member": name,
                "axiom_log_sha256": sha(data),
            })
        self.json = {
            "status": "COMPILER_ONLY_UNREVIEWED", "head_sha": H,
            "claim_count": 11, "proof_count": 11,
            "compiler_axiom_receipts": rows,
        }
        self.save()
        patcher = mock.patch.object(stamp, "source_git", side_effect=self.git)
        patcher.start()
        self.addCleanup(patcher.stop)

    def git(self, *cmd):
        if cmd == ("rev-parse", "HEAD"): return H
        if cmd == ("rev-parse", "HEAD^{tree}"): return T
        raise AssertionError(cmd)

    def save(self):
        (self.out/"compiler_candidate.json").write_text(json.dumps(self.json))

    def check(self, env=None):
        return stamp.attestation(self.out, head=H, env=self.env if env is None else env)

    def test_mock_execution_is_unreviewed_even_with_all_claims(self):
        record = self.check()
        self.assertEqual(record["proof_count"], 11)
        self.assertEqual(record["source_tree"], T)
        self.assertEqual(record["github_run_attempt"], 2)
        self.assertIsNone(record["check_run_id"])
        self.assertFalse(record["independent_review"])
        self.assertFalse(record["full_mathematical_acceptance"])

    def test_forged_repository_synthetic_sha_and_job_rejected(self):
        for key, val in (
            ("GITHUB_REPOSITORY", "evil/repo"),
            ("GITHUB_SHA", "c"*40),
            ("GITHUB_JOB", "research"),
            ("GITHUB_RUN_ID", "0"),
            ("GITHUB_RUN_ATTEMPT", "no"),
            ("GITHUB_EVENT_NAME", "pull_request"),
            ("GITHUB_WORKFLOW", "Confusing Similar Name"),
        ):
            env = dict(self.env, **{key: val})
            with self.subTest(key=key), self.assertRaises(stamp.StampingError):
                self.check(env)

    def test_proof_log_corruption_or_absence_blocks_stamp(self):
        name = "axiom_logs/Q1.log"
        (self.out/name).write_bytes(b"mismatched")
        with self.assertRaises(stamp.StampingError):
            self.check()
        (self.out/name).unlink()
        with self.assertRaises(stamp.StampingError):
            self.check()

    def test_claim_subset_or_inherited_checkrun_fails(self):
        self.json["compiler_axiom_receipts"].pop()
        self.json["proof_count"] = 10
        self.save()
        with self.assertRaises(stamp.StampingError):
            self.check()
        self.json["compiler_axiom_receipts"].append(
            dict(self.json["compiler_axiom_receipts"][0],
                 id="Extra", claim_ids=["D9"]))
        self.json["proof_count"] = 11
        self.json["compiler_axiom_receipts"][0]["check_run_id"] = 42
        self.save()
        with self.assertRaises(stamp.StampingError):
            self.check()

    def test_source_path_traversal_and_duplicate_id_rejected(self):
        first = self.json["compiler_axiom_receipts"][0]
        first["axiom_log_member"] = "../outside.log"
        self.save()
        with self.assertRaises(stamp.StampingError):
            self.check()
        first["axiom_log_member"] = "axiom_logs/Q1.log"
        self.json["compiler_axiom_receipts"][1]["id"] = first["id"]
        self.save()
        with self.assertRaises(stamp.StampingError):
            self.check()


if __name__ == "__main__":
    unittest.main()
