"""Fail-closed original-45 audit verifier and anti-promotion regressions."""
from __future__ import annotations
import copy
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verification/research"))
import post_merge_102_verify as v


class Post102CandidateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.decisions = v.load_json(v.AUDIT / "acceptance_decisions.json")
        cls.index = v.load_json(v.AUDIT / "source_ci_index.json")
        cls.crosswalk = v.load_json(v.AUDIT / "theorem_crosswalk.json")
        cls.reviews = v.load_json(v.AUDIT / "review_receipts.json")

    def test_current_124_source_hashes_and_45_original_cases(self):
        report = v.validate_audit()
        self.assertEqual(report["cases"],45)
        self.assertEqual(report["contracts"],42)
        self.assertGreaterEqual(report["sources"],120)
        self.assertEqual(report["pending"],45)

    def test_missing_case_fails(self):
        d=copy.deepcopy(self.decisions)
        d["cases"].pop()
        with self.assertRaises(v.EvidenceError):
            v.validate_audit(decisions=d)

    def test_duplicate_case_fails(self):
        d=copy.deepcopy(self.decisions)
        d["cases"][-1]=copy.deepcopy(d["cases"][0])
        with self.assertRaises(v.EvidenceError):
            v.validate_audit(decisions=d)

    def test_historical_requirement_cannot_be_weakened(self):
        d=copy.deepcopy(self.decisions)
        d["cases"][0]["required_expected_result"]="easy placeholder"
        with self.assertRaises(v.EvidenceError):
            v.validate_audit(decisions=d)

    def test_false_acceptance_promotion_rejected(self):
        d=copy.deepcopy(self.decisions)
        d["cases"][0]["decision"]="VERIFIED_SELECTED_SCOPE"
        with self.assertRaises(v.EvidenceError):
            v.validate_audit(decisions=d)

    def test_source_digest_corruption_rejected(self):
        idx=copy.deepcopy(self.index)
        idx["current_verified_source_sha256"][0]["sha256"]="0"*64
        with self.assertRaises(v.EvidenceError):
            v.validate_audit(index=idx)

    def test_wrong_historical_receipt_claim_rejected(self):
        idx=copy.deepcopy(self.index)
        idx["original_17_679_census"]="VERIFIED"
        with self.assertRaises(v.EvidenceError):
            v.validate_audit(index=idx)

    def test_fake_external_review_rejected(self):
        rv=copy.deepcopy(self.reviews)
        rv["receipts"].append({"event":"COMMENT","decision":"APPROVED"})
        with self.assertRaises(v.EvidenceError):
            v.validate_audit(reviews=rv)

    def test_pending_full45_gate_is_nonzero(self):
        self.assertRaises(v.EvidenceError,v.verify,"full45-strict")
        cp=subprocess.run([sys.executable,str(ROOT /
            "verification/research/post_merge_102_verify.py"),
            "--mode","full45-strict"],cwd=ROOT,capture_output=True,text=True)
        self.assertNotEqual(cp.returncode,0)
        self.assertIn("NOT ACCEPTED",cp.stderr)

    def test_release_gate_missing_manifest_is_nonzero(self):
        with self.assertRaises(v.EvidenceError):
            v.verify("scoped-release-strict")

    def test_candidate_gate_runs_with_current_source(self):
        self.assertEqual(v.verify("audit")["pending"],45)


if __name__=="__main__":
    unittest.main()
