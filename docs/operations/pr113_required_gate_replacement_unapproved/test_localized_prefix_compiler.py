"""UNAPPROVED R3 versioned A2 test; never installed before security review.

Original historical A2 itself runs in its authentic historical checkout.
This candidate replacement checks that source-bound original execution,
the present H successor and four genuine negatives on both sides via an
independently security-reviewed producing GitHub workflow. Missing detached
inputs or approval MUST fail the required Research Lean check.
"""
import json
import os
from pathlib import Path
import unittest
from pr113_required_dual_gate import verify

INPUTS = (
    "PERMANSSON_DUAL_HISTORICAL_EVIDENCE",
    "PERMANSSON_DUAL_ORIGINAL_T_ZIP",
    "PERMANSSON_DUAL_ORIGINAL_A2_ZIP",
)

class LocalizedCompilerIntegration(unittest.TestCase):
    def test_actual_final_source_and_semantic_mutations(self):
        payload=[]
        for name in INPUTS:
            value=os.environ.get(name)
            self.assertTrue(value,"missing authentic historical input "+name)
            candidate=Path(value)
            self.assertTrue(candidate.is_file() and not candidate.is_symlink())
            self.assertLessEqual(candidate.stat().st_size,256*1024*1024)
            payload.append(candidate.read_bytes())
        self.assertLessEqual(len(payload[0]),64*1024)
        result=verify(json.loads(payload[0]),payload[1],payload[2])
        event = os.environ.get("GITHUB_EVENT_NAME")
        self.assertIn(event, ("pull_request", "push"))
        expected = (
            "MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE"
            if event == "push" else
            "REQUIRED_HISTORICAL_SOURCE_AND_SECURITY_REVIEW_VERIFIED"
        )
        self.assertEqual(result["status"], expected)
        if event == "pull_request":
            self.assertFalse(result["all_required_CI_accepted"])
        else:
            self.assertEqual(result["required_ci_successful"], 0)
        self.assertFalse(result["mathematical_acceptance"])
        if event == "pull_request":
            self.assertFalse(result["owner_merge_authorized"])
        else:
            self.assertFalse(result["owner_merge_authorized"])
        self.assertFalse(result["publication_authorized"])
        print("PR113_ORIGINAL_DUAL_HISTORICAL_RECEIPT_BEGIN")
        print(json.dumps(result,sort_keys=True))
        print("PR113_ORIGINAL_DUAL_HISTORICAL_RECEIPT_END")
