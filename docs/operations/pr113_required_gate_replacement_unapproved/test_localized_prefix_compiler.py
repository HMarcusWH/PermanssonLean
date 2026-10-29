"""Review-pending versioned A2 required-check consumer (not installed).

The authentic v3 historical runtime already executed and bound the phase-
appropriate original T/A2 or inherited M113 check. Revalidate its detached
receipt against the *current* real CI event before accepting this test:
original PR/main and later CERT/main descendants have different sources.
A candidate result is never independent review or mathematical acceptance.
"""
import json
import os
from pathlib import Path
import unittest

from pr113_boundary_io import strict_json_object
from pr113_historical_runtime_v3 import FORMAT, check_stored

RECEIPT_ENV = "PERMANSSON_HISTORICAL_REQUIRED_RECEIPT"
PHASE_STATUSES = {
    "initial_113_pr": "REQUIRED_HISTORICAL_SOURCE_AND_SECURITY_REVIEW_VERIFIED",
    "initial_113_main": "MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE",
    "main_descendant_pr": "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
    "main_descendant_push": "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
}
MAX_RECEIPT_BYTES = 4 * 1024 * 1024


class LocalizedCompilerIntegration(unittest.TestCase):
    def test_actual_final_source_and_semantic_mutations(self):
        value = os.environ.get(RECEIPT_ENV)
        self.assertTrue(value, "missing phase-neutral authenticated historical receipt")
        candidate = Path(value)
        self.assertTrue(candidate.is_file() and not candidate.is_symlink())
        self.assertLessEqual(candidate.stat().st_size, MAX_RECEIPT_BYTES)
        payload = strict_json_object(
            candidate.read_bytes(), max_bytes=MAX_RECEIPT_BYTES)
        self.assertEqual(payload.get("format"), FORMAT)
        phase = payload.get("phase")
        self.assertIn(phase, PHASE_STATUSES)
        producer_id = payload.get("historical_producer_run_id")
        reviewer_id = payload.get("historical_security_review_id")
        self.assertIs(type(producer_id), int)
        self.assertGreater(producer_id, 0)
        self.assertIs(type(reviewer_id), int)
        self.assertGreater(reviewer_id, 0)

        # This is the real fail-closed validator, not a status-only parse:
        # it binds actual_source() to this job and independently re-executes
        # the historical source+artifact+independent-review authentication.
        # Only the initial PR/main phases carry original T/A2 ZIP sidecars;
        # descendants must revalidate M113 without borrowing those ZIPs.
        verified = check_stored(candidate, producer_id, reviewer_id)
        self.assertEqual(verified, payload)
        result = verified["historical_required_result"]
        self.assertEqual(result.get("status"), PHASE_STATUSES[phase])
        if phase.startswith("initial_113"):
            self.assertIs(result.get("independent_security_review_authenticated"), True)
        else:
            self.assertRegex(
                result.get("historical_merged_main_sha", ""), r"^[0-9a-f]{40}$")
            self.assertIs(result.get("current_required_ci_accepted"), False)
        self.assertIs(verified.get("accepted_current_mathematics"), False)
        self.assertIs(verified.get("owner_merge_authorized"), False)
        self.assertIs(verified.get("publication_authorized"), False)
        print("PR113_PHASE_AWARE_HISTORICAL_RECEIPT_BEGIN")
        print(json.dumps({
            "phase": phase,
            "historical_status": result["status"],
            "source_commit_sha": verified["source_commit_sha"],
            "mathematical_acceptance": False,
            "required_ci_acceptance_inferred": False,
            "publication_authorized": False,
        }, sort_keys=True))
        print("PR113_PHASE_AWARE_HISTORICAL_RECEIPT_END")
