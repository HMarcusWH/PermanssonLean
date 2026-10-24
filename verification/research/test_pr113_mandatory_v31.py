"""Adversarial mandatory v3.1 gate tests; mock CI is NOT evidence."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import final_closure_gate as gate
import final_closure_verify as verify
import pr113_mandatory_v31 as v31


H = "a" * 40
M = "b" * 40
CLAIMS = ("Q1", "Q2", "Q3", "M1", "M2", "M3", "N1",
          "N2", "N3", "D8", "D9")


def mocked_owners():
    return (
        [{"kind": "original_positive", "owner_id": f"C-{i:02}"}
         for i in range(1, 46)] +
        [{"kind": "legacy_negative", "owner_id": f"C-{i:02}"}
         for i in range(1, 21)] +
        [{"kind": "claim_pair", "owner_id": cid} for cid in CLAIMS]
    )


class MandatoryV31Tests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="pr113-v31-mock-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.zips = self.root / "original-zips"
        self.zips.mkdir()
        for id_ in (101, 102, 103):
            (self.zips / (str(id_) + ".zip")).write_bytes(b"TEST_NOT_REAL_ZIP")
        self.contract = self.root / "contract.json"
        self.contract.write_text(json.dumps({"head_sha": H}))
        self.blobs = self.root / "blobs.json"
        self.blobs.write_text(json.dumps({"stub": "source-oid"}))
        self.original = {
            "format": "Permansson.FinalClosureDetachedReceipts.v3",
            "head_sha": H,
            "evidence_bundle_sha256": "d" * 64,
        }

    def run_mocked_live_auth(self, *, bad_count=False):
        owners = mocked_owners()
        if bad_count:
            owners.pop()
        attributed = {
            "status": "ALL_ADDITIONAL_CONTROLS_SOURCE_ATTRIBUTED_UNREVIEWED",
            "head_sha": H,
            "source_owned_controls": owners,
            "schema_security_approved": False,
            "independent_mathematical_review": False,
        }
        executed = {
            "status": "ACTUAL_CONTROL_BYTES_REVALIDATED_UNREVIEWED",
            "source_owner_count": 76,
            "claim_positive_negative_directions": 22,
            "canonical_routes_bound": True,
            "legacy_original_captures_bound": True,
            "execution_log_members_checked": 208,
        }
        claims = {"claims": [{"claim_id": x} for x in CLAIMS]}
        legacy_cases = {f"C-{i:02}": {} for i in range(1, 46)}
        with mock.patch.object(v31, "git", return_value="commit"), \
             mock.patch.object(v31, "authenticate_v3_sources",
                               return_value={
                                   "status": "REAL_PRODUCING_BYTES_UNREVIEWED",
                                   "head_sha": H, "producer_count": 21,
                               }), \
             mock.patch.object(v31, "original_case_map",
                               return_value=(legacy_cases, set(list(legacy_cases)[:20]))), \
             mock.patch.object(v31, "committed_file_bytes",
                               return_value=json.dumps(claims).encode()), \
             mock.patch.object(v31, "candidate_registry",
                               return_value=[{"artifact_id": k}
                                             for k in (101, 102, 103)]), \
             mock.patch.object(v31, "authenticated_extra_controls",
                               return_value=attributed) as authentic, \
             mock.patch.object(v31, "exact_source",
                               return_value="exact-H-routes"), \
             mock.patch.object(v31, "validate_executed_controls",
                               return_value=executed) as logs:
            value = v31.authenticate_all_76(
                H, self.original, {},
                additional_contract=self.contract,
                additional_zips=self.zips,
                workflow_blob_candidates=self.blobs)
            self.assertEqual(authentic.call_count, 1)
            self.assertEqual(logs.call_count, 1)
            self.assertEqual(logs.call_args.kwargs["source"],
                             "exact-H-routes")
            self.assertEqual(
                logs.call_args.kwargs["original_producers"]["producer_count"], 21)
            return value

    def test_full_76_owners_still_do_not_self_certify(self):
        result = self.run_mocked_live_auth()
        self.assertEqual(result["additional_owners"], 76)
        self.assertEqual(result["original_artifacts"], 21)
        self.assertEqual(result["claim_directions"], 22)
        self.assertIs(result["independent_math_approval"], False)
        self.assertIs(result["publication_authorized"], False)

    def test_75_owners_fails_even_with_mocked_green_github(self):
        with self.assertRaises(v31.MandatoryV31Error):
            self.run_mocked_live_auth(bad_count=True)

    def test_missing_original_producer_zip_fails_closed(self):
        (self.zips / "102.zip").unlink()
        with self.assertRaises(v31.MandatoryV31Error):
            self.run_mocked_live_auth()

    def test_wrong_exact_source_commit_fails_before_github(self):
        self.original["head_sha"] = "c" * 40
        with self.assertRaises(v31.MandatoryV31Error):
            self.run_mocked_live_auth()

    def test_premerge_full_v3_only_cannot_claim_complete(self):
        receipts = {
            "format": gate.FORMAT_V3,
            "phase": "premerge_review", "head_sha": H,
            "merged_main_sha": None,
            "evidence_bundle_sha256": "d" * 64,
        }
        verified = {
            "accepted_case_count": 45,
            "accepted_claim_count": 11,
            "effective_cases": {},
            "effective_claims": [],
        }
        with mock.patch.object(gate, "validate_overlay"), \
             mock.patch.object(gate, "verify_premerge",
                               return_value={
                                   "H": H, "S": "e" * 40,
                                   "checks": {}, "review_scopes": {},
                               }), \
             mock.patch.object(gate, "load_detached_bundle",
                               return_value={}), \
             mock.patch.object(gate, "effective_acceptance",
                               return_value=verified), \
             mock.patch.object(gate, "read_json",
                               side_effect=[
                                   {"cases": []}, {"claims": []},
                                   {"cases": []}, {"claims": []},
                               ]), \
             mock.patch.object(gate, "require_full_source",
                               return_value={}), \
             mock.patch.object(gate, "require_complete_obligation_receipts",
                               return_value={}):
            with self.assertRaisesRegex(gate.GateError, "76 real v3.1"):
                gate.premerge(receipts, None, full=True)

    def test_postmerge_full_release_rejects_v3_only_payload(self):
        source = {
            "format": verify.DETACHED_V3,
            "phase": "postmerge_acceptance", "head_sha": H,
            "evidence_bundle_sha256": "d" * 64,
        }
        with mock.patch.object(verify, "validate_overlay"), \
             mock.patch.object(verify, "audit", return_value={}), \
             mock.patch.object(verify, "verify_merged_v2",
                               return_value={
                                   "H": H, "M": M, "S": "c" * 40,
                                   "checks": {}, "review_scopes": {},
                               }), \
             mock.patch.object(verify, "load_detached_bundle",
                               return_value={}), \
             mock.patch.object(verify, "read_json",
                               side_effect=[
                                   {"cases": []}, {"claims": []},
                               ]), \
             mock.patch.object(verify, "effective_acceptance",
                               return_value={
                                   "accepted_case_count": 45,
                                   "accepted_claim_count": 11,
                               }):
            with self.assertRaisesRegex(verify.GateError, "76 original v3.1"):
                verify.strict(source, "full-release-strict", None,
                              bundle_path=self.root / "fake-original.zip")


    def test_public_76_gate_calls_real_validator_with_original_legacy_captures(self):
        """Synthetic data; only external GitHub I/O is stubbed, not validation."""
        from test_pr113_v31_execution_integrity import (
            CASE_IDS, complete, source, authentic_original_legacy,
        )
        contract, binaries = complete()
        original = authentic_original_legacy()
        for path in self.zips.glob("*.zip"):
            path.unlink()
        for artifact_id, raw in binaries.items():
            (self.zips / f"{artifact_id}.zip").write_bytes(raw)
        self.contract.write_text(json.dumps(contract))
        case_map = {cid: {} for cid in CASE_IDS}
        claims = {"claims": [{"claim_id": cid} for cid in CLAIMS]}
        attributed = {
            "status": "ALL_ADDITIONAL_CONTROLS_SOURCE_ATTRIBUTED_UNREVIEWED",
            "head_sha": H,
            "source_owned_controls": mocked_owners(),
            "schema_security_approved": False,
            "independent_mathematical_review": False,
        }
        with mock.patch.object(v31, "git", return_value="commit"), \
             mock.patch.object(v31, "authenticate_v3_sources",
                               return_value=original), \
             mock.patch.object(v31, "original_case_map",
                               return_value=(case_map, set(CASE_IDS[:20]))), \
             mock.patch.object(v31, "committed_file_bytes",
                               return_value=json.dumps(claims).encode()), \
             mock.patch.object(v31, "candidate_registry",
                               return_value=contract["producers"]), \
             mock.patch.object(v31, "authenticated_extra_controls",
                               return_value=attributed), \
             mock.patch.object(v31, "exact_source", return_value=source()), \
             mock.patch.object(v31, "validate_executed_controls",
                               wraps=v31.validate_executed_controls) as validator:
            result = v31.authenticate_all_76(
                H, self.original, {},
                additional_contract=self.contract,
                additional_zips=self.zips,
                workflow_blob_candidates=self.blobs)
            self.assertEqual(result["additional_owners"], 76)
            self.assertEqual(validator.call_count, 1)
            self.assertIs(
                validator.call_args.kwargs["original_producers"], original)
            self.assertFalse(result["publication_authorized"])

            captured = original["producers"][555]["members"]
            key = "C-01/test-00/raw_compiler/event-1-000001/source.lean"
            captured[key] = b"forged old Lean capture"
            with self.assertRaises(v31.MandatoryV31Error):
                v31.authenticate_all_76(
                    H, self.original, {},
                    additional_contract=self.contract,
                    additional_zips=self.zips,
                    workflow_blob_candidates=self.blobs)


if __name__ == "__main__":
    unittest.main()
