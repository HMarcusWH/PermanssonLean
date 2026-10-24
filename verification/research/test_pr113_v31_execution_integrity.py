"""Synthetic negative tests for 76 source byte owners; never real approvals."""
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from pr113_v31_execution_integrity import (
    RealControlError, validate_executed_controls, verify_owner,
)
from pr113_pack_ci_remaining_owners import manifest, PackError

H = "a" * 40
CLAIMS = ["Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2", "N3", "D8", "D9"]
ORIGINAL = b"theorem original : True := by trivial\n"
FALSE = ORIGINAL + b"\ntheorem false_goal : False := by trivial\n"
POSITIVE = b"Lean positive proof passed\n"
NEGATIVE = b"error: type mismatch\n"
TEST_OK = b"Ran 1 test in 0.001s\n\nOK\n"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def serialized(row):
    return (json.dumps(row, sort_keys=True) + "\n").encode()


def zipped(members):
    target = io.BytesIO()
    with zipfile.ZipFile(target, "w", compression=zipfile.ZIP_DEFLATED) as z:
        for name, raw in sorted(members.items()):
            z.writestr(name, raw)
    return target.getvalue()


def make_positive(cid):
    base = "positive/" + cid + "/"
    record = {
        "status": "SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED",
        "head_sha": H, "case_id": cid,
        "positive_role": "COMPILER_SOURCE",
        "source_positive_exit_code": 0, "registered_method_exit_code": 0,
        "actual_producing_check_run_id": None,
        "authenticated_ci_artifact": False,
        "independent_case_review": False,
        "scientific_release_approved": False,
        "unittest_stdout_sha256": sha(b""),
        "unittest_stderr_sha256": sha(TEST_OK),
        "source_positive_log_sha256": sha(POSITIVE),
    }
    owner = base + "unreviewed_positive.json"
    return owner, {
        owner: serialized(record),
        base + "unittest_stdout.log": b"",
        base + "unittest_stderr.log": TEST_OK,
        base + "source_positive.log": POSITIVE,
    }


def make_legacy(cid):
    base = "legacy/" + cid + "/"
    proof = {
        "head_sha": H, "case_ids": [cid],
        "outcome": "REJECTED_SEMANTIC", "compiler_exit_code": 1,
        "positive_control": {
            "compiled": True, "exit_code": 0,
            "log_member": "pos.log", "log_sha256": sha(POSITIVE),
        },
        "log_member": "neg.log", "log_sha256": sha(NEGATIVE),
        "original_lean_source_member": "original.lean",
        "original_lean_source_sha256": sha(ORIGINAL),
        "mutant_source_member": "false.lean",
        "mutant_source_sha256": sha(FALSE),
    }
    source = {
        "format": "Permansson.LegacyAppendOnlyReplayCandidate.v1",
        "status": "REPLAYED_APPEND_ONLY_UNREVIEWED_UNATTRIBUTED",
        "case_id": cid, "head_sha": H,
        "mutation_record": proof,
        "ci_check_run_id": None,
        "independent_review": False,
        "mathematical_acceptance": False,
    }
    src_bytes = serialized(source)
    compiler = zipped({
        "pos.log": POSITIVE, "neg.log": NEGATIVE,
        "original.lean": ORIGINAL, "false.lean": FALSE,
    })
    record = {
        "status": "SOURCE_APPENDED_REPLAYED_UNREVIEWED_NOT_CI_ATTRIBUTED",
        "head_sha": H, "case_id": cid,
        "historical_producing_artifact_id": 555,
        "actual_ci_check_run_id": None,
        "execution_receipt_member": base + "original_unreviewed_replay.json",
        "execution_receipt_sha256": sha(src_bytes),
        "semantic_zip_member": base + "semantic_replay_candidate.zip",
        "semantic_zip_sha256": sha(compiler),
        "independent_case_review": False,
        "mathematical_acceptance": False,
        "scientific_release_approved": False,
    }
    owner = base + "unreviewed_legacy_ci.json"
    return owner, {
        owner: serialized(record),
        base + "original_unreviewed_replay.json": src_bytes,
        base + "semantic_replay_candidate.zip": compiler,
    }, source, compiler


def make_claim(cid):
    base = "claim/" + cid + "/"
    members = {
        "original.lean": ORIGINAL, "appended_false.lean": FALSE,
        "positive_lean.log": POSITIVE,
        "negative_lean.log": NEGATIVE,
        "positive_test.stdout": b"",
        "positive_test.stderr": TEST_OK,
        "negative_test.stdout": b"",
        "negative_test.stderr": TEST_OK,
    }
    record = {
        "format": "Permansson.PR113.ClaimOnlyControlCandidate.v1",
        "status": "LEAN_POSITIVE_AND_FALSE_MUTANT_EXECUTED_UNREVIEWED",
        "head_sha": H, "claim_id": cid,
        "claim_ids": [cid], "case_ids": [],
        "lean_positive_exit_code": 0,
        "lean_negative_exit_code": 1,
        "retained_member_sha256":
            {name: sha(raw) for name, raw in members.items()},
        "actual_ci_check_run_id": None,
        "independent_mathematical_review": False,
        "accepted_claim": False,
        "scientific_release_approved": False,
    }
    owner = base + "unreviewed_claim_control.json"
    return owner, {
        owner: serialized(record),
        **{base + name: raw for name, raw in members.items()},
    }, record


def complete():
    jobs, zipfiles = [], {}
    for kind, cases, fn, artifact in (
        ("original_positive", [f"C-{i:02}" for i in range(1, 46)],
         make_positive, 1),
        ("legacy_negative", [f"C-{i:02}" for i in range(1, 21)],
         make_legacy, 2),
        ("claim_pair", CLAIMS, make_claim, 3),
    ):
        members = {}
        owners = []
        for cid in cases:
            owner, entries, *_rest = fn(cid)
            members.update(entries)
            owners.append({
                "kind": kind, "owner_id": cid,
                "receipt_member": owner,
                "receipt_sha256": sha(entries[owner]),
            })
        jobs.append({"artifact_id": artifact, "owners": owners})
        zipfiles[artifact] = zipped(members)
    return {"head_sha": H, "producers": jobs}, zipfiles


class ExecutedControlValidationTests(unittest.TestCase):
    def test_all_76_genuine_member_shapes_still_unreviewed(self):
        contract, binaries = complete()
        result = validate_executed_controls(H, contract, binaries)
        self.assertEqual(result["source_owner_count"], 76)
        self.assertEqual(result["claim_positive_negative_directions"], 22)
        self.assertFalse(result["independent_review"])
        self.assertFalse(result["mathematical_acceptance"])
        self.assertFalse(result["publication_approved"])

    def test_missing_true_log_blocks_original_positive(self):
        name, members = make_positive("C-01")
        del members["positive/C-01/source_positive.log"]
        with self.assertRaises(RealControlError):
            verify_owner("original_positive", "C-01", name, members, H)

    def test_parser_failure_is_not_semantic_negative(self):
        name, members, _, _ = make_legacy("C-01")
        nested = zipped({
            "pos.log": POSITIVE,
            "neg.log": b"error: parser error\n",
            "original.lean": ORIGINAL,
            "false.lean": FALSE,
        })
        # A correct hash cannot make a parser error a semantic refutation.
        wrapper = json.loads(members[name])
        wrapper["semantic_zip_sha256"] = sha(nested)
        members[name] = serialized(wrapper)
        members[wrapper["semantic_zip_member"]] = nested
        with self.assertRaises(RealControlError):
            verify_owner("legacy_negative", "C-01", name, members, H)

    def test_claim_import_change_cannot_replace_false_goal(self):
        name, members, row = make_claim("Q1")
        false = ORIGINAL + b"\nimport Other\n"
        row["retained_member_sha256"]["appended_false.lean"] = sha(false)
        members[name] = serialized(row)
        members["claim/Q1/appended_false.lean"] = false
        with self.assertRaises(RealControlError):
            verify_owner("claim_pair", "Q1", name, members, H)

    def test_partial_owner_partition_not_a_full_release(self):
        contract, binaries = complete()
        contract["producers"][2]["owners"].pop()
        with self.assertRaises(RealControlError):
            validate_executed_controls(H, contract, binaries)

    def test_original_legacy_packer_20_owners_no_approval(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "original-input"
            source.mkdir()
            records = []
            for i in range(1, 21):
                cid = f"C-{i:02}"
                _, _, report, binary = make_legacy(cid)
                case = source / cid
                case.mkdir()
                report["detached_bundle_sha256"] = sha(binary)
                (case / "unreviewed_replay.json").write_bytes(
                    serialized(report))
                (case / "semantic_replay_candidate.zip").write_bytes(binary)
                records.append({
                    "case_id": cid,
                    "original_legacy_producing_artifact_id": 555,
                    "replay_bundle_sha256": sha(binary),
                    "new_replay_producer_check_run_id": None,
                    "status":
                        "SOURCE_APPENDED_REPLAYED_UNREVIEWED_NOT_CI_ATTRIBUTED",
                })
            summary = {
                "format": "Permansson.PR113.LegacyBatchAppendOnlyCandidate.v1",
                "status":
                    "TWENTY_REAL_LEAN_REPLAYS_UNREVIEWED_NOT_CI_BOUND",
                "source_head": H, "replayed_case_count": 20,
                "replays": records,
                "new_source_bound_CI_acceptance": False,
                "independent_case_reviews": 0,
                "mathematical_release_approved": False,
            }
            (source / "unreviewed_batch_replays.json").write_bytes(
                serialized(summary))
            result = manifest(H, 123, 1, "legacy_negative",
                              source, root / "packed")
            self.assertEqual(len(result["owners"]), 20)
            self.assertFalse(result["independent_review"])
            self.assertEqual(result["accepted_cases"], 0)

    def test_original_claim_packer_11_pairs_no_approval(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "original-input"
            source.mkdir()
            records = []
            for cid in CLAIMS:
                _, entries, row = make_claim(cid)
                case = source / cid
                case.mkdir()
                (case / "unreviewed_claim_control.json").write_bytes(
                    serialized(row))
                for name in row["retained_member_sha256"]:
                    (case / name).write_bytes(entries["claim/"+cid+"/"+name])
                records.append(row)
            summary = {
                "format": "Permansson.PR113.ClaimControlsCandidate.v1",
                "status": "ALL_ELEVEN_EXECUTED_UNREVIEWED_NO_CI_ATTRIBUTION",
                "source_head": H,
                "actual_new_claims_executed": 11,
                "claim_controls": records,
                "actual_producing_ci_check_run_id": None,
                "independent_claim_reviews": 0,
                "mathematical_release_approved": False,
            }
            (source / "unreviewed_11_claim_control_summary.json").write_bytes(
                serialized(summary))
            result = manifest(H, 124, 1, "claim_pair",
                              source, root / "packed")
            self.assertEqual(len(result["owners"]), 11)
            self.assertFalse(result["independent_review"])
            self.assertEqual(result["accepted_claims"], 0)


if __name__ == "__main__":
    unittest.main()
