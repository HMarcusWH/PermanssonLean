"""Synthetic negative tests for 76 source byte owners; never real approvals."""
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from pr113_v31_execution_integrity import (
    ExactSource, RealControlError, validate_executed_controls, verify_owner,
)
from pr113_pack_ci_remaining_owners import manifest, PackError

H = "a" * 40
CLAIMS = ["Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2", "N3", "D8", "D9"]
ORIGINAL = b"theorem original : True := by trivial\n"
FALSE = ORIGINAL + b"\ntheorem false_goal : False := by trivial\n"
POSITIVE = b"Lean positive proof passed\n"
NEGATIVE = b"error: type mismatch\n"
TEST_OK = b"Ran 1 test in 0.001s\n\nOK\n"
ROUTES = "verification/research/test_fixture_routes.py"
CLAIM_TESTS = "verification/research/test_fixture_claims.py"


def method(cid):
    return "test_" + cid.replace("-", "").lower()


def proof(cid):
    return "PermanssonResearch/Fixture/" + cid.replace("-", "") + ".lean"


def ran(path, cls, name):
    module = Path(path).stem
    return (f"{name} ({module}.{cls}.{name}) ... ok\n\n" +
            "-" * 70 + "\n").encode() + TEST_OK


def test_source(cls, names):
    body = "".join(f"    def {n}(self):\n        pass\n" for n in names)
    return f"import unittest\n\nclass {cls}(unittest.TestCase):\n{body}".encode()


CASE_IDS = [f"C-{i:02}" for i in range(1, 46)]
BLOBS = {
    ROUTES: test_source("Routes", [method(c) for c in CASE_IDS] +
                              [method(c) + "_false" for c in CASE_IDS]),
    CLAIM_TESTS: test_source("Claims", [
        "test_" + c.lower() + side for c in CLAIMS
        for side in ("_true", "_false")]),
    **{proof(c): b"theorem " + c.encode() + b" : True := trivial\n"
       for c in CASE_IDS},
    **{proof(c): ORIGINAL for c in CLAIMS},
}


def source(blobs=None, **selection):
    cases = {"cases": [{
        "case_id": c, "effective_accepted": False,
        "test_method_candidates": [
            {"path": ROUTES, "method": method(c), "role": "COMPILER_SOURCE"},
            {"path": ROUTES, "method": method(c) + "_false",
             "role": "SEMANTIC_NEGATIVE"},
        ],
        "historical_proof_declarations": [{"path": proof(c)}],
    } for c in CASE_IDS]}
    claims = {"claims": [{
        "claim_id": c, "declarations": [{"path": proof(c)}],
        "test_source_candidates": [CLAIM_TESTS],
    } for c in CLAIMS]}
    table = dict(BLOBS if blobs is None else blobs)
    return ExactSource(H, cases, claims, lambda path: table.get(path),
                       **selection)


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
    stderr = ran(ROUTES, "Routes", method(cid))
    record = {
        "format": "Permansson.PR113.OriginalCasePositiveCandidate.v1",
        "status": "SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED",
        "head_sha": H, "case_id": cid,
        "test_path": ROUTES, "test_class": "Routes",
        "test_name": method(cid),
        "source_sha256": sha(BLOBS[ROUTES]),
        "proof_source_path": proof(cid),
        "proof_source_sha256": sha(BLOBS[proof(cid)]),
        "positive_role": "COMPILER_SOURCE",
        "source_positive_exit_code": 0, "registered_method_exit_code": 0,
        "actual_producing_check_run_id": None,
        "authenticated_ci_artifact": False,
        "independent_case_review": False,
        "scientific_release_approved": False,
        "unittest_stdout_sha256": sha(b""),
        "unittest_stderr_sha256": sha(stderr),
        "source_positive_log_sha256": sha(POSITIVE),
    }
    owner = base + "unreviewed_positive.json"
    return owner, {
        owner: serialized(record),
        base + "unittest_stdout.log": b"",
        base + "unittest_stderr.log": stderr,
        base + "source_positive.log": POSITIVE,
    }


def original_legacy_capture(cid):
    selected = method(cid) + "_false"
    event = "event-1-000001"
    inp = BLOBS[proof(cid)] + b"\ntheorem false_goal : False := by trivial\n"
    manifest = {
        "format": "Permansson.LegacyCaseTestExecutionCandidate.v1",
        "status": "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED",
        "case_id": cid, "test_file": ROUTES,
        "selected_methods": [selected],
        "source_test_sha256": sha(BLOBS[ROUTES]),
        "test_exit_code": 0,
        "independent_review": False, "release_approved": False,
    }
    obs = {
        "format": "Permansson.LegacyLeanCompilerObservation.v1",
        "case_id_unverified": cid,
        "selected_method_unverified": selected,
        "source_sha256": sha(inp),
    }
    return manifest, obs, inp, event


def authentic_original_legacy():
    members = {}
    for cid in [f"C-{i:02}" for i in range(1, 21)]:
        manifest, obs, inp, event = original_legacy_capture(cid)
        base = f"{cid}/test-00/"
        members[base + "unreviewed_test_manifest.json"] = serialized(manifest)
        members[base + "raw_compiler/" + event + "/observation.json"] = serialized(obs)
        members[base + "raw_compiler/" + event + "/source.lean"] = inp
    return {
        "status": "REAL_PRODUCING_BYTES_UNREVIEWED", "head_sha": H,
        "producer_count": 21,
        "producers": {555: {
            "kind": "legacy", "head_sha": H, "check_run_id": 777,
            "members": members,
        }},
    }


def make_legacy(cid):
    base = "legacy/" + cid + "/"
    original = BLOBS[proof(cid)]
    mutated = original + b"\ntheorem false_goal : False := by trivial\n"
    test_manifest, observation, captured, event = original_legacy_capture(cid)
    selected = method(cid) + "_false"
    mutation = {
        "head_sha": H, "case_ids": [cid], "claim_ids": [],
        "test_path": ROUTES, "test_name": selected,
        "source_sha256": sha(BLOBS[ROUTES]),
        "original_lean_source_path": proof(cid),
        "outcome": "REJECTED_SEMANTIC", "compiler_exit_code": 1,
        "positive_control": {
            "compiled": True, "exit_code": 0,
            "log_member": "pos.log", "log_sha256": sha(POSITIVE),
        },
        "log_member": "neg.log", "log_sha256": sha(NEGATIVE),
        "original_lean_source_member": "original.lean",
        "original_lean_source_sha256": sha(original),
        "mutant_source_member": "false.lean",
        "mutant_source_sha256": sha(mutated),
    }
    source = {
        "format": "Permansson.LegacyAppendOnlyReplayCandidate.v1",
        "status": "REPLAYED_APPEND_ONLY_UNREVIEWED_UNATTRIBUTED",
        "case_id": cid, "head_sha": H,
        "selected_test_path": ROUTES,
        "selected_method": selected,
        "original_provider_path": proof(cid),
        "original_observation_id": event,
        "legacy_test_manifest_sha256": sha(serialized(test_manifest)),
        "raw_observation_sha256": sha(serialized(observation)),
        "captured_false_source_sha256": sha(captured),
        "replayed_false_source_sha256": sha(mutated),
        "detached_bundle_sha256": None,
        "mutation_record": mutation,
        "ci_check_run_id": None,
        "independent_review": False,
        "mathematical_acceptance": False,
    }
    compiler = zipped({
        "pos.log": POSITIVE, "neg.log": NEGATIVE,
        "original.lean": original, "false.lean": mutated,
    })
    source["detached_bundle_sha256"] = sha(compiler)
    src_bytes = serialized(source)
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
        "positive_test.stderr":
            ran(CLAIM_TESTS, "Claims", "test_" + cid.lower() + "_true"),
        "negative_test.stdout": b"",
        "negative_test.stderr":
            ran(CLAIM_TESTS, "Claims", "test_" + cid.lower() + "_false"),
    }
    record = {
        "format": "Permansson.PR113.ClaimOnlyControlCandidate.v1",
        "status": "LEAN_POSITIVE_AND_FALSE_MUTANT_EXECUTED_UNREVIEWED",
        "head_sha": H, "claim_id": cid,
        "claim_ids": [cid], "case_ids": [],
        "original_lean_source_path": proof(cid),
        "positive_test_path": CLAIM_TESTS,
        "positive_test_name": "test_" + cid.lower() + "_true",
        "negative_test_path": CLAIM_TESTS,
        "negative_test_name": "test_" + cid.lower() + "_false",
        "source_test_hashes": {"positive": sha(BLOBS[CLAIM_TESTS]),
                               "negative": sha(BLOBS[CLAIM_TESTS])},
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
        ("original_positive", CASE_IDS, make_positive, 1),
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
        result = validate_executed_controls(H, contract, binaries,
                                            source=source(),
                                            original_producers=authentic_original_legacy())
        self.assertEqual(result["source_owner_count"], 76)
        self.assertTrue(result["canonical_routes_bound"])
        self.assertFalse(result["reviewed_positive_selection_bound"])
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
            validate_executed_controls(H, contract, binaries, source=source(),
                                       original_producers=authentic_original_legacy())

    def test_full_validation_requires_exact_h_route_source(self):
        contract, binaries = complete()
        with self.assertRaises(RealControlError):
            validate_executed_controls(H, contract, binaries, source=None)

    def assert_positive_rejected(self, edit, cid="C-02", blobs=None):
        name, members = make_positive(cid)
        row = json.loads(members[name])
        edit(row, members)
        members[name] = serialized(row)
        # Byte-only packing still accepts it; only route binding rejects.
        verify_owner("original_positive", cid, name, members, H)
        with self.assertRaises(RealControlError):
            verify_owner("original_positive", cid, name, members, H,
                         source(blobs))

    def test_owner_label_swap_fails_route_binding(self):
        name, members = make_positive("C-02")
        row = json.loads(members[name])
        row["case_id"] = "C-03"
        members[name] = serialized(row)
        verify_owner("original_positive", "C-03", name, members, H)
        with self.assertRaises(RealControlError):
            verify_owner("original_positive", "C-03", name, members, H,
                         source())

    def test_unrelated_passing_test_is_not_case_route(self):
        def unrelated(row, members):
            stderr = ran(ROUTES, "Routes", method("C-07"))
            members["positive/C-02/unittest_stderr.log"] = stderr
            row["unittest_stderr_sha256"] = sha(stderr)
            row["test_name"] = method("C-07")
        self.assert_positive_rejected(unrelated)

    def test_semantic_negative_route_cannot_be_positive(self):
        def negative(row, _):
            row["test_name"] = method("C-02") + "_false"
        self.assert_positive_rejected(negative)

    def test_log_of_other_method_fails_named_run(self):
        def other_log(row, members):
            stderr = ran(ROUTES, "Routes", method("C-07"))
            members["positive/C-02/unittest_stderr.log"] = stderr
            row["unittest_stderr_sha256"] = sha(stderr)
        self.assert_positive_rejected(other_log)

    def test_foreign_original_provider_fails(self):
        def foreign(row, _):
            row["proof_source_path"] = proof("C-09")
            row["proof_source_sha256"] = sha(BLOBS[proof("C-09")])
        self.assert_positive_rejected(foreign)

    def test_source_test_digest_substitution_fails(self):
        def substituted(row, _):
            row["source_sha256"] = sha(b"other test bytes")
        self.assert_positive_rejected(substituted)

    def test_undefined_class_method_at_exact_h_fails(self):
        blobs = dict(BLOBS)
        blobs[ROUTES] = test_source("Routes", [method("C-01")])
        def rehash(row, _):
            row["source_sha256"] = sha(blobs[ROUTES])
        self.assert_positive_rejected(rehash, blobs=blobs)

    def test_reviewed_selection_is_compared_exactly(self):
        name, members = make_positive("C-02")
        chosen = {"format": "Permansson.PR113.OriginalPositiveSelection.v1",
                  "cases": [{"case_id": "C-02", "test_path": ROUTES,
                             "test_class": "Routes",
                             "test_method": method("C-02"),
                             "proof_source_path": proof("C-03")}]}
        with self.assertRaises(RealControlError):
            verify_owner("original_positive", "C-02", name, members, H,
                         source(positive_selection=chosen))
        chosen["cases"][0]["proof_source_path"] = proof("C-02")
        verify_owner("original_positive", "C-02", name, members, H,
                     source(positive_selection=chosen))

    def assert_claim_rejected(self, edit, blobs=None):
        name, members, row = make_claim("Q2")
        edit(row, members)
        members[name] = serialized(row)
        verify_owner("claim_pair", "Q2", name, members, H)
        with self.assertRaises(RealControlError):
            verify_owner("claim_pair", "Q2", name, members, H, source(blobs))

    def test_claim_foreign_provider_fails(self):
        def foreign(row, _):
            row["original_lean_source_path"] = proof("Q3")
        self.assert_claim_rejected(foreign)

    def test_claim_original_bytes_must_equal_exact_h(self):
        blobs = dict(BLOBS)
        blobs[proof("Q2")] = ORIGINAL + b"-- edited at H\n"
        self.assert_claim_rejected(lambda row, _: None, blobs=blobs)

    def test_claim_source_test_digest_substitution_fails(self):
        def substituted(row, _):
            row["source_test_hashes"]["negative"] = sha(b"other")
        self.assert_claim_rejected(substituted)

    def test_claim_stderr_containing_ok_is_not_method_route(self):
        def loose(row, members):
            members["claim/Q2/negative_test.stderr"] = b"ok\n" + TEST_OK
            row["retained_member_sha256"]["negative_test.stderr"] = sha(
                b"ok\n" + TEST_OK)
        self.assert_claim_rejected(loose)


    def test_true_original_legacy_route_and_capture_is_bound(self):
        name, members, _, _ = make_legacy("C-01")
        self.assertEqual(
            verify_owner("legacy_negative", "C-01", name, members, H,
                         source(), authentic_original_legacy())["owner_id"],
            "C-01")

    def test_swapped_legacy_method_rejected_despite_valid_zip_hashes(self):
        cid = "C-01"
        name, members, _, _ = make_legacy(cid)
        row = json.loads(members[name])
        receipt_name = row["execution_receipt_member"]
        original = json.loads(members[receipt_name])
        original["selected_method"] = method("C-02") + "_false"
        changed = serialized(original)
        members[receipt_name] = changed
        row["execution_receipt_sha256"] = sha(changed)
        members[name] = serialized(row)
        # The byte-only receipt path does not establish original route.
        verify_owner("legacy_negative", cid, name, members, H)
        with self.assertRaises(RealControlError):
            verify_owner("legacy_negative", cid, name, members, H,
                         source(), authentic_original_legacy())

    def test_foreign_legacy_original_capture_rejected(self):
        cid = "C-01"
        name, members, _, _ = make_legacy(cid)
        changed = authentic_original_legacy()
        target = changed["producers"][555]["members"]
        event = "C-01/test-00/raw_compiler/event-1-000001/source.lean"
        target[event] = target[
            "C-02/test-00/raw_compiler/event-1-000001/source.lean"]
        # Original receipt bytes still pass local ZIP-log checks.
        verify_owner("legacy_negative", cid, name, members, H)
        with self.assertRaises(RealControlError):
            verify_owner("legacy_negative", cid, name, members, H,
                         source(), changed)

    def test_borrowed_legacy_provider_rejected(self):
        cid = "C-01"
        name, members, _, _ = make_legacy(cid)
        row = json.loads(members[name])
        receipt_name = row["execution_receipt_member"]
        original = json.loads(members[receipt_name])
        original["original_provider_path"] = proof("C-02")
        changed = serialized(original)
        members[receipt_name] = changed
        row["execution_receipt_sha256"] = sha(changed)
        members[name] = serialized(row)
        verify_owner("legacy_negative", cid, name, members, H)
        with self.assertRaises(RealControlError):
            verify_owner("legacy_negative", cid, name, members, H,
                         source(), authentic_original_legacy())

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
