"""Nonauthorizing historical evidence v2 structure and schema regression.

All values are synthetic; only live GitHub and actual independent review
can turn a structural candidate into valid historical security evidence.
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
import unittest
from unittest import mock

import infrastructure_acceptance_v2 as consumer
import pr113_historical_evidence_contract_v2 as contract
from final_closure_authenticate import REQUIRED
from test_pr113_release_target import fake_target


ROOT = Path(__file__).resolve().parents[2]
SCHEMA = ROOT / "research/certification/infrastructure_receipt_v2.schema.json"


def candidate(*, aggregate=False):
    head = fake_target()["head_sha"]
    rows = ([{"name":name, "id":200+index, "head_sha":head}
             for index, name in enumerate(sorted(REQUIRED))]
            if aggregate else [])
    return {
        "format": contract.FORMAT,
        "target": fake_target(),
        "source_bound_ci": rows,
        "historical_T": {
            "run_id":101, "run_attempt":2, "job_id":102,
            "check_run_id":103, "artifact_id":104},
        "historical_A2": {
            "run_id":101, "run_attempt":2, "job_id":105,
            "check_run_id":106, "artifact_id":107},
        "security_review_id":108,
    }


class HistoricalEnvelopeV2Tests(unittest.TestCase):
    def test_two_phase_structural_contract_never_authenticates(self):
        base = candidate()
        self.assertIs(contract.validate_envelope(base), base)
        self.assertEqual(contract.parse_envelope(json.dumps(base).encode()), base)
        self.assertEqual(base["source_bound_ci"], [])
        self.assertNotIn("independent_review", base)
        self.assertNotIn("mathematical_acceptance", base)
        aggregate = candidate(aggregate=True)
        self.assertIs(contract.validate_envelope(aggregate, require_all_checks=True),
                      aggregate)
        self.assertEqual(len(aggregate["source_bound_ci"]), 12)
        with self.assertRaises(contract.InfrastructureEnvelopeError):
            contract.validate_envelope(base, require_all_checks=True)

    def test_partial_borrowed_duplicate_stale_contexts_fail(self):
        good = candidate(aggregate=True)
        for edit in (
            lambda p:p["source_bound_ci"].pop(),
            lambda p:p["source_bound_ci"].__setitem__(0,p["source_bound_ci"][1]),
            lambda p:p["source_bound_ci"][0].update(id=True),
            lambda p:p["source_bound_ci"][0].update(head_sha="0"*40),
            lambda p:p["source_bound_ci"][0].update(name="foreign-workflow"),
            lambda p:p["source_bound_ci"][0].update(
                id=p["source_bound_ci"][1]["id"]),
        ):
            with self.subTest(edit=str(edit)):
                payload = copy.deepcopy(good)
                edit(payload)
                with self.assertRaises(contract.InfrastructureEnvelopeError):
                    contract.validate_envelope(payload, require_all_checks=True)

    def test_distinct_historical_producers_and_exact_types_required(self):
        for edit in (
            lambda p:p["historical_A2"].update(run_id=999),
            lambda p:p["historical_A2"].update(run_attempt=1),
            lambda p:p["historical_A2"].update(job_id=102),
            lambda p:p["historical_A2"].update(check_run_id=103),
            lambda p:p["historical_A2"].update(artifact_id=104),
            lambda p:p["historical_T"].update(job_id=True),
            lambda p:p.update(security_review_id=True),
            lambda p:p.update(security_review_id=0),
            lambda p:p.update(fake_approval=True),
            lambda p:p["target"].update(phase="certification_premerge"),
        ):
            with self.subTest(edit=str(edit)):
                payload = copy.deepcopy(candidate())
                edit(payload)
                with self.assertRaises(contract.InfrastructureEnvelopeError):
                    contract.validate_envelope(payload)

    def test_duplicate_json_keys_and_unbounded_bytes_fail_before_git(self):
        orig = candidate()
        raw = json.dumps(orig).encode()
        self.assertEqual(contract.parse_envelope(raw), orig)
        double = raw[:-1] + b', "security_review_id":999}'
        with self.assertRaises(contract.InfrastructureEnvelopeError):
            contract.parse_envelope(double)
        with self.assertRaises(contract.InfrastructureEnvelopeError):
            contract.parse_envelope(b" " * (contract.MAX_BYTES + 1))
        with self.assertRaises(contract.InfrastructureEnvelopeError):
            contract.parse_envelope(b"{bad json}")

    def test_generic_bounded_event_parser_rejects_duplicate_values(self):
        message = b'{"after":"%s", "ref":"refs/heads/main"}' % (b"a"*40)
        self.assertEqual(contract.decode_unique_json(message)["after"],
                         "a" * 40)
        duplicate = message[:-1] + b', "after":"%s"}' % (b"a"*40)
        with self.assertRaises(contract.InfrastructureEnvelopeError):
            contract.decode_unique_json(duplicate, max_bytes=8*1024*1024)
        for raw in (b"[]", b"false", b"null", b"{}"*(contract.MAX_BYTES+1)):
            with self.subTest(raw=raw[:10]), self.assertRaises(
                    contract.InfrastructureEnvelopeError):
                contract.decode_unique_json(raw)

    def test_pr_and_main_event_decoders_reject_duplicate_object_keys(self):
        from test_pr113_required_dual_gate import fake_env, fake_event
        from test_pr113_historical_postmerge import (
            env as main_env, event as main_event,
        )
        import pr113_required_dual_gate_v2 as pr_gate
        import pr113_historical_postmerge_v2 as main_gate

        pr_raw = fake_event()
        pr_dup = pr_raw[:-1] + b', "number":113}'
        with self.assertRaises(pr_gate.RequiredGateError):
            pr_gate.actual_ci_event(
                env=fake_env(), event_data=pr_dup,
                git=lambda *args: "irrelevant")
        original = main_event()
        main_dup = original[:-1] + b', "after":"%s"}' % (b"b"*40)
        with self.assertRaises(main_gate.PostmergeError):
            main_gate.exact_main_event(
                env=main_env(), event_bytes=main_dup,
                git=lambda *args: "irrelevant",
                live=lambda *args: {})

    def test_versioned_source_schema_preserves_v1_and_target_contract(self):
        schema = json.loads(SCHEMA.read_bytes())
        self.assertEqual(schema["properties"]["format"]["const"], contract.FORMAT)
        self.assertFalse(schema["additionalProperties"])
        self.assertEqual(set(schema["required"]), contract.FIELDS)
        self.assertEqual(set(schema["$defs"]["artifact"]["required"]),
                         contract.ARTIFACT_FIELDS)
        self.assertEqual(
            set(schema["properties"]["source_bound_ci"]["items"]
                ["properties"]["name"]["enum"]), REQUIRED)
        self.assertEqual(
            schema["properties"]["target"]["$ref"],
            "target_contract.schema.json")
        historical = json.loads((SCHEMA.parent/"infrastructure_receipt.schema.json")
                                .read_bytes())
        self.assertEqual(historical["properties"]["format"]["const"],
                         "Permansson.PR113.InfrastructureEvidence.v1")

    def test_v2_consumer_rejects_bad_phase_before_live_authority(self):
        bad = candidate()
        bad["historical_A2"]["run_id"] = 999
        with mock.patch.object(consumer.release_target, "bind") as live_auth:
            with self.assertRaises(contract.InfrastructureEnvelopeError):
                consumer.check_historical_only(bad, b"", b"")
            live_auth.assert_not_called()
        missing = candidate()
        with mock.patch.object(consumer.release_target, "bind") as live_auth:
            with self.assertRaises(contract.InfrastructureEnvelopeError):
                consumer.check_evidence(missing, b"", b"")
            live_auth.assert_not_called()


if __name__ == "__main__":
    unittest.main()
