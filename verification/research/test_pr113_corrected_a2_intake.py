"""Corrected A2 source-binding tests. Compiler receipts below are synthetic.

The real intake/source checks run. The compiler receipt adapter is mocked only
here; actual source compilation and semantic-receipt validators remain separate
mandatory suites. Nothing here authenticates a GitHub artifact or human review.
"""
from __future__ import annotations
import ast
import copy
import hashlib
import json
from pathlib import Path
import unittest
from unittest import mock

import pr113_historical_a2_baseline_v1 as baseline
import pr113_historical_intake_v2 as intake

H = "a" * 40
ROOT = Path(__file__).resolve().parents[2]


def encoded(value):
    return (json.dumps(value, sort_keys=True) + "\n").encode()


def git_blob(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def fixture():
    historical = {
        "format": "Permansson.A2P02.CompilerReceipt.v2",
        "status": "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
        "source_unchanged": True,
        "source": {"git_head": baseline.REPLAY_HEAD, "git_head_tree": baseline.REPLAY_TREE},
        "declarations": dict.fromkeys(intake.DECLS, []),
    }
    successor = {
        "format": "Permansson.PR113.A2SuccessorCompilerCandidate.v2",
        "status": "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING", "source_unchanged": True,
        "source": {"git_head": H}, "declarations": dict.fromkeys(intake.DECLS, []),
    }
    provenance = {
        "historical_checkout_sha": baseline.REPLAY_HEAD,
        "historical_tree_sha": baseline.REPLAY_TREE,
        "introduced_executable_sha": baseline.INTRODUCER,
        "baseline_contract": baseline.FORMAT,
        "original_runtime_git_blobs": dict(baseline.EXECUTORS),
        "output_receipt_sha256": hashlib.sha256(encoded(historical)).hexdigest(),
        "imported_current_A2_gate": False,
    }
    overall = {
        "format": baseline.DUAL_FORMAT,
        "status": "BOTH_ACTUAL_A2_COMPILER_PATHS_EXECUTED_UNREVIEWED",
        "historical_source_commit": baseline.REPLAY_HEAD,
        "historical_introducer_sha": baseline.INTRODUCER,
        "historical_tree_sha": baseline.REPLAY_TREE,
        "historical_runtime_provenance": provenance, "current_source_commit": H,
        "historical_original_workflow_count": 25, "current_reviewed_workflow_count": 30,
        "historical_test_executed": True, "successor_test_executed": True,
        "historical_signatures": 40, "successor_signatures": 40,
        "historical_semantic_mutants": 4, "successor_semantic_mutants": 4,
        "original_verifier_modified": False, "independent_security_approval": False,
        "independent_mathematical_approval": False, "merged_main_sha": None,
        "full_release_approved": False,
    }
    return historical, successor, overall


def inspect(rows):
    original, successor, overall = rows
    files = {
        "historical_original_A2/receipt.json": encoded(original),
        "pr113_successor_A2/receipt.json": encoded(successor),
        "unreviewed_dual_A2_candidate.json": encoded(overall),
    }
    def synthetic_compiler_adapter(files, prefix, status, mutations):
        raw = files[prefix + "/receipt.json"]
        return json.loads(raw), hashlib.sha256(raw).hexdigest()
    with mock.patch.object(intake, "validate_compiler_receipt_v2",
                           side_effect=synthetic_compiler_adapter) as verify:
        result = intake.inspect_A2_v2(files, H)
        if verify.call_count != 2:
            raise AssertionError("both independent receipt legs must be consumed")
        return result


class CorrectedA2IntakeTests(unittest.TestCase):
    def test_corrected_source_is_explicit_without_granting_review(self):
        result = inspect(fixture())
        self.assertEqual(result["historical_replay_sha"], baseline.REPLAY_HEAD)
        self.assertEqual(result["historical_replay_tree"], baseline.REPLAY_TREE)
        self.assertEqual(result["historical_introducer_sha"], baseline.INTRODUCER)
        self.assertFalse(result["independent_security_review"])
        self.assertFalse(result["mathematical_acceptance"])

    def test_legacy_dual_format_cannot_be_upgraded(self):
        for version in ("v2", "v3"):
            rows = fixture(); rows[2]["format"] = "Permansson.PR113.DualA2CompilerCandidate." + version
            with self.subTest(version=version), self.assertRaises(ValueError):
                inspect(rows)

    def test_introduction_cannot_substitute_for_successful_replay(self):
        for scope in ("receipt", "overall", "provenance"):
            rows = fixture()
            if scope == "receipt": rows[0]["source"]["git_head"] = baseline.INTRODUCER
            elif scope == "overall": rows[2]["historical_source_commit"] = baseline.INTRODUCER
            else: rows[2]["historical_runtime_provenance"]["historical_checkout_sha"] = baseline.INTRODUCER
            with self.subTest(scope=scope), self.assertRaises(ValueError): inspect(rows)

    def test_wrong_tree_at_any_binding_is_rejected(self):
        for scope in ("receipt", "overall", "provenance"):
            rows = fixture()
            if scope == "receipt": rows[0]["source"]["git_head_tree"] = "f" * 40
            elif scope == "overall": rows[2]["historical_tree_sha"] = "f" * 40
            else: rows[2]["historical_runtime_provenance"]["historical_tree_sha"] = "f" * 40
            with self.subTest(scope=scope), self.assertRaises(ValueError): inspect(rows)

    def test_provenance_requires_original_executors_and_introducer(self):
        for field, value in (("original_runtime_git_blobs", {}),
                             ("introduced_executable_sha", baseline.REPLAY_HEAD),
                             ("baseline_contract", "v0"), ("imported_current_A2_gate", True),
                             ("output_receipt_sha256", "0" * 64)):
            rows = fixture(); rows[2]["historical_runtime_provenance"][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): inspect(rows)

    def test_historical_success_cannot_cover_foreign_current_source(self):
        for field in ("current_source_commit", "receipt"):
            rows = fixture()
            if field == "receipt": rows[1]["source"]["git_head"] = "b" * 40
            else: rows[2][field] = "b" * 40
            with self.subTest(field=field), self.assertRaises(ValueError): inspect(rows)

    def test_both_legs_need_all_forty_original_declarations(self):
        for which in (0, 1):
            rows = fixture(); rows[which]["declarations"].pop(next(iter(intake.DECLS)))
            with self.subTest(which=which), self.assertRaises(ValueError): inspect(rows)
        for field in ("historical_signatures", "successor_signatures"):
            rows = fixture(); rows[2][field] = 39
            with self.subTest(field=field), self.assertRaises(ValueError): inspect(rows)

    def test_review_or_math_acceptance_cannot_be_self_asserted(self):
        for field in ("original_verifier_modified", "independent_security_approval",
                      "independent_mathematical_approval", "full_release_approved"):
            rows = fixture(); rows[2][field] = True
            with self.subTest(field=field), self.assertRaises(ValueError): inspect(rows)


class CorrectedA2SourceWiringTests(unittest.TestCase):
    def test_all_changed_staged_fingerprints_agree_with_actual_bytes(self):
        stage = ROOT / "docs/operations/pr113_required_gate_replacement_unapproved"
        proposal = ROOT / "docs/operations/pr113_unapproved_workflows"
        producer = proposal / "pr113-historical-migration-candidates.yml"
        source = producer.read_bytes()
        producer_oid = git_blob(source)
        manifest = json.loads((proposal / "manifest.json").read_bytes())
        row = next(r for r in manifest["proposals"]
                   if r["workflow_path"].endswith("pr113-historical-migration-candidates.yml"))
        self.assertEqual(row["git_blob_oid"], producer_oid)
        self.assertFalse(row["approved"])
        self.assertFalse(row["installed"])
        contract = (stage / "workflow_contract_v2.py").read_bytes()
        declared = json.loads((stage / "workflow_contract_v2_manifest.json").read_bytes())
        self.assertEqual(declared["staged_git_blob_oid"], git_blob(contract))
        def assigned(raw, name):
            for node in ast.parse(raw).body:
                if isinstance(node, ast.Assign) and any(
                        isinstance(t, ast.Name) and t.id == name for t in node.targets):
                    return ast.literal_eval(node.value)
            raise AssertionError("missing source declaration: " + name)
        expected = assigned(contract, "APPROVED_WORKFLOW_BLOBS")
        self.assertEqual(expected, declared["expected_workflow_git_blobs"])
        self.assertEqual(len(expected), 30)
        self.assertEqual(expected[producer.name], producer_oid)
        pins = assigned((ROOT / "verification/research/pr113_a2_successor_identity_v2.py").read_bytes(),
                        "PINNED_MODIFIED_PROVIDERS")
        self.assertEqual(pins["verification/integrity/workflow_contract.py"], git_blob(contract))
        self.assertIn(("--historical-head " + baseline.REPLAY_HEAD).encode(), source)
        self.assertNotIn(("--historical-head " + baseline.INTRODUCER).encode(), source)
        self.assertIn(b"pr113_a2_dependency_bridge_v2.py", source)
        self.assertNotIn(b"HistoricalA2DependencyBridge.v1", source)

    def test_v2_runtime_imports_versioned_bridge_not_legacy_alias(self):
        raw = (ROOT / "verification/research/infrastructure_acceptance_v2.py").read_bytes()
        nodes = ast.parse(raw).body
        self.assertTrue(any(isinstance(n, ast.ImportFrom)
                            and n.module == "pr113_a2_dependency_bridge_v2"
                            and any(a.name == "verify_A2_dependency_bridge" for a in n.names)
                            for n in nodes))
        self.assertNotIn(b"verify_A2_dependency_bridge = legacy.verify_A2_dependency_bridge", raw)


if __name__ == "__main__":
    unittest.main()
