"""Adversarial tests for C10 release provenance (not a simulated Lean proof)."""
from __future__ import annotations

import copy
from pathlib import Path
from unittest import mock
import tempfile
import unittest

from c10_exact_execution import check_input, execute
from c10_golden import create_golden
from c10_emit_golden_bridge import emit_golden_bridge
from c10_release_evidence import (
    EvidenceError, ROOT, SUMMARY_TEXT, THEOREMS, make_manifest, parse_pr_checkout,
    stable_json, axiom_reports,
)
from c10_verify_release_evidence import (
    verify_bundle_structure, verify_release_bundle,
)

CONTEXT = {
    "repository": "HMarcusWH/PermanssonLean",
    "pr_number": 61,
    "base_sha": "a" * 40,
    "head_sha": "b" * 40,
    "synthetic_merge_sha": "c" * 40,
}


class C10ReleaseEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.folder = Path(self.tmp.name)
        self.receipt = create_golden(self.folder)
        (self.folder / "normalized_input.json").write_bytes(
            stable_json(self.receipt["normalized_input"]))
        (self.folder / "C10ReifiedGolden.lean").write_text(
            emit_golden_bridge(self.receipt), encoding="utf-8")
        # Unit-test synthetic stdout only. Release CLI runs the real Lean kernel.
        fake = "".join(
            "'" + theorem + "' does not depend on any axioms\n"
            for theorem in THEOREMS
        )
        (self.folder / "lean_check.stdout.txt").write_text(fake, encoding="utf-8")
        (self.folder / "lean_check.stderr.txt").write_text("", encoding="utf-8")
        (self.folder / "verification_summary.txt").write_text(
            SUMMARY_TEXT, encoding="utf-8")
        self.refresh_manifest()

    def refresh_manifest(self):
        (self.folder / "evidence_manifest.json").write_bytes(
            stable_json(make_manifest(self.folder, CONTEXT)))

    def edit_json(self, filename, transform):
        from c10_release_evidence import strict_json
        file = self.folder / filename
        obj = strict_json(file)
        transform(obj)
        file.write_bytes(stable_json(obj))

    def assert_rejected(self, expected=CONTEXT):
        with self.assertRaises((EvidenceError, ValueError, KeyError)):
            verify_bundle_structure(self.folder, expected)

    def test_01_valid_structural_data_binding(self):
        self.assertTrue(verify_bundle_structure(self.folder, CONTEXT))

    def test_02_corrupt_receipt_digest(self):
        self.edit_json("receipt.json", lambda o: o["members"][0].update({"margin": "2"}))
        self.assert_rejected()

    def test_03_corrupt_raw_input_even_after_rehash(self):
        self.edit_json("input.json", lambda o: o["descriptor"].__setitem__(0, True))
        self.refresh_manifest()
        self.assert_rejected()

    def test_04_wrong_normalized_comparison_even_after_rehash(self):
        self.edit_json("normalized_input.json",
                       lambda o: o["comparison"].__setitem__(0, 0))
        self.refresh_manifest()
        self.assert_rejected()

    def test_05_reordered_menu_even_after_rehash(self):
        self.edit_json("normalized_input.json", lambda o: o["menu"].reverse())
        self.refresh_manifest()
        self.assert_rejected()

    def test_06_wrong_source_head(self):
        other = dict(CONTEXT, head_sha="d" * 40)
        self.assert_rejected(other)

    def test_07_wrong_base_sha(self):
        other = dict(CONTEXT, base_sha="e" * 40)
        self.assert_rejected(other)

    def test_08_wrong_synthetic_merge(self):
        other = dict(CONTEXT, synthetic_merge_sha="f" * 40)
        self.assert_rejected(other)

    def test_09_false_baseline_certification_status(self):
        self.edit_json("evidence_manifest.json",
                       lambda o: o["proof"].update({"status": "BASELINE_CERTIFIED"}))
        self.assert_rejected()

    def test_10_wrong_typed_realization(self):
        self.edit_json("evidence_manifest.json",
                       lambda o: o["typed_realization"].update({"id": "external.model"}))
        self.assert_rejected()

    def test_11_wrong_specification_digest(self):
        self.edit_json("evidence_manifest.json",
                       lambda o: o["specification"].update({"sha256": "0" * 64}))
        self.assert_rejected()

    def test_12_missing_generated_proof(self):
        (self.folder / "C10ReifiedGolden.lean").unlink()
        self.assert_rejected()

    def test_13_tampered_lean_source_with_updated_hash(self):
        source = self.folder / "C10ReifiedGolden.lean"
        source.write_text(source.read_text(encoding="utf-8") + "\n-- forged\n",
                          encoding="utf-8")
        self.refresh_manifest()
        self.assert_rejected()

    def test_14_extra_axiom_even_after_rehash(self):
        output = self.folder / "lean_check.stdout.txt"
        output.write_text(output.read_text(encoding="utf-8").replace(
            "'reifiedReceipt_valid' does not depend on any axioms",
            "'reifiedReceipt_valid' depends on axioms: [sorryAx]"),
            encoding="utf-8")
        self.refresh_manifest()
        self.assert_rejected()

    def test_15_genuine_lean_rerun_is_mandatory_for_release(self):
        fake = mock.Mock(returncode=1, stdout="error: rejected", stderr="")
        with mock.patch("c10_verify_release_evidence.subprocess.run", return_value=fake):
            with self.assertRaises(EvidenceError):
                verify_release_bundle(self.folder, CONTEXT, rerun_lean=True)

    def test_16_shallow_merge_commit_parents_accepted(self):
        event = {
            "repository": {"full_name": CONTEXT["repository"]},
            "pull_request": {
                "number": 61,
                "base": {"sha": CONTEXT["base_sha"],
                         "repo": {"full_name": CONTEXT["repository"]}},
                "head": {"sha": CONTEXT["head_sha"]},
            },
        }
        raw = ("tree " + "e" * 40 + "\nparent " + CONTEXT["base_sha"] +
               "\nparent " + CONTEXT["head_sha"] + "\nauthor ...\n")
        self.assertEqual(
            parse_pr_checkout(event, raw, CONTEXT["synthetic_merge_sha"],
                              CONTEXT["repository"], CONTEXT["synthetic_merge_sha"]),
            CONTEXT,
        )

    def test_17_swapped_merge_parents_rejected(self):
        event = {
            "repository": {"full_name": CONTEXT["repository"]},
            "pull_request": {
                "number": 61,
                "base": {"sha": CONTEXT["base_sha"],
                         "repo": {"full_name": CONTEXT["repository"]}},
                "head": {"sha": CONTEXT["head_sha"]},
            },
        }
        raw = ("parent " + CONTEXT["head_sha"] + "\nparent " +
               CONTEXT["base_sha"] + "\n")
        with self.assertRaises(EvidenceError):
            parse_pr_checkout(event, raw, CONTEXT["synthetic_merge_sha"],
                              CONTEXT["repository"], CONTEXT["synthetic_merge_sha"])

    def test_18_github_sha_does_not_equal_checkout(self):
        event = {
            "repository": {"full_name": CONTEXT["repository"]},
            "pull_request": {
                "number": 61,
                "base": {"sha": CONTEXT["base_sha"],
                         "repo": {"full_name": CONTEXT["repository"]}},
                "head": {"sha": CONTEXT["head_sha"]},
            },
        }
        with self.assertRaises(EvidenceError):
            parse_pr_checkout(event, "parent " + CONTEXT["base_sha"] +
                              "\nparent " + CONTEXT["head_sha"],
                              CONTEXT["synthetic_merge_sha"],
                              CONTEXT["repository"], "0" * 40)

    def test_19_provenance_scope_not_arbitrary_six_state(self):
        modified = copy.deepcopy(self.receipt["normalized_input"])
        modified["descriptor"][0] = True
        valid_different_receipt = execute(check_input(modified))
        from c10_verify_receipt import ReceiptError
        with self.assertRaises(ReceiptError):
            emit_golden_bridge(valid_different_receipt)

    def test_20_refuse_missing_axiom_report(self):
        output = self.folder / "lean_check.stdout.txt"
        output.write_text("", encoding="utf-8")
        self.refresh_manifest()
        self.assert_rejected()

    def test_21_receipt_fraction_corruption_even_with_rehash(self):
        self.edit_json("receipt.json",
                       lambda o: o["members"][1].update({"margin": "2/3"}))
        self.refresh_manifest()
        self.assert_rejected()

    def test_22_reject_extra_manifest_field(self):
        self.edit_json("evidence_manifest.json", lambda o: o.update({"trusted": True}))
        self.assert_rejected()

    def test_23_missing_human_readable_boundary_rejected(self):
        (self.folder / "verification_summary.txt").unlink()
        self.assert_rejected()

    def test_24_forged_human_boundary_rejected_even_after_rehash(self):
        (self.folder / "verification_summary.txt").write_text(
            "C10 CERTIFIED EXTERNAL ORIGINAL GR for all models\n", encoding="utf-8")
        self.refresh_manifest()
        self.assert_rejected()

    def test_25_unexpected_artifact_rejected_even_if_manifest_valid(self):
        (self.folder / "forged-authority.txt").write_text(
            "PR proof is unconditional", encoding="utf-8")
        self.assert_rejected()

    def test_26_legacy_receipt_not_accepted_as_release_proof(self):
        historical = execute(check_input(self.receipt["normalized_input"]),
                             format_version=1)
        self.assertTrue(verify_receipt(historical))
        (self.folder / "receipt.json").write_bytes(stable_json(historical))
        self.refresh_manifest()
        self.assert_rejected()

    def test_27_full_state_effect_tamper_outside_comparison_rejected(self):
        self.receipt["members"][0]["effects"][3] = "0"
        (self.folder / "receipt.json").write_bytes(stable_json(self.receipt))
        self.refresh_manifest()
        self.assert_rejected()


if __name__ == "__main__":
    unittest.main()
