"""Adversarial tests for C10 release provenance (not a simulated Lean proof)."""
from __future__ import annotations

import copy
import subprocess
from pathlib import Path
from unittest import mock
import tempfile
import unittest

from c10_exact_execution import check_input, execute
from c10_golden import create_golden
from c10_emit_golden_bridge import emit_golden_bridge
from c10_emit_initial_law_lean import MIXED_LAW, MIXED_PROOFS, emit_mixed_golden
from c10_eval_initial_law import eval_initial_law
from c10_release_evidence import (
    EvidenceError, ROOT, SUMMARY_TEXT, THEOREMS, make_manifest, parse_pr_checkout,
    stable_json, axiom_reports, verify_source_checkout,
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
        mixed = eval_initial_law(self.receipt, MIXED_LAW)
        (self.folder / "mixed_initial.json").write_bytes(stable_json(MIXED_LAW))
        (self.folder / "mixed_report.json").write_bytes(stable_json(mixed))
        (self.folder / "C10MixedGolden.lean").write_text(
            emit_mixed_golden(self.receipt, mixed), encoding="utf-8")
        (self.folder / "mixed_check.stdout.txt").write_text(
            "".join("'" + theorem + "' does not depend on any axioms\n"
                    for theorem in MIXED_PROOFS), encoding="utf-8")
        (self.folder / "mixed_check.stderr.txt").write_text("", encoding="utf-8")
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
        with mock.patch("c10_verify_release_evidence.verify_source_checkout"):
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



    def test_28_mixed_report_tampering_rejected_after_rehash(self):
        self.edit_json("mixed_report.json",
                       lambda r: r["members"][1].update({"event": "1/999"}))
        self.refresh_manifest()
        self.assert_rejected()

    def test_29_mixed_initial_law_tampering_rejected_after_rehash(self):
        self.edit_json("mixed_initial.json",
                       lambda r: r["weights"].__setitem__(1, "1/3"))
        self.refresh_manifest()
        self.assert_rejected()

    def test_30_generated_mixed_lean_tamper_rejected_after_rehash(self):
        target = self.folder / "C10MixedGolden.lean"
        target.write_text(target.read_text(encoding="utf-8") +
                          "\n-- forged\n", encoding="utf-8")
        self.refresh_manifest()
        self.assert_rejected()

    def test_31_unpermitted_mixed_lean_axiom_rejected(self):
        target = self.folder / "mixed_check.stdout.txt"
        target.write_text(target.read_text(encoding="utf-8").replace(
            "'mixedGolden_exact' does not depend on any axioms",
            "'mixedGolden_exact' depends on axioms: [sorryAx]"
        ), encoding="utf-8")
        self.refresh_manifest()
        self.assert_rejected()

class C10RealGitSourceTests(unittest.TestCase):
    """Use REAL temporary Git repos, not mocked status strings."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.run_git("init", "-q")
        self.run_git("config", "user.name", "C10 Evidence Test")
        self.run_git("config", "user.email", "ci@example.invalid")
        spec = self.root / "docs/PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md"
        spec.parent.mkdir(parents=True)
        from c10_release_evidence import SPEC_PATH
        spec.write_bytes((ROOT / SPEC_PATH).read_bytes())
        script = self.root / "verification/research/producer.py"
        script.parent.mkdir(parents=True)
        script.write_text("VALUE = 1\n", encoding="utf-8")
        lean = self.root / "PermanssonResearch/Core.lean"
        lean.parent.mkdir(parents=True)
        lean.write_text("theorem x : True := trivial\n", encoding="utf-8")
        (self.root / ".gitignore").write_text(".lake/\n__pycache__/\n*.pyc\n",
                                              encoding="utf-8")
        self.run_git("add", ".")
        self.run_git("commit", "-qm", "frozen source checkout")
        self.original = self.run_git("rev-parse", "HEAD").stdout.strip()

    def run_git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, text=True,
                              check=True, capture_output=True)

    def test_clean_real_repo_passes_source_identity(self):
        self.assertEqual(verify_source_checkout(self.root, self.original),
                         self.original)

    def test_dirty_tracked_specification_rejected(self):
        path = self.root / "docs/PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md"
        path.write_text(path.read_text(encoding="utf-8") + "\nFORGED\n", encoding="utf-8")
        with self.assertRaises(EvidenceError):
            verify_source_checkout(self.root, self.original)

    def test_dirty_lean_source_rejected(self):
        (self.root / "PermanssonResearch/Core.lean").write_text(
            "axiom not_valid : False\n", encoding="utf-8")
        with self.assertRaises(EvidenceError):
            verify_source_checkout(self.root, self.original)

    def test_dirty_producer_rejected(self):
        (self.root / "verification/research/producer.py").write_text(
            "VALUE = 9000\n", encoding="utf-8")
        with self.assertRaises(EvidenceError):
            verify_source_checkout(self.root, self.original)

    def test_staged_change_rejected(self):
        path = self.root / "verification/research/producer.py"
        path.write_text("VALUE = 2\n", encoding="utf-8")
        self.run_git("add", "verification/research/producer.py")
        with self.assertRaises(EvidenceError):
            verify_source_checkout(self.root, self.original)

    def test_deleted_source_rejected(self):
        (self.root / "PermanssonResearch/Core.lean").unlink()
        with self.assertRaises(EvidenceError):
            verify_source_checkout(self.root, self.original)

    def test_untracked_shadow_source_rejected(self):
        (self.root / "verification/research/shadow.py").write_text(
            "TRUSTED = True\n", encoding="utf-8")
        with self.assertRaises(EvidenceError):
            verify_source_checkout(self.root, self.original)

    def test_ignored_build_outputs_are_not_mislabeled_source(self):
        target = self.root / ".lake/build/lib/lean/Stub.olean"
        target.parent.mkdir(parents=True)
        target.write_bytes(b"opaque build cache")
        self.assertEqual(verify_source_checkout(self.root, self.original),
                         self.original)

    def test_expected_head_mismatch_rejected(self):
        with self.assertRaises(EvidenceError):
            verify_source_checkout(self.root, "0" * 40)

if __name__ == "__main__":
    unittest.main()
