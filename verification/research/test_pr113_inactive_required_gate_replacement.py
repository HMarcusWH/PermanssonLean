"""An inactive R3 transition must not silently relax the original checks."""
import ast
import json
from pathlib import Path
import subprocess
import unittest

ROOT=Path(__file__).resolve().parents[2]
STAGED=ROOT/"docs/operations/pr113_required_gate_replacement_unapproved"
from pr113_workflow_profile_v2 import PREACTIVATION_HEAD, audit as audit_v2


def active30():
    count=len(list((ROOT/".github/workflows").glob("*.yml")))
    if count not in (25,30):
        raise AssertionError("unexpected workflow count")
    return count==30

def git(*args):
    return subprocess.check_output(["git",*args],cwd=ROOT,
       stderr=subprocess.DEVNULL,text=True,timeout=20).strip()

class InactiveHistoricalTransition(unittest.TestCase):
    def test_staged_files_and_original_git_blobs_remain_exact_and_unapproved(self):
        obj=json.loads((STAGED/"manifest.json").read_bytes())
        self.assertEqual(obj["format"],
                         "Permansson.PR113.UnapprovedRequiredGateTransition.v1")
        self.assertEqual(obj["baseline_original_workflow_count"],25)
        if active30():
            result=audit_v2(ROOT,git("rev-parse","HEAD"),phase="active")
            self.assertEqual(result["historical_original_workflow_count"],25)
            self.assertEqual(result["current_reviewed_workflow_count"],30)
            self.assertFalse(result["independent_security_review"])
        self.assertTrue(obj["original_T_A2_unmodified"])
        self.assertTrue(obj["requires_independent_security_review"])
        for k in ("owner_activation_authorized","mathematical_acceptance",
                  "merge_authorized","publication_authorized"):
            self.assertFalse(obj[k])
        self.assertEqual(len(obj["original_unchanged_sources"]),3)
        for rec in obj["original_unchanged_sources"]:
            original_source=PREACTIVATION_HEAD
            self.assertEqual(git("rev-parse",original_source+":"+rec["path"]),
                             rec["git_blob_oid"])
        self.assertEqual(len(obj["staged_replacements"]),2)
        for rec in obj["staged_replacements"]:
            self.assertFalse(rec["installed"])
            self.assertFalse(rec["independent_reviewed"])
            self.assertEqual(git("rev-parse","HEAD:"+rec["source"]),
                             rec["git_blob_oid"])
            # The original historical file remains in the preactivation
            # commit. The reviewed successor is checked by the full v2
            # workflow and test source contract rather than a fragment hash.

    def test_original_A2_is_mandatory_and_staged_successor_is_real(self):
        original=subprocess.check_output(
            ["git","show",PREACTIVATION_HEAD+
             ":verification/research/test_localized_prefix_compiler.py"],
            cwd=ROOT,text=True,timeout=20)
        self.assertIn('report = verify(ROOT, out, mode="focused")',original)
        replacement=(STAGED/"test_localized_prefix_compiler.py").read_text()
        if active30():
            installed=(ROOT/"verification/research/test_localized_prefix_compiler.py").read_text()
            self.assertEqual(installed,replacement)
        else:
            from pr113_a2_successor_identity import INHERITED_A2_VERIFIERS
            path="verification/research/test_localized_prefix_compiler.py"
            self.assertEqual(git("rev-parse","HEAD:"+path),
                             INHERITED_A2_VERIFIERS[path])
            installed=(ROOT/path).read_text()
            self.assertIn("from pr113_historical_a2_replay_v1 import verify",installed)
            self.assertIn("HISTORICAL_A2_AND_CURRENT_SOURCE",installed)
            self.assertNotIn("skipTest",installed)
            self.assertNotIn("@unittest.skip",installed)
        from pr113_a2_successor_identity_v2 import (
            LATE_A2_TEST_ORIGINAL_BLOB, LATE_A2_TEST_PROPOSED_BLOB,
        )
        path="verification/research/test_localized_prefix_compiler.py"
        self.assertEqual(
            git("rev-parse", PREACTIVATION_HEAD+":"+path),
            LATE_A2_TEST_ORIGINAL_BLOB)
        self.assertEqual(git(
            "rev-parse","HEAD:docs/operations/"
            "pr113_required_gate_replacement_unapproved/"
            "test_localized_prefix_compiler.py"),
            LATE_A2_TEST_PROPOSED_BLOB)
        ast.parse(replacement)
        self.assertIn(
            "from pr113_historical_runtime_v3 import FORMAT, check_stored",
            replacement)
        self.assertIn("check_stored(candidate, producer_id, reviewer_id)",
                      replacement)
        self.assertIn("strict_json_object(",replacement)
        self.assertIn("PERMANSSON_HISTORICAL_REQUIRED_RECEIPT",replacement)
        self.assertIn("test_actual_final_source_and_semantic_mutations",
                      replacement)
        self.assertIn("PHASE_STATUSES",replacement)
        for status in (
            "REQUIRED_HISTORICAL_SOURCE_AND_SECURITY_REVIEW_VERIFIED",
            "MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE",
            "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
        ):
            self.assertIn(status,replacement)
        self.assertNotIn("from pr113_required_dual_gate_v2 import verify",
                         replacement)
        self.assertNotIn("@unittest.skip",replacement)
        self.assertNotIn("skipTest(",replacement)
        self.assertNotIn("mock.patch",replacement)
        # Initial PR/main may use original T/A2 sidecars, but the v3
        # consumer must not require those inputs for later CERT/main phases.
        for original_only in ("PERMANSSON_DUAL_HISTORICAL_EVIDENCE",
                              "PERMANSSON_DUAL_ORIGINAL_T_ZIP",
                              "PERMANSSON_DUAL_ORIGINAL_A2_ZIP"):
            self.assertNotIn(original_only,replacement)

    def test_original_archive_gate_is_still_protected_and_staged_step_fails_closed(self):
        original=(
            subprocess.check_output(
                ["git","show",PREACTIVATION_HEAD+
                 ":.github/workflows/research-integrity.yml"],
                cwd=ROOT,text=True,timeout=20)
            if active30() else
            (ROOT/".github/workflows/research-integrity.yml").read_text())
        if active30():
            # The installed v3 workflow replaces current-source delivery,
            # while the immutable historical v2 archive fragment below stays
            # separately asserted. Verify exact active-30 source identity.
            report=audit_v2(ROOT,git("rev-parse","HEAD"),phase="active")
            self.assertEqual(report["versioned_source_phase"],"active")
            self.assertEqual(report["current_reviewed_workflow_count"],30)
            installed=(ROOT/".github/workflows/research-integrity.yml").read_text(
                encoding="utf-8")
            runtime="python3 -B verification/research/pr113_historical_runtime_v3.py"
            self.assertEqual(installed.count(runtime),2)
            self.assertNotIn("pr113_required_dual_gate_v2.py",installed)
            producer_name="      - name: Deliver genuine source-bound historical T and A2 artifacts\n"
            verifier_name="      - name: Verify genuine reviewed original T/T2 and A2 source\n"
            preserve_name="      - name: Preserve archival restoration reports\n"
            for name in (producer_name,verifier_name,preserve_name):
                self.assertEqual(installed.count(name),1)
            producer,tail=installed.split(producer_name,1)[1].split(verifier_name,1)
            verifier=tail.split(preserve_name,1)[0]
            self.assertEqual(producer.count(runtime),1)
            self.assertEqual(verifier.count(runtime),1)
            self.assertRegex(producer,
                             r"(?m)^\s+python3 -B verification/research/"
                             r"pr113_historical_runtime_v3\.py \s*\\\s*$")
            self.assertRegex(verifier,
                             r"(?m)^\s+python3 -B verification/research/"
                             r"pr113_historical_runtime_v3\.py \s*\\\s*$")
            self.assertNotIn("--check-existing",producer)
            self.assertRegex(verifier,r"(?m)^\s+--check-existing\s*$")
        preactivation=subprocess.check_output(
            ["git","show",PREACTIVATION_HEAD+":.github/workflows/research-integrity.yml"],
            cwd=ROOT,text=True,timeout=20)
        self.assertIn("verification.archive.offline_smoke",preactivation)
        if not active30():
            # Installed: the owner-engineering archive successor contract v1,
            # which still executes the original, unchanged T verifier.
            self.assertIn("verification/research/archive_successor_gate_v1.py",original)
            self.assertNotIn("verification.archive.offline_smoke --repo",original)
            gate_source=(ROOT/"verification/research/archive_successor_gate_v1.py").read_text()
            self.assertIn('"verification.archive.offline_smoke"',gate_source)
        self.assertIn("Execute archive adversaries",original)
        replacement=(STAGED/"research_integrity_archive_step.yml.inc").read_text()
        self.assertIn("pr113_required_dual_gate_v2.py",replacement)
        for option in ("historical-T-zip","historical-A2-zip",
                       "PERMANSSON_DUAL_HISTORICAL_EVIDENCE","set -euo pipefail"):
            self.assertIn(option,replacement)
        self.assertNotIn("continue-on-error",replacement)
        self.assertNotIn("|| true",replacement)

if __name__=="__main__":
    unittest.main()
