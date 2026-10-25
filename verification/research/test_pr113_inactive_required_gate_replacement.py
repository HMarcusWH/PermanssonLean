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
            original_source=(PREACTIVATION_HEAD if active30() else "HEAD")
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
        original=(
            subprocess.check_output(
                ["git","show",PREACTIVATION_HEAD+
                 ":verification/research/test_localized_prefix_compiler.py"],
                cwd=ROOT,text=True,timeout=20)
            if active30() else
            (ROOT/"verification/research/test_localized_prefix_compiler.py").read_text())
        self.assertIn('report = verify(ROOT, out, mode="focused")',original)
        replacement=(STAGED/"test_localized_prefix_compiler.py").read_text()
        if active30():
            installed=(ROOT/"verification/research/test_localized_prefix_compiler.py").read_text()
            self.assertEqual(installed,replacement)
        ast.parse(replacement)
        self.assertIn("from pr113_required_dual_gate_v2 import verify",replacement)
        self.assertIn("test_actual_final_source_and_semantic_mutations",replacement)
        self.assertIn("GITHUB_EVENT_NAME",replacement)
        self.assertIn("MERGED_HISTORICAL_T_AND_A2",replacement)
        self.assertNotIn("@unittest.skip",replacement)
        self.assertNotIn("skipTest(",replacement)
        self.assertNotIn("mock.patch",replacement)
        for term in ("PERMANSSON_DUAL_HISTORICAL_EVIDENCE",
                     "PERMANSSON_DUAL_ORIGINAL_T_ZIP",
                     "PERMANSSON_DUAL_ORIGINAL_A2_ZIP"):
            self.assertIn(term,replacement)

    def test_original_archive_gate_is_still_protected_and_staged_step_fails_closed(self):
        original=(
            subprocess.check_output(
                ["git","show",PREACTIVATION_HEAD+
                 ":.github/workflows/research-integrity.yml"],
                cwd=ROOT,text=True,timeout=20)
            if active30() else
            (ROOT/".github/workflows/research-integrity.yml").read_text())
        if active30():
            self.assertIn("pr113_required_dual_gate_v2.py",
                          (ROOT/".github/workflows/research-integrity.yml").read_text())
        self.assertIn("verification.archive.offline_smoke",original)
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
