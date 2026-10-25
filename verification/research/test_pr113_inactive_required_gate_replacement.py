"""An inactive R3 transition must not silently relax the original checks."""
import ast
import json
from pathlib import Path
import subprocess
import unittest

ROOT=Path(__file__).resolve().parents[2]
STAGED=ROOT/"docs/operations/pr113_required_gate_replacement_unapproved"

def git(*args):
    return subprocess.check_output(["git",*args],cwd=ROOT,
       stderr=subprocess.DEVNULL,text=True,timeout=20).strip()

class InactiveHistoricalTransition(unittest.TestCase):
    def test_staged_files_and_original_git_blobs_remain_exact_and_unapproved(self):
        obj=json.loads((STAGED/"manifest.json").read_bytes())
        self.assertEqual(obj["format"],
                         "Permansson.PR113.UnapprovedRequiredGateTransition.v1")
        self.assertEqual(obj["baseline_original_workflow_count"],25)
        self.assertTrue(obj["original_T_A2_unmodified"])
        self.assertTrue(obj["requires_independent_security_review"])
        for k in ("owner_activation_authorized","mathematical_acceptance",
                  "merge_authorized","publication_authorized"):
            self.assertFalse(obj[k])
        self.assertEqual(len(obj["original_unchanged_sources"]),3)
        for rec in obj["original_unchanged_sources"]:
            self.assertEqual(git("rev-parse","HEAD:"+rec["path"]),
                             rec["git_blob_oid"])
        self.assertEqual(len(obj["staged_replacements"]),2)
        for rec in obj["staged_replacements"]:
            self.assertFalse(rec["installed"])
            self.assertFalse(rec["independent_reviewed"])
            self.assertEqual(git("rev-parse","HEAD:"+rec["source"]),
                             rec["git_blob_oid"])

    def test_original_A2_is_mandatory_and_staged_successor_is_real(self):
        original=(ROOT/"verification/research/test_localized_prefix_compiler.py").read_text()
        self.assertIn('report = verify(ROOT, out, mode="focused")',original)
        replacement=(STAGED/"test_localized_prefix_compiler.py").read_text()
        ast.parse(replacement)
        self.assertIn("from pr113_required_dual_gate import verify",replacement)
        self.assertIn("test_actual_final_source_and_semantic_mutations",replacement)
        self.assertNotIn("@unittest.skip",replacement)
        self.assertNotIn("skipTest(",replacement)
        self.assertNotIn("mock.patch",replacement)
        for term in ("PERMANSSON_DUAL_HISTORICAL_EVIDENCE",
                     "PERMANSSON_DUAL_ORIGINAL_T_ZIP",
                     "PERMANSSON_DUAL_ORIGINAL_A2_ZIP"):
            self.assertIn(term,replacement)

    def test_original_archive_gate_is_still_protected_and_staged_step_fails_closed(self):
        original=(ROOT/".github/workflows/research-integrity.yml").read_text()
        self.assertIn("verification.archive.offline_smoke",original)
        self.assertIn("Execute archive adversaries",original)
        replacement=(STAGED/"research_integrity_archive_step.yml.inc").read_text()
        self.assertIn("pr113_required_dual_gate.py",replacement)
        for option in ("historical-T-zip","historical-A2-zip",
                       "PERMANSSON_DUAL_HISTORICAL_EVIDENCE","set -euo pipefail"):
            self.assertIn(option,replacement)
        self.assertNotIn("continue-on-error",replacement)
        self.assertNotIn("|| true",replacement)

if __name__=="__main__":
    unittest.main()
