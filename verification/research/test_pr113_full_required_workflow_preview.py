"""Bound exact full staged required workflows; do not activate implicitly."""
import json
from pathlib import Path
import subprocess
import unittest
from pr113_workflow_profile_v2 import PREACTIVATION_HEAD, audit as audit_v2

ROOT=Path(__file__).resolve().parents[2]
STAGE=ROOT/"docs/operations/pr113_required_gate_replacement_unapproved"

def git(*args):
    return subprocess.check_output(["git",*args],cwd=ROOT,
        stderr=subprocess.DEVNULL,text=True,timeout=20).strip()

class FullRequiredPreview(unittest.TestCase):
    def setUp(self):
        self.m=json.loads((STAGE/"full_workflow_manifest.json").read_bytes())
        self.lean=(STAGE/"research_lean_full.yml").read_text()
        self.arch=(STAGE/"research_integrity_full.yml").read_text()

    def test_protected_originals_and_full_candidates_are_hash_pinned(self):
        self.assertEqual(self.m["original_workflow_count"],25)
        self.assertEqual(self.m["proposed_final_workflow_count"],30)
        self.assertTrue(self.m["requires_main_PR_and_ordered_merge"])
        for k in ("independent_security_review","owner_activation_authorized",
                  "mathematical_acceptance","merge_authorized",
                  "publication_authorized"):
            self.assertFalse(self.m[k])
        active={p.name for p in (ROOT/".github/workflows").iterdir()
                if p.suffix in (".yml",".yaml")}
        if len(active)==25:
            from verification.integrity.workflow_contract import APPROVED_WORKFLOWS
            self.assertEqual(active,set(APPROVED_WORKFLOWS))
        else:
            self.assertEqual(len(active),30)
            source=audit_v2(ROOT,git("rev-parse","HEAD"),phase="active")
            self.assertEqual(source["current_reviewed_workflow_count"],30)
            self.assertFalse(source["independent_security_review"])
        for entry in self.m["old_workflows"]:
            origin=("HEAD" if len(active)==25 else PREACTIVATION_HEAD)
            self.assertEqual(git("rev-parse",origin+":"+entry["path"]),
                             entry["git_blob_oid"])
        for entry in self.m["full_replacements"]:
            self.assertFalse(entry["installed"])
            self.assertFalse(entry["independent_reviewed"])
            self.assertEqual(git("rev-parse","HEAD:"+entry["staged_source"]),
                             entry["git_blob_oid"])
            if len(active)==30:
                self.assertEqual(git("rev-parse","HEAD:"+entry["target"]),
                                 entry["git_blob_oid"])

    def test_archive_original_other_jobs_unchanged_and_research_stages_preserved(self):
        count=len([p for p in (ROOT/".github/workflows").iterdir()
                   if p.suffix in (".yml",".yaml")])
        old=(
            (ROOT/".github/workflows/research-integrity.yml").read_text()
            if count==25 else subprocess.check_output(
                ["git","show",PREACTIVATION_HEAD+
                 ":.github/workflows/research-integrity.yml"],
                cwd=ROOT,text=True,timeout=20))
        self.assertEqual(
            old.split("  archive-reproducibility:\n",1)[0],
            self.arch.split("  archive-reproducibility:\n",1)[0])
        self.assertIn("Execute archive adversaries",self.arch)
        self.assertIn("verification.integrity.run_tests --suite archive",self.arch)
        for stage in ("Build research library and audit its transitive axioms",
                      "Run research-only exact rational regressions",
                      "Generate and independently verify C10",
                      "Generate and independently recheck D0",
                      "Verify original default target still builds",
                      "Ensure every research module is imported",
                      "Reject proof placeholders"):
            self.assertIn(stage,self.lean)

    def test_readonly_artifact_transport_and_source_checks_cannot_be_bypassed(self):
        for source in (self.lean,self.arch):
            for needle in (
                "GITHUB_TOKEN: ${{ github.token }}",
                "PR113_HISTORICAL_PRODUCER_RUN_ID",
                "PR113_SECURITY_REVIEW_ID",
                "pr113_historical_artifact_delivery_v2.py",
                "actions: read","checks: read","contents: read",
                "pull-requests: read","pull_request:","push:",
                '[[ "$ORIGINAL_RUN_ID" =~ ^[1-9][0-9]*$ ]]',
                '[[ "$INDEPENDENT_REVIEW_ID" =~ ^[1-9][0-9]*$ ]]'):
                self.assertIn(needle,source)
            self.assertNotIn("actions: write",source)
            self.assertNotIn("contents: write",source)
            self.assertNotIn("pull-requests: write",source)
            self.assertNotIn("pull_request_target",source)
            self.assertNotIn("continue-on-error",source)
            self.assertNotIn("|| true",source)
        self.assertIn("pr113_required_dual_gate_v2.py",self.arch)
        self.assertIn("PERMANSSON_DUAL_HISTORICAL_EVIDENCE",self.lean)
        self.assertIn("GITHUB_ENV",self.lean)

if __name__=="__main__":
    unittest.main()
