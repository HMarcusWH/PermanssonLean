"""Mandatory ORIGINAL A2 replay at its frozen source, not at current HEAD.

This registered P-02 method also compiles current source through the native
successor. Neither result grants migration review or merge authority.
"""
import json
from pathlib import Path
import tempfile
import unittest
from pr113_historical_a2_replay_v1 import verify, HISTORICAL_A2, STATUS

ROOT = Path(__file__).resolve().parents[2]


class LocalizedCompilerIntegration(unittest.TestCase):
    def test_actual_final_source_and_semantic_mutations(self):
        with tempfile.TemporaryDirectory(prefix="a2p02-proof-") as temp:
            out = Path(temp) / "original-evidence"
            try:
                report = verify(ROOT, out, mode="focused")
            finally:
                # Preserve original raw evidence even if replay fails. A
                # failing compiler must never disappear with its worktree.
                for scope in ("historical_original_A2", "pr113_successor_A2"):
                    folder = out / scope
                    receipt = folder / "receipt.json"
                    if receipt.is_file():
                        print("A2P02_SCOPED_RECEIPT_BEGIN", scope)
                        print(receipt.read_text(encoding="utf-8"))
                        print("A2P02_SCOPED_RECEIPT_END", scope)
                    for log in sorted(folder.glob("*.log")):
                        print("A2P02_SCOPED_LOG_BEGIN", scope, log.name)
                        print(log.read_text(encoding="utf-8", errors="replace"))
                        print("A2P02_SCOPED_LOG_END", scope, log.name)
            self.assertEqual(report["status"], STATUS)
            self.assertEqual(report["historical_source_sha"], HISTORICAL_A2)
            self.assertEqual(report["execution_scope"], "HISTORICAL_A2_AND_CURRENT_SOURCE")
            self.assertTrue(report["original_compiler_receipt"]["source_unchanged"])
            self.assertTrue(report["current_compiler_required_separately"])
            self.assertTrue(report["current_source_compiler_executed"])
            self.assertTrue(report["current_compiler_receipt"]["source_unchanged"])
            self.assertFalse(report["historical_project_build_imported"])
            self.assertFalse(report["historical_executor_modified"])
            self.assertFalse(report["independent_security_review"])
            self.assertFalse(report["mathematical_acceptance"])
            self.assertFalse(report["merge_authorized"])
            print("PR113_HISTORICAL_ENGINEERING_REPLAY_BEGIN")
            print(json.dumps(report, sort_keys=True))
            print("PR113_HISTORICAL_ENGINEERING_REPLAY_END")
