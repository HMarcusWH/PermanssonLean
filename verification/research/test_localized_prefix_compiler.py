"""Real, mandatory compiler gate in the existing Research discovery step.

No skip path. Unit-only kit QA intentionally runs separately and does NOT
claim this integration test passed. No recursive test discovery is invoked.
"""
import json
from pathlib import Path
import tempfile
import unittest
from localized_prefix_gate import verify

ROOT = Path(__file__).resolve().parents[2]


class LocalizedCompilerIntegration(unittest.TestCase):
    def test_actual_final_source_and_semantic_mutations(self):
        with tempfile.TemporaryDirectory(prefix="a2p02-proof-") as temp:
            out = Path(temp)
            report = verify(ROOT, out, mode="focused")
            # Existing required workflow stores stdout in its source-bound job log.
            # Emit raw logs as well as the receipt; do not leave the only evidence
            # in a temporary directory that disappears at the end of this test.
            print("\nA2P02_RECEIPT_BEGIN\n" + json.dumps(report, sort_keys=True) + "\nA2P02_RECEIPT_END")
            for entry in report["commands"]:
                print("\nA2P02_LOG_BEGIN " + entry["log"])
                print((out / entry["log"]).read_text(encoding="utf-8", errors="replace"))
                print("A2P02_LOG_END " + entry["log"])
            self.assertEqual(report["status"], "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
                             report.get("reason", "compiler gate failed"))
            self.assertTrue(report["source_unchanged"])
