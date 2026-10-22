"""No-approval and source-identity regressions for legacy Lean evidence capture.

These deliberately test the plumbing with fixture bytes, NOT Lean proofs,
semantic truth, genuine CI attribution, or independent scholarly review.
"""
from pathlib import Path
import json
import subprocess
import tempfile
import types
import unittest
from unittest import mock

import final_closure_legacy_semantic_evidence as legacy
import pr113_compiler_trace_hook as hook
from final_closure_mutation_evidence import MutationEvidenceError

H = "a" * 40


class LegacyEvidenceContract(unittest.TestCase):
    def test_exact_25_plus_20_original_partition_and_named_methods(self):
        with mock.patch.object(
            legacy, "committed_file_bytes",
            side_effect=lambda _head, path, **kwargs: path.read_bytes()):
            all_rows, ids = legacy.shard_cases(H, 0, 1)
            self.assertEqual(len(all_rows), 45)
            self.assertEqual(len(ids), 20)
            self.assertFalse(set(ids) & set(legacy.DETACHED_SPECS))
            self.assertEqual(set(ids) | set(legacy.DETACHED_SPECS),
                             set(all_rows))
            for cid in ids:
                groups = legacy.selected_methods(H, all_rows[cid])
                self.assertTrue(groups, cid)
                self.assertTrue(all(method.startswith("test_")
                                    for _path, _cls, methods in groups
                                    for method in methods))
                self.assertFalse(all_rows[cid]["effective_accepted"])

    def test_shards_disjoint_and_invalid_counts_rejected(self):
        with mock.patch.object(
            legacy, "committed_file_bytes",
            side_effect=lambda _head, path, **kwargs: path.read_bytes()):
            shards = [legacy.shard_cases(H, i, 8)[1] for i in range(8)]
            flat = [cid for group in shards for cid in group]
            self.assertEqual(len(flat), 20)
            self.assertEqual(len(set(flat)), 20)
            for i, n in ((-1, 8), (8, 8), (0, 0), (0, 21)):
                with self.subTest(index=i, count=n), self.assertRaises(
                        MutationEvidenceError):
                    legacy.shard_cases(H, i, n)

    def test_observer_records_exact_temporary_source_before_cleanup(self):
        with tempfile.TemporaryDirectory(prefix="pr113-legacy-event-") as td:
            root = Path(td)
            source = root / "false.lean"
            original = b"import Valid.Module\nexample : False := by trivial\n"
            source.write_bytes(original)
            observation = hook._source(
                ["lake", "env", "lean", str(source)], str(root))
            self.assertEqual(observation[2], original)
            self.assertIsNone(hook._source(["python", "-V"], str(root)))
            captured = root / "events"
            captured.mkdir()
            hook._record(str(captured), observation[0], observation[1],
                         observation[2],
                         outcome=types.SimpleNamespace(
                             returncode=1, stdout="error: type mismatch",
                             stderr=""))
            events = legacy.test_observations(captured)
            self.assertEqual(len(events), 1)
            self.assertTrue(events[0]["possible_semantic_diagnostic"])
            self.assertTrue(events[0]["source_retained"])
            source.unlink()
            self.assertEqual(
                (next(captured.glob("event-*")) / "source.lean").read_bytes(),
                original)

    def test_mutated_compiler_log_and_unrelated_error_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="pr113-legacy-hash-") as td:
            root = Path(td)
            source = b"import Valid.Module\nexample : False := by trivial\n"
            hook._record(str(root), ["lake", "env", "lean", "false.lean"],
                         "false.lean", source,
                         outcome=types.SimpleNamespace(
                             returncode=1, stdout="error: parser error",
                             stderr=""))
            observations = legacy.test_observations(root)
            self.assertEqual(len(observations), 1)
            self.assertFalse(observations[0]["possible_semantic_diagnostic"])
            event = next(root.glob("event-*"))
            (event / "stdout.log").write_bytes(b"error: type mismatch")
            with self.assertRaises(MutationEvidenceError):
                legacy.test_observations(root)

    def test_unexecuted_and_unreviewed_cannot_become_case_acceptance(self):
        with tempfile.TemporaryDirectory(prefix="pr113-legacy-payload-") as td:
            target = Path(td) / "sample.json"
            data = {
                "format": "Permansson.LegacyCaseTestExecutionCandidate.v1",
                "status": "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED",
                "compiler_events": [],
                "independent_review": False,
                "ci_check_run_id": None,
                "release_approved": False,
            }
            target.write_bytes(legacy.canonical(data))
            self.assertFalse(json.loads(target.read_bytes())["independent_review"])
            self.assertIsNone(json.loads(target.read_bytes())["ci_check_run_id"])


if __name__ == "__main__":
    unittest.main()
