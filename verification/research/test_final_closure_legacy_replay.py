"""Original source-append replay adapters: Python-only adversarial tests.

No mocked test outcome here is a Lean or independent scientific certificate.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import tempfile
import unittest
from unittest import mock

import final_closure_legacy_replay as replay
from final_closure_mutation_evidence import MutationEvidenceError

H = "a" * 40


class LegacyAppendOnlyReplayBoundaries(unittest.TestCase):
    def setUp(self):
        self.original = (b"import Mathlib.Tactic\n"
                         b"namespace Original\n"
                         b"theorem established : True := by trivial\n"
                         b"end Original\n")
        self.probe = (
            b"import PermanssonResearch.X1.Exact\n"
            b"open Original\n"
            b"example : False := by exact established\n")

    def test_replay_preserves_exact_original_prefix_and_imports(self):
        combined = replay.appended_mutant(
            self.original, self.probe, "PermanssonResearch.X1.Exact")
        self.assertTrue(combined.startswith(self.original))
        self.assertGreater(len(combined), len(self.original))
        self.assertEqual(
            [x for x in combined.splitlines() if x.startswith(b"import ")],
            [x for x in self.original.splitlines() if x.startswith(b"import ")])
        self.assertIn(b"example : False", combined)
        self.assertIn(b"CANDIDATE ONLY", combined)

    def test_missing_provider_and_missing_statement_fail_closed(self):
        invalid = (
            (b"import Unrelated.Module\nexample : False := by trivial\n",
             "PermanssonResearch.X1.Exact"),
            (b"import PermanssonResearch.X1.Exact\n#check True\n",
             "PermanssonResearch.X1.Exact"),
            (b"", "PermanssonResearch.X1.Exact"),
        )
        for raw, source in invalid:
            with self.subTest(raw=raw), self.assertRaises(MutationEvidenceError):
                replay.appended_mutant(self.original, raw, source)

    def test_forbidden_axioms_admissions_and_late_imports_fail(self):
        forbidden = (
            b"axiom fake : False\nexample : False := fake\n",
            b"example : False := by sorry\n",
            b"example : False := by admit\n",
            b"example : False := by trivial\nimport Unexpected.Module\n",
            b"set_option autoImplicit true\nexample : False := by trivial\n",
        )
        for body in forbidden:
            with self.subTest(body=body), self.assertRaises(
                    MutationEvidenceError):
                replay.appended_mutant(
                    self.original,
                    b"import PermanssonResearch.X1.Exact\n" + body,
                    "PermanssonResearch.X1.Exact")

    def test_original_provider_cannot_be_replaced_with_unrelated_module(self):
        with tempfile.TemporaryDirectory(prefix="pr113-replay-provider-") as td:
            root = Path(td)
            src = root / "PermanssonResearch" / "X1" / "Exact.lean"
            src.parent.mkdir(parents=True)
            src.write_bytes(self.original)
            row = {
                "historical_proof_declarations": [
                    {"path": "PermanssonResearch/X1/Exact.lean"}
                ],
                "new_claim_source_candidates": [],
            }
            with mock.patch.object(replay, "ROOT", root), mock.patch.object(
                replay, "committed_file_bytes",
                return_value=self.original
            ):
                path, raw, mod = replay.choose_original(
                    H, row, "PermanssonResearch/X1/Exact.lean")
                self.assertEqual(path, src)
                self.assertEqual(raw, self.original)
                self.assertEqual(mod, "PermanssonResearch.X1.Exact")
                for bad in (
                    "PermanssonResearch/X1/Other.lean",
                    "PermanssonResearch/../untracked.lean",
                    "/tmp/Original.lean",
                ):
                    with self.subTest(provider=bad), self.assertRaises(
                            MutationEvidenceError):
                        replay.choose_original(H, row, bad)


    def test_replay_keeps_identity_but_never_creates_review_or_ci(self):
        """Synthetic local Git with mocked Lean compiler only; not a proof."""
        with tempfile.TemporaryDirectory(prefix="pr113-replay-contract-") as td:
            base = Path(td)
            root = base / "repo"
            root.mkdir()
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            relative = "PermanssonResearch/X1/Exact.lean"
            source = root / relative
            source.parent.mkdir(parents=True)
            source.write_bytes(self.original)
            test_relative = "verification/research/test_original.py"
            test_file = root / test_relative
            test_file.parent.mkdir(parents=True)
            test_file.write_text("def test_false_original():\n    pass\n")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(
                ["git", "-c", "user.name=ClosureAudit",
                 "-c", "user.email=audit@example.invalid",
                 "commit", "-qm", "source-bound fixture"],
                cwd=root, check=True)
            h = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
            test_dir = base / "legacy-test"
            capture = test_dir / "raw_compiler" / "event-1-000000"
            capture.mkdir(parents=True)
            false_input = self.probe
            (capture / "source.lean").write_bytes(false_input)
            (capture / "observation.json").write_text(
                json.dumps({"status": "RAW_UNREVIEWED"}))
            (capture / "stdout.log").write_text("error: type mismatch")
            (capture / "stderr.log").write_text("")
            test_stdout = b"legacy test ok\n"
            (test_dir / "test_stdout.log").write_bytes(test_stdout)
            (test_dir / "test_stderr.log").write_bytes(b"")
            hash256 = lambda raw: hashlib.sha256(raw).hexdigest()
            test_manifest = {
                "format": "Permansson.LegacyCaseTestExecutionCandidate.v1",
                "case_id": "X-01", "test_file": test_relative,
                "selected_methods": ["test_false_original"],
                "test_exit_code": 0,
                "status": "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED",
                "independent_review": False, "release_approved": False,
                "ci_check_run_id": None,
                "source_test_sha256": hash256(test_file.read_bytes()),
                "stdout_sha256": hash256(test_stdout),
                "stderr_sha256": hash256(b""),
            }
            (test_dir / "unreviewed_test_manifest.json").write_text(
                json.dumps(test_manifest))
            row = {
                "historical_proof_declarations": [{"path": relative}],
                "new_claim_source_candidates": [],
            }
            observations = [{
                "observation_id": "event-1-000000",
                "possible_semantic_diagnostic": True,
                "method_observed_unverified": "test_false_original",
                "method_attribution_ambiguous": False,
                "source_sha256": hash256(false_input),
                "raw_metadata_sha256": hash256(
                    (capture / "observation.json").read_bytes()),
            }]

            def mocked_lean_producer(_head, *, true_source, mutant,
                                     test_path, test_name, case_id,
                                     claim_ids, out):
                self.assertEqual(_head, h)
                self.assertEqual(true_source, source)
                self.assertEqual(test_path, test_file)
                self.assertEqual(test_name, "test_false_original")
                self.assertEqual(case_id, "X-01")
                self.assertEqual(claim_ids, [])
                self.assertTrue(mutant.read_bytes().startswith(self.original))
                self.assertIn(b"example : False", mutant.read_bytes())
                out.mkdir()
                (out / "original.lean").write_bytes(self.original)
                (out / "mutated.lean").write_bytes(mutant.read_bytes())
                (out / "positive.log").write_bytes(b"mock positive\n")
                (out / "negative.log").write_bytes(
                    b"mock negative: type mismatch\n")
                return {
                    "original_lean_source_member": "original.lean",
                    "original_lean_source_sha256": hash256(self.original),
                    "mutant_source_member": "mutated.lean",
                    "mutant_source_sha256": hash256(mutant.read_bytes()),
                    "check_run_id": None,
                }

            detached = base / "replay"
            with (
                mock.patch.object(replay, "ROOT", root),
                mock.patch.object(replay, "git_head", return_value=h),
                mock.patch.object(replay, "original_case_map",
                                  return_value=({"X-01": row}, ("X-01",))),
                mock.patch.object(replay, "selected_methods",
                                  return_value=((test_relative,
                                                 "Class", ("test_false_original",)),)),
                mock.patch.object(replay, "test_observations",
                                  return_value=observations),
                mock.patch.object(replay, "produce",
                                  side_effect=mocked_lean_producer),
            ):
                produced = replay.replay(
                    h, case_id="X-01", method="test_false_original",
                    provider=relative, test_output=test_dir,
                    observation_id="event-1-000000", output=detached)
            self.assertIn("UNREVIEWED", produced["status"])
            self.assertFalse(produced["independent_review"])
            self.assertFalse(produced["mathematical_acceptance"])
            self.assertFalse(produced["scientific_release_approved"])
            self.assertIsNone(produced["ci_check_run_id"])
            self.assertEqual(
                (detached / "original_legacy_capture" / "source.lean").read_bytes(),
                false_input)
            self.assertTrue((detached / "semantic_replay_candidate.zip").is_file())


if __name__ == "__main__":
    unittest.main()
