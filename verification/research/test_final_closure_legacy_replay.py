"""Original source-append replay adapters: Python-only adversarial tests.

No mocked test outcome here is a Lean or independent scientific certificate.
"""
from pathlib import Path
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


if __name__ == "__main__":
    unittest.main()
