"""Mutation-evidence logic tests (compiler results mocked; not real proof receipts)."""
from pathlib import Path
import tempfile
import subprocess
import types
import unittest
from unittest import mock

import final_closure_mutation_evidence as m


def result(rc, log):
    return types.SimpleNamespace(returncode=rc, stdout=log, stderr="")


class MutantEvidenceTests(unittest.TestCase):
    def test_true_control_and_semantically_false_mutant(self):
        source = b"import Valid.Module\ntheorem t : True := by trivial\n"
        wrong = b"import Valid.Module\ntheorem t : False := by trivial\n"
        self.assertTrue(m.verify_negative(
            result(0, "no errors"),
            result(1, "error: unsolved goals\n  \u22a2 False"), source, wrong))

    def test_bad_positive_and_parser_heartbeat_are_rejected(self):
        source = b"import Valid.Module\ntheorem t : True := by trivial\n"
        wrong = b"import Valid.Module\ntheorem t : False := by trivial\n"
        failures = (
            (result(1, "error: unsolved goals"), result(1, "error: unsolved goals")),
            (result(0, "ok"), result(1, "error: parser error\nunsolved goals")),
            (result(0, "ok"), result(1, "error: unknown identifier\nunsolved goals")),
            (result(0, "ok"), result(1, "error: maximum number of heartbeats\nunsolved goals")),
        )
        for positive, negative in failures:
            with self.assertRaises(m.MutationEvidenceError):
                m.verify_negative(positive, negative, source, wrong)

    def test_same_source_or_changed_import_not_accepted_as_semantic_mutant(self):
        src = b"import Valid.Module\ntheorem t : True := by trivial\n"
        for invalid in (src, b"import Other.Module\ntheorem t : False := by trivial\n"):
            with self.assertRaises(m.MutationEvidenceError):
                m.verify_negative(result(0, "ok"), result(1, "error: unsolved goals"),
                                  src, invalid)

    def test_detached_bundle_bytes_reproducible_across_output_paths(self):
        with tempfile.TemporaryDirectory() as root:
            base = Path(root)
            logs = base/"logs"
            logs.mkdir()
            (logs/"b.log").write_text("negative diagnostic")
            (logs/"a.log").write_text("positive control")
            first = base/"one.zip"
            second = base/"two.zip"
            self.assertEqual(m.seal_logs(logs, first), m.seal_logs(logs, second))
            self.assertEqual(first.read_bytes(), second.read_bytes())


    def test_git_blob_binding_refuses_dirty_and_untracked_source(self):
        with tempfile.TemporaryDirectory(prefix="pr113-git-bound-") as td:
            root = Path(td)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            source = root / "proof.lean"
            original = b"import Mathlib.Tactic\\ntheorem fact : True := by trivial\\n"
            source.write_bytes(original)
            subprocess.run(["git", "add", "proof.lean"], cwd=root, check=True)
            subprocess.run([
                "git", "-c", "user.name=ClosureAudit",
                "-c", "user.email=audit@example.invalid",
                "commit", "-qm", "source"
            ], cwd=root, check=True)
            head = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
            self.assertEqual(
                m.committed_file_bytes(head, source, root=root), original)
            untracked = root / "untracked.lean"
            untracked.write_bytes(original)
            with self.assertRaises(m.MutationEvidenceError):
                m.committed_file_bytes(head, untracked, root=root)
            source.write_bytes(original + b"-- false local alteration\\n")
            with self.assertRaises(m.MutationEvidenceError):
                m.committed_file_bytes(head, source, root=root)
            source.unlink()
            source.symlink_to(untracked)
            with self.assertRaises(m.MutationEvidenceError):
                m.committed_file_bytes(head, source, root=root)


    def test_producer_rechecks_source_after_compiler_run(self):
        # Deliberate dirty-worktree race, with mocked Lean results only.
        # Success here is a validator regression, not mathematical evidence.
        with tempfile.TemporaryDirectory(prefix="pr113-source-race-") as tmp:
            base = Path(tmp)
            repo = base / "repo"
            repo.mkdir()
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            source = repo / "PermanssonResearch" / "Proof.lean"
            source.parent.mkdir(parents=True)
            original = b"import Mathlib.Tactic\ntheorem positive : True := by trivial\n"
            source.write_bytes(original)
            test = repo / "verification" / "research" / "test_case.py"
            test.parent.mkdir(parents=True)
            test.write_text("def test_boundary():\n    pass\n")
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run([
                "git", "-c", "user.name=ClosureAudit",
                "-c", "user.email=audit@example.invalid",
                "commit", "-qm", "frozen candidate"
            ], cwd=repo, check=True)
            head = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
            mutant = base / "mutant.lean"
            mutant.write_bytes(original + b"example : False := by trivial\n")
            out = base / "detached-evidence"

            def fake_compile(path):
                if path == mutant:
                    source.write_bytes(original + b"-- changed during compilation\n")
                    return result(1, "error: type mismatch")
                return result(0, "positive compilation simulated")

            with (
                mock.patch.object(m, "ROOT", repo),
                mock.patch.object(m, "git_head", return_value=head),
                mock.patch.object(m.shutil, "which", return_value="/fake/lake"),
                mock.patch.object(m, "lean_result", side_effect=fake_compile),
            ):
                with self.assertRaises(m.MutationEvidenceError):
                    m.produce(
                        head, true_source=source, mutant=mutant, test_path=test,
                        test_name="test_boundary", case_id="T-01", claim_ids=[],
                        out=out)
            self.assertFalse(out.exists())


if __name__ == "__main__":
    unittest.main()
