"""No mocked output below is compiler proof or independent acceptance.

These tests verify only that real diagnostics cannot disappear merely because
a theorem's elaborated type, target axiom output, or Lean process failed.
The required CI job and complete 45/11 proof graph must still pass independently.
"""
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest import mock

import final_closure_complete_lean_evidence as compiler

H = "a" * 40


class CompilerDiagnosticRetention(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="pr113-retained-log-")
        self.addCleanup(self.dir.cleanup)
        self.root = Path(self.dir.name) / "repo"
        (self.root / ".lake").mkdir(parents=True)
        self.source = self.root / "PermanssonResearch/Demo.lean"
        self.source.parent.mkdir()
        self.source.write_text(
            "namespace Demo\n"
            "theorem genuine : True := by trivial\n"
            "end Demo\n", encoding="utf-8")
        self.out = Path(self.dir.name) / "detached"
        # Exporter requires more than eleven targets before querying Lean.
        self.inventory = [
            {"path": "PermanssonResearch/Demo.lean",
             "declaration": "Demo.genuine",
             "case_ids": ["X-01"], "claim_ids": []}
            for _ in range(12)
        ]

    def run_with(self, result):
        with mock.patch.object(compiler, "ROOT", self.root), \
             mock.patch.object(compiler, "git_head", return_value=H), \
             mock.patch.object(compiler, "required_inventory",
                               return_value=self.inventory), \
             mock.patch.object(compiler, "committed_file_bytes",
                               side_effect=lambda *_args, **_kw:
                                   self.source.read_bytes()), \
             mock.patch.object(compiler, "run_probe", return_value=result):
            return compiler.export_all(H, self.out, shard_index=0,
                                       shard_count=1)

    def test_unparseable_type_keeps_verbatim_diagnostic_without_pass_receipt(self):
        result = SimpleNamespace(returncode=0,
                                 stdout="info: actual malformed type record",
                                 stderr="Lean emitted unrelated diagnostic")
        with self.assertRaisesRegex(compiler.CompleteCompilerError,
                                    "unverifiable compiler declaration"):
            self.run_with(result)
        raw = (self.out / "axiom_logs/all_0000.log").read_bytes()
        self.assertEqual(raw, (
            "info: actual malformed type record\n"
            "Lean emitted unrelated diagnostic").encode("utf-8"))
        self.assertFalse((self.out / "complete_compiler_candidate.json").exists())

    def test_nonzero_compiler_rejection_keeps_log_but_never_passes(self):
        result = SimpleNamespace(
            returncode=1, stdout="",
            stderr="error: type mismatch in original source")
        with self.assertRaisesRegex(compiler.CompleteCompilerError,
                                    "compiler rejected mandatory source theorem"):
            self.run_with(result)
        self.assertEqual(
            (self.out / "axiom_logs/all_0000.log").read_bytes(),
            b"\nerror: type mismatch in original source")
        self.assertFalse((self.out / "complete_compiler_candidate.json").exists())

    def test_no_accepted_output_for_oversized_compiler_diagnostic(self):
        result = SimpleNamespace(returncode=1,
                                 stdout="x" * (4 * 1024 * 1024),
                                 stderr="error: oversized")
        with self.assertRaisesRegex(compiler.CompleteCompilerError,
                                    "compiler theorem log missing or too large"):
            self.run_with(result)
        self.assertFalse((self.out / "axiom_logs/all_0000.log").exists())
        self.assertFalse((self.out / "complete_compiler_candidate.json").exists())


if __name__ == "__main__":
    unittest.main()
