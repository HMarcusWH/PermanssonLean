"""Mutation-evidence logic tests (compiler results mocked; not real proof receipts)."""
from pathlib import Path
import tempfile
import types
import unittest

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


if __name__ == "__main__":
    unittest.main()
