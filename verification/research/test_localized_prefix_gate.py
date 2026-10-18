"""Unit tests of gate parsing/failure policy; mocked transcripts are NOT Lean runs."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from localized_prefix_gate import parse_axioms, parse_version, semantic_rejection, mutated_source, verify, prepare_output
from localized_prefix_support import GuardError, lean_code, source_firewall, safe_relative

NAME = "PermanssonResearch.Probability.goodHistory_lintegral_le"


class GatePolicyTests(unittest.TestCase):
    def test_exact_version(self):
        self.assertEqual(parse_version("Lean (version 4.34.0, x86_64, commit abc, Release)"), "4.34.0")

    def test_wrong_versions_rejected(self):
        for v in ("4.34.0-rc1", "4.34.0.1", "4.34.1", "4.3.4", "4.34.0+custom"):
            with self.subTest(version=v), self.assertRaises(GuardError): parse_version(f"Lean (version {v}, Linux)")

    def test_empty_or_duplicate_version_rejected(self):
        for text in ("", "version 4.34.0 version 4.34.0"):
            with self.assertRaises(GuardError): parse_version(text)

    def test_axiom_list_and_universes(self):
        text = f"'{NAME}.{{u_1, u_2}}' depends on axioms: [propext,\n Classical.choice.{{u}}, Quot.sound.{{v}}]"
        self.assertEqual(parse_axioms(text, (NAME,))[NAME], ["Classical.choice", "Quot.sound", "propext"])

    def test_no_axiom_record(self):
        self.assertEqual(parse_axioms(f"'{NAME}' does not depend on any axioms", (NAME,)), {NAME: []})

    def test_missing_record_rejected(self):
        with self.assertRaises(GuardError): parse_axioms("", (NAME,))

    def test_duplicate_record_rejected(self):
        text = f"'{NAME}' depends on axioms: [propext]\n"
        with self.assertRaises(GuardError): parse_axioms(text + text, (NAME,))

    def test_unknown_axiom_rejected(self):
        for axiom in ("sorryAx", "bad.oracle", "Lean.ofReduceBool"):
            with self.assertRaises(GuardError):
                parse_axioms(f"'{NAME}' depends on axioms: [{axiom}]", (NAME,))

    def test_wrong_declaration_rejected(self):
        with self.assertRaises(GuardError):
            parse_axioms("'Other.declaration' depends on axioms: [propext]", (NAME,))

    def test_semantic_rejection_requires_negative_exit(self):
        self.assertFalse(semantic_rejection(0, "unsolved goals"))
        self.assertTrue(semantic_rejection(1, "error: unsolved goals\n⊢ (1:ℝ) ≤ 0"))
        self.assertTrue(semantic_rejection(1, "error: Type mismatch\n  proof\nhas type ..."))

    def test_resource_and_import_errors_never_count(self):
        for message in ("unknown identifier", "unknown constant", "unknown module", "object file missing",
                        "unexpected token", "failed to synthesize", "maximum recursion depth",
                        "out of memory", "deterministic timeout", "maximum heartbeat", "no such file"):
            with self.subTest(message=message), self.assertRaises(GuardError):
                semantic_rejection(1, "unsolved goals\n" + message)

    def test_signal_and_empty_negative_output_rejected(self):
        with self.assertRaises(GuardError): semantic_rejection(-9, "unsolved goals")
        with self.assertRaises(GuardError): semantic_rejection(1, "")

    def test_mutation_missing_or_duplicate_anchor_rejected(self):
        key = "omit_baseline_reporting_error"
        for text in ("", "  reportBase := 1 / 10\n" * 2):
            with self.assertRaises(GuardError): mutated_source(text, key)

    def test_nested_comments_and_strings_are_not_code(self):
        text = '/- outer /- sorry -/ admit -/\n#check "axiom"\ntheorem fine : True := by trivial'
        code = lean_code(text)
        self.assertNotIn("sorry", code)
        self.assertNotIn("admit", code)
        self.assertNotIn("axiom", code)
        source_firewall(text)

    def test_shortcuts_after_nested_comments_are_detected(self):
        for token in ("sorry", "admit", "native_decide", "unsafe", "axiom", "run_cmd", "#eval"):
            with self.assertRaises(GuardError): source_firewall('/- /- nested -/ -/\n' + token)

    def test_unclosed_comments_are_rejected(self):
        with self.assertRaises(GuardError): lean_code("/- unclosed")
        with self.assertRaises(GuardError): lean_code('"unclosed')

    def test_canonical_relative_paths_only(self):
        self.assertEqual(safe_relative("PermanssonResearch/Probability/A.lean"), "PermanssonResearch/Probability/A.lean")
        for path in ("", "/etc/passwd", "../x", "a/../b", "a//b", "./x", "C:/x", "C:\\x", "a\\b", "a/./b", "a\x00b"):
            with self.subTest(path=path), self.assertRaises(GuardError): safe_relative(path)

    def test_output_cannot_overwrite_repository(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td).resolve()
            with self.assertRaises(GuardError): prepare_output(repo, repo / "lean-toolchain")
            self.assertFalse((repo / "lean-toolchain").exists())

    def test_output_cannot_overwrite_old_receipt(self):
        with tempfile.TemporaryDirectory() as td:
            top = Path(td)
            repo = top / "repo"; repo.mkdir()
            out = top / "out"; out.mkdir(); (out / "receipt.json").write_text("OLD")
            with self.assertRaises(GuardError): prepare_output(repo, out)
            self.assertEqual((out / "receipt.json").read_text(), "OLD")

    def test_no_compiler_fails_closed_not_skipped(self):
        # Only source preflight is mocked to isolate the missing-tool policy.
        # No mock result is written into the distribution as compiler evidence.
        with tempfile.TemporaryDirectory() as td:
            top = Path(td); repo = top / "repo"; repo.mkdir(); out = top / "out"
            state = {"files": {}, "source_digest": "unit-test-only", "git_head": "fixture",
                     "git_head_tree": "fixture", "git_status": []}
            with patch("localized_prefix_gate.support.inspect_repo", return_value=state), \
                 patch("localized_prefix_gate.support.read_member", return_value=b"leanprover/lean4:v4.34.0\n"), \
                 patch("localized_prefix_gate.shutil.which", return_value=None):
                result = verify(repo, out)
            self.assertEqual(result["status"], "FAIL_CLOSED")
            self.assertIn("unavailable", result["reason"])
            self.assertEqual(result["commands"], [])
            self.assertEqual(result["declarations"], {})
            self.assertEqual(result["mutations"], {})


class GateFlowMockTests(unittest.TestCase):
    """Exercise driver control flow using MOCK process outputs, never a Lean claim."""
    def exercise(self, fault=None):
        import subprocess
        import localized_prefix_gate as gate
        root = Path(__file__).resolve().parents[2]
        fixture = (root / gate.FIXTURE).read_bytes()
        state = {"files": {}, "source_digest": "MOCK_UNIT_TEST_ONLY", "git_head": "fixture",
                 "git_head_tree": "fixture", "git_status": []}
        counter = {"inspections":0}
        def inspect(repo):
            counter["inspections"] += 1
            x = dict(state)
            if fault == "source_change" and counter["inspections"] > 1:
                x["source_digest"] = "UNIT_TEST_CHANGED"
            return x
        def read(repo, path):
            if path == "lean-toolchain":return b"leanprover/lean4:v4.34.0\n"
            if path == gate.FIXTURE:return fixture
            raise AssertionError(path)
        def run(args, **kwargs):
            if args[-1] == "--version":
                return subprocess.CompletedProcess(args,0,b"Lean (version 4.34.0, MOCK)\n")
            if "AuditSignatures.lean" in args[-1]:
                names = gate.DECLS[:-1] if fault == "missing_axiom" else gate.DECLS
                text = "\n".join(f"'{name}' depends on axioms: [propext]" for name in names)
                return subprocess.CompletedProcess(args,0,text.encode())
            label = Path(args[-1]).stem
            if label in gate.MUTATIONS:
                if fault == "mutant_pass":return subprocess.CompletedProcess(args,0,b"MOCK")
                if fault == "resource_failure":return subprocess.CompletedProcess(args,1,b"error: maximum heartbeat\nunsolved goals")
                return subprocess.CompletedProcess(args,1,b"error: unsolved goals\nMOCK PROOF DIAGNOSTIC")
            return subprocess.CompletedProcess(args,0,b"MOCK SUCCESS; NOT A COMPILER RUN\n")
        with tempfile.TemporaryDirectory(prefix="a2-mock-flow-") as td:
            repo=Path(td)/"repo";repo.mkdir();out=Path(td)/"evidence"
            with patch.object(gate.support,"inspect_repo",side_effect=inspect), \
                 patch.object(gate.support,"read_member",side_effect=read), \
                 patch.object(gate.shutil,"which",return_value="MOCK_LAKE"), \
                 patch.object(gate,"check_dependencies",return_value={"mathlib":"MOCK_REV"}), \
                 patch.object(gate.subprocess,"run",side_effect=run):
                result=gate.verify(repo,out)
            self.assertTrue((out/"receipt.json").is_file())
            for cmd in result["commands"]:self.assertTrue((out/cmd["log"]).is_file())
            # Temporary mock transcripts/receipts are deleted here. They are never
            # copied into evidence/ or presented as actual compiler observations.
            return result
    def test_mock_all_stages_and_four_mutations_are_required(self):
        import localized_prefix_gate as gate
        r=self.exercise()
        self.assertEqual(r["status"],"LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING")
        self.assertEqual(set(r["declarations"]),set(gate.DECLS))
        self.assertEqual(set(r["mutations"]),set(gate.MUTATIONS))
        self.assertIn("original_default_build",[c["label"] for c in r["commands"]])
        self.assertTrue(r["source_unchanged"])
    def test_mock_missing_axiom_fails_entire_gate(self):
        r=self.exercise("missing_axiom");self.assertEqual(r["status"],"FAIL_CLOSED")
        self.assertIn("missing axiom",r["reason"])
    def test_mock_accepted_false_mutant_fails_entire_gate(self):
        r=self.exercise("mutant_pass");self.assertEqual(r["status"],"FAIL_CLOSED")
        self.assertIn("mutation accepted",r["reason"])
    def test_mock_resource_rejection_is_not_semantic_success(self):
        r=self.exercise("resource_failure");self.assertEqual(r["status"],"FAIL_CLOSED")
        self.assertIn("resource",r["reason"])
    def test_mock_source_change_invalidates_otherwise_successful_gate(self):
        r=self.exercise("source_change");self.assertEqual(r["status"],"FAIL_CLOSED")
        self.assertFalse(r["source_unchanged"])


if __name__ == "__main__":
    unittest.main()
