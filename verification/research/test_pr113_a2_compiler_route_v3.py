"""A2 source-phase dispatch contracts; synthetic routing is not Lean evidence."""
from __future__ import annotations

import ast
import copy
from pathlib import Path
import subprocess
import tempfile
from types import ModuleType
import unittest
from unittest import mock

import pr113_a2_compiler_route_v3 as routing

H = "a" * 40
DECLARATIONS = tuple("Synthetic.declaration_%02d" % i for i in range(40))
MUTATIONS = {"synthetic_mutation_%d" % i: ("before%d" % i, "after%d" % i)
             for i in range(4)}


def profile(phase):
    return {
        "format": routing.PROFILE_FORMAT,
        "status": routing.PHASES[phase][0],
        "head_sha": H,
        "versioned_source_phase": phase,
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "independent_security_review": False,
    }


def module(name):
    result = ModuleType(name)
    result.DECLS = DECLARATIONS
    result.MUTATIONS = copy.deepcopy(MUTATIONS)
    result.verify = mock.Mock(name="SYNTHETIC_COMPILER_NOT_LEAN")
    return result


class A2CompilerRouteTests(unittest.TestCase):
    def select(self, phase, record=None, compiler=None, head=None):
        compiler = compiler or module(routing.PHASES.get(phase, (None, "bad"))[1])
        historical = module("localized_prefix_gate")
        loaded = []

        def load(name):
            loaded.append(name)
            if name == "localized_prefix_gate":
                return historical
            return compiler

        with tempfile.TemporaryDirectory() as temp:
            with mock.patch.object(routing, "_head", side_effect=head or [H, H]), \
                 mock.patch.object(routing, "_audited_profile",
                                   return_value=(phase, record if record is not None
                                                 else profile(phase))) as audit, \
                 mock.patch.object(routing.importlib, "import_module", side_effect=load):
                result = routing.select_compiler(Path(temp))
                audit.assert_called_once_with(Path(temp).resolve(), H)
        return result, loaded, compiler

    def test_staged_25_uses_v1_not_the_active30_compiler(self):
        selected, loaded, compiler = self.select("staged")
        self.assertEqual(selected.phase, "staged")
        self.assertEqual(selected.checked_sha, H)
        self.assertEqual(selected.receipt_format,
                         "Permansson.PR113.A2SuccessorCompilerCandidate.v1")
        self.assertEqual(loaded, ["pr113_a2_successor_compiler", "localized_prefix_gate"])
        self.assertIs(selected.module, compiler)
        compiler.verify.assert_not_called()

    def test_active_30_uses_v2_not_the_historical25_compiler(self):
        selected, loaded, compiler = self.select("active")
        self.assertEqual(selected.receipt_format,
                         "Permansson.PR113.A2SuccessorCompilerCandidate.v2")
        self.assertEqual(loaded, ["pr113_a2_successor_compiler_v2", "localized_prefix_gate"])
        self.assertIs(selected.module, compiler)
        compiler.verify.assert_not_called()

    def test_count_only_receipt_is_not_an_authenticated_profile(self):
        with self.assertRaises(routing.CompilerRouteError):
            self.select("active", {"historical_original_workflow_count": 25,
                                   "current_reviewed_workflow_count": 30})

    def test_unknown_phase_has_no_fallback(self):
        for phase in ("unknown", "staged25", "approved", "", None):
            with self.subTest(phase=phase), self.assertRaises(routing.CompilerRouteError):
                self.select(phase, {})

    def test_wrong_source_phase_format_count_or_authority_fails_closed(self):
        changes = (
            ("head_sha", "b" * 40), ("versioned_source_phase", "staged"),
            ("format", "Permansson.PR113.VersionedWorkflowEvidence.v1"),
            ("status", routing.PHASES["staged"][0]),
            ("historical_original_workflow_count", 30),
            ("current_reviewed_workflow_count", 25),
            ("historical_original_workflow_count", 25.0),
            ("current_reviewed_workflow_count", True),
            ("independent_security_review", True),
        )
        for key, value in changes:
            wrong = profile("active")
            wrong[key] = value
            with self.subTest(field=key), self.assertRaises(routing.CompilerRouteError):
                self.select("active", wrong)

    def test_profile_failure_never_attempts_a_less_strict_compiler(self):
        with tempfile.TemporaryDirectory() as temp:
            with mock.patch.object(routing, "_head", return_value=H), \
                 mock.patch.object(routing, "_audited_profile",
                                   side_effect=ValueError("exact blob mismatch")), \
                 mock.patch.object(routing.importlib, "import_module") as load:
                with self.assertRaisesRegex(ValueError, "exact blob mismatch"):
                    routing.select_compiler(Path(temp))
                load.assert_not_called()

    def test_native_compiler_failure_is_not_retried_or_promoted(self):
        compiler = module("pr113_a2_successor_compiler_v2")
        compiler.verify.side_effect = ValueError("source mismatch")
        selected, loaded, compiler = self.select("active", compiler=compiler)
        with self.assertRaisesRegex(ValueError, "source mismatch"):
            selected.module.verify(Path("repo"), Path("out"), mode="focused")
        compiler.verify.assert_called_once()
        self.assertNotIn("pr113_a2_successor_compiler", loaded)

    def test_changed_proof_or_negative_control_inventory_is_rejected(self):
        for field in ("DECLS", "MUTATIONS", "verify"):
            compiler = module("pr113_a2_successor_compiler_v2")
            if field == "DECLS":
                compiler.DECLS = compiler.DECLS[:-1]
            elif field == "MUTATIONS":
                compiler.MUTATIONS.pop(next(iter(compiler.MUTATIONS)))
            else:
                compiler.verify = None
            with self.subTest(field=field), self.assertRaises(routing.CompilerRouteError):
                self.select("active", compiler=compiler)

    def test_head_moving_during_selection_is_rejected(self):
        with self.assertRaisesRegex(routing.CompilerRouteError, "checkout moved"):
            self.select("active", head=[H, "b" * 40])

    def test_real_profile_adapter_calls_the_exact_source_auditor(self):
        source = ModuleType("pr113_workflow_profile_v2")
        source.audited_source_phase = mock.Mock(return_value=("active", profile("active")))
        with mock.patch.dict("sys.modules", {"pr113_workflow_profile_v2": source}):
            actual = routing._audited_profile(Path("source"), H)
        self.assertEqual(actual, ("active", profile("active")))
        source.audited_source_phase.assert_called_once_with(Path("source"), H)

    def test_discovered_mandatory_lean_test_uses_the_phase_selected_compiler(self):
        source = Path(__file__).with_name("test_pr113_a2_successor_compiler.py").read_text()
        syntax = ast.parse(source)
        imports = [node for node in ast.walk(syntax) if isinstance(node, ast.ImportFrom)]
        self.assertTrue(any(node.module == "pr113_a2_compiler_route_v3" and
                            any(alias.name == "select_compiler" for alias in node.names)
                            for node in imports))
        self.assertFalse(any(node.module in ("pr113_a2_successor_compiler",
                                             "pr113_a2_successor_compiler_v2")
                             for node in imports))
        self.assertIn('record = compiler.verify(ROOT, folder, mode="focused")', source)
        self.assertIn('self.assertEqual(record["format"], selected.receipt_format)', source)
        self.assertNotIn("skipTest", source)
        self.assertNotIn("@unittest.skip", source)

    def test_git_head_is_observed_from_real_repository_not_environment(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            subprocess.run(["git", "init", "--quiet", str(root)], check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Synthetic Test",
                            "-c", "user.email=test@example.invalid", "commit",
                            "--allow-empty", "--quiet", "-m", "synthetic source fixture"],
                           check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            observed = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"])
            with mock.patch.dict("os.environ", {"GITHUB_SHA": "f" * 40}):
                self.assertEqual(routing._head(root), observed.decode().strip())

    def test_absent_git_repository_is_not_accepted(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(routing.CompilerRouteError):
                routing._head(Path(temp))


if __name__ == "__main__":
    unittest.main()
