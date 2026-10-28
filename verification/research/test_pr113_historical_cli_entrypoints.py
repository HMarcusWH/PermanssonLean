"""Real direct-script startup tests; disposable fixtures are never replay evidence.

Every positive source audit reads committed Git objects and executes the actual
staged contract loader. No namespace privileges or historical replay are needed:
the two producer tests deliberately stop at a known post-profile boundary.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from uuid import uuid4

import pr113_disposable_transition_rehearsal as transition
from pr113_tooling_migration import ROOT, T
from pr113_workflow_profile_v2 import CONTRACT, CONTRACT_MANIFEST, PREACTIVATION_HEAD


class HistoricalCLIEntrypointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="pr113-cli-fixtures-")
        cls.addClassCleanup(cls.temp.cleanup)
        cls.outside = Path(cls.temp.name)
        cls.env = {
            key: value for key, value in os.environ.items()
            if key.upper() in {"PATH", "SYSTEMROOT", "WINDIR", "TEMP", "TMP",
                               "HOME", "USERPROFILE", "LANG", "LC_ALL"}
        }
        cls.env.update({"PYTHONDONTWRITEBYTECODE": "1",
                        "PYTHONNOUSERSITE": "1", "GIT_CONFIG_NOSYSTEM": "1",
                        "GIT_CONFIG_GLOBAL": os.devnull,
                        "GIT_TERMINAL_PROMPT": "0"})
        cls.source_head = cls.git(ROOT, "rev-parse", "HEAD").decode().strip()
        cls.staged = cls.clone("staged", cls.source_head)
        # Support routine discovery after a later authorized cutover, too.
        workflow_paths = cls.git(cls.staged, "ls-tree", "-r", "--name-only",
                                 "HEAD", "--", ".github/workflows").splitlines()
        if len(workflow_paths) == 30:
            for raw in workflow_paths:
                (cls.staged / raw.decode()).unlink()
            cls.git(cls.staged, "checkout", PREACTIVATION_HEAD, "--",
                    ".github/workflows", *transition.SOURCE_REPLACEMENTS)
            cls.commit(cls.staged, "DISPOSABLE staged25 CLI test fixture")
        cls.staged_head = cls.git(cls.staged, "rev-parse", "HEAD").decode().strip()
        cls.active = cls.clone("active", cls.staged_head, source=cls.staged)
        mapping = transition.planned_sources(cls.active, cls.staged_head)
        for target, (staged, _oid) in mapping.items():
            destination = cls.active / target
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(cls.git(cls.active, "show",
                                            cls.staged_head + ":" + staged))
        cls.commit(cls.active, "DISPOSABLE active30 CLI test fixture")
        cls.active_head = cls.git(cls.active, "rev-parse", "HEAD").decode().strip()
        cls.historical = cls.clone("historical", T)
        cls.foreign = cls.outside / "foreign-cwd"
        package = cls.foreign / "verification" / "integrity"
        package.mkdir(parents=True)
        for source in (package.parent / "__init__.py", package / "__init__.py",
                       package / "reports.py"):
            source.write_text("FOREIGN_CLI_FIXTURE = True\n", encoding="utf-8")

    @classmethod
    def git(cls, repo, *args):
        process = subprocess.run(["git", "-C", str(repo), *args], env=cls.env,
                                 capture_output=True, timeout=45)
        if process.returncode:
            raise AssertionError("disposable Git fixture failed: " +
                                 process.stderr.decode("utf-8", "replace"))
        return process.stdout

    @classmethod
    def clone(cls, name, commit, *, source=ROOT):
        dest = cls.outside / name
        cls.git(cls.outside, "-c", "core.autocrlf=false", "-c", "core.longpaths=true", "clone",
                "--no-hardlinks", "--no-checkout", str(source), str(dest))
        cls.git(dest, "config", "core.autocrlf", "false")
        # Git for Windows also stats the literal SHA:path revision argument.
        # Deep temp roots must not reject that valid object as a long filename.
        cls.git(dest, "config", "core.longpaths", "true")
        cls.git(dest, "checkout", "--detach", commit)
        return dest

    @classmethod
    def commit(cls, repo, message):
        cls.git(repo, "add", "-A")
        cls.git(repo, "-c", "user.name=PR113 CLI Test Fixture",
                "-c", "user.email=pr113-cli-fixture@invalid.example",
                "-c", "commit.gpgsign=false", "commit", "--no-gpg-sign",
                "-m", message)

    def invoke(self, repo, script, args, *, cwd=None, optimized=False):
        command = [sys.executable, "-B"]
        if optimized:
            command.append("-O")
        command += [str(repo / "verification/research" / script), *map(str, args)]
        return subprocess.run(command, cwd=cwd or repo, env=self.env,
                              capture_output=True, text=True, timeout=90)

    def audit(self, repo, head, phase, *, cwd=None, optimized=False):
        output = self.outside / ("profile-" + uuid4().hex + ".json")
        result = self.invoke(repo, "pr113_tooling_migration_v2.py",
                             ["--head", head, "--phase", phase, "--out", output],
                             cwd=cwd, optimized=optimized)
        return result, output

    def assert_rejected(self, process, reason):
        self.assertEqual(process.returncode, 2, process.stdout + process.stderr)
        self.assertIn(reason, process.stderr)
        self.assertNotIn("ModuleNotFoundError", process.stderr)

    def test_real_staged_cli_from_repository_and_foreign_cwd(self):
        for cwd, optimized in ((self.staged, False), (self.foreign, True)):
            with self.subTest(cwd=str(cwd), optimized=optimized):
                process, output = self.audit(self.staged, self.staged_head,
                                             "staged", cwd=cwd, optimized=optimized)
                self.assertEqual(process.returncode, 0, process.stderr)
                record = json.loads(output.read_bytes())
                self.assertEqual(record["source_commit_sha"], self.staged_head)
                self.assertEqual(record["historical_packaged_tooling_files_verified"], 35)
                self.assertEqual(record["reviewed_workflow_source_mode"], "staged")
                self.assertEqual(record["current_reviewed_workflow_count"], 30)
                self.assertFalse(record["owner_activation_authorized"])

    def test_disposable_active30_cli_runs_actual_committed_contract(self):
        process, output = self.audit(self.active, self.active_head, "active",
                                     cwd=self.foreign, optimized=True)
        self.assertEqual(process.returncode, 0, process.stderr)
        record = json.loads(output.read_bytes())
        self.assertEqual(record["source_commit_sha"], self.active_head)
        self.assertEqual(record["reviewed_workflow_source_mode"], "active")
        self.assertEqual(record["current_reviewed_workflow_count"], 30)
        self.assertFalse(record["new_successor_T_approved"])

    def test_wrong_head_and_dirty_source_are_rejected(self):
        process, output = self.audit(self.staged, "0" * 40, "staged")
        self.assert_rejected(process, "candidate checkout no longer matches")
        self.assertFalse(output.exists())
        dirty = self.staged / "deliberately-untracked-cli-fixture.txt"
        dirty.write_text("synthetic negative source fixture\n", encoding="utf-8")
        try:
            process, output = self.audit(self.staged, self.staged_head, "staged",
                                         cwd=self.foreign, optimized=True)
            self.assert_rejected(process, "workflow review source is dirty/untracked")
            self.assertFalse(output.exists())
        finally:
            dirty.unlink()

    def test_changed_committed_contract_cannot_borrow_original_pin(self):
        fixture = self.clone("changed-contract", self.staged_head, source=self.staged)
        path = fixture / CONTRACT
        path.write_bytes(path.read_bytes() + b"\n# synthetic unreviewed contract drift\n")
        self.commit(fixture, "DISPOSABLE wrong contract negative fixture")
        head = self.git(fixture, "rev-parse", "HEAD").decode().strip()
        process, output = self.audit(fixture, head, "staged", optimized=True)
        self.assert_rejected(process, "differs from committed Git blob pin")
        self.assertFalse(output.exists())

    def test_staged_source_cannot_claim_active30_in_optimized_python(self):
        process, output = self.audit(self.staged, self.staged_head, "active",
                                     optimized=True)
        self.assert_rejected(process, "activated source is not exactly the 30")
        self.assertFalse(output.exists())

    def test_dual_producer_direct_cli_reaches_real_staged_phase_rejection(self):
        for cwd, optimized in ((self.staged, False), (self.foreign, True)):
            with self.subTest(cwd=str(cwd), optimized=optimized):
                output = self.outside / ("dual-staged-" + uuid4().hex)
                process = self.invoke(self.staged, "pr113_dual_tooling_candidate_v2.py", [
                    "--historical-T-source", self.historical,
                    "--current-source", self.staged, "--head", self.staged_head,
                    "--output", output], cwd=cwd, optimized=optimized)
                self.assert_rejected(process, "activated source is not exactly the 30")
                self.assertFalse(output.exists())

    def test_rehearsal_direct_cli_completes_profile_before_output_boundary(self):
        # A regular file used as a parent stops mkdir after the real staged
        # profile succeeds, before either T/H child executes. No replay is claimed.
        parent = self.outside / "synthetic-output-parent-file"
        parent.write_text("intentional post-profile failure fixture\n", encoding="utf-8")
        for cwd, optimized in ((self.staged, False), (self.foreign, True)):
            with self.subTest(cwd=str(cwd), optimized=optimized):
                output = parent / ("packet-" + uuid4().hex)
                diagnostics = self.outside / ("rehearsal-diagnostics-" + uuid4().hex)
                process = self.invoke(self.staged,
                                      "pr113_archive_pre_activation_rehearsal_v1.py", [
                    "--historical-T-source", self.historical,
                    "--current-source", self.staged, "--head", self.staged_head,
                    "--out", output, "--diagnostics", diagnostics],
                    cwd=cwd, optimized=optimized)
                self.assert_rejected(process, "STAGED_T_H_REHEARSAL_BLOCKED")
                outer = json.loads((diagnostics / "outer.execution.json").read_bytes())
                self.assertEqual(outer["stage"], "EVIDENCE_PREPARATION")
                self.assertEqual(outer["outer_exit"], 2)
                self.assertEqual(outer["children"], {})
                self.assertTrue(parent.is_file())
                self.assertFalse(output.exists())

    def test_cached_foreign_reports_module_is_rejected_by_real_loader(self):
        research = self.staged / "verification/research"
        program = (
            "import sys; from pathlib import Path; "
            "import verification.integrity.reports; "
            "sys.path.insert(0,sys.argv[1]); "
            "from pr113_workflow_profile_v2 import _contract; "
            "_contract(Path(sys.argv[2]),sys.argv[3])"
        )
        process = subprocess.run(
            [sys.executable, "-B", "-O", "-c", program,
             str(research), str(self.staged), self.staged_head],
            cwd=self.foreign, env=self.env, capture_output=True, text=True, timeout=45)
        self.assertNotEqual(process.returncode, 0)
        self.assertIn("foreign source", process.stderr)
        self.assertIn("ToolingMigrationError", process.stderr)

    def test_real_dynamic_import_failure_retains_cause_before_any_child(self):
        fixture = self.clone("missing-import", self.staged_head, source=self.staged)
        contract = fixture / CONTRACT
        # Explicitly synthetic committed fault injection, never a replay source.
        contract.write_bytes(contract.read_bytes() +
                             b"\nimport pr113_synthetic_missing_cli_dependency\n")
        manifest_file = fixture / CONTRACT_MANIFEST
        manifest = json.loads(manifest_file.read_bytes())
        manifest["staged_git_blob_oid"] = self.git(
            fixture, "hash-object", str(contract)).decode().strip()
        manifest_file.write_text(json.dumps(manifest, sort_keys=True) + "\n",
                                 encoding="utf-8")
        self.commit(fixture, "DISPOSABLE synthetic import failure fixture")
        head = self.git(fixture, "rev-parse", "HEAD").decode().strip()
        output = self.outside / "missing-import-packet"
        diagnostics = self.outside / "missing-import-diagnostics"
        process = self.invoke(fixture,
                              "pr113_archive_pre_activation_rehearsal_v1.py", [
            "--historical-T-source", self.historical,
            "--current-source", fixture, "--head", head,
            "--out", output, "--diagnostics", diagnostics], cwd=self.foreign)
        self.assert_rejected(process, "versioned contract package import failed")
        outer = json.loads((diagnostics / "outer.execution.json").read_bytes())
        self.assertEqual(outer["outer_exit"], 2)
        self.assertEqual(outer["exception_type"], "ToolingMigrationError")
        self.assertEqual(outer["children"], {})
        trace = (diagnostics / "outer.stderr.log").read_text(encoding="utf-8")
        self.assertIn("ModuleNotFoundError", trace)
        self.assertIn("pr113_synthetic_missing_cli_dependency", trace)
        self.assertIn("versioned contract package import failed", trace)
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
