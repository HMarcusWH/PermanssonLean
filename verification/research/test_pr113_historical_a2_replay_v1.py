"""Non-authorizing historical replay protocol tests with real temporary Git.

Git objects/worktrees, byte pins, dependency links, cleanup and scope checks
are exercised. The compiler and receipt-library adapters below are SYNTHETIC;
none of these tests claims a historical Lean run or independent approval.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

import pr113_historical_a2_replay_v1 as replay


def command(root, *args):
    return subprocess.check_output(
        ["git", "-C", str(root), *args], stderr=subprocess.DEVNULL,
        timeout=30).decode().strip()


def initialize(root):
    root.mkdir(parents=True, exist_ok=True)
    command(root, "init", "-q")
    command(root, "config", "user.name", "Synthetic replay test")
    command(root, "config", "user.email", "synthetic@invalid.example")
    command(root, "config", "commit.gpgsign", "false")


def commit(root):
    command(root, "add", ".")
    command(root, "commit", "-qm", "Synthetic source, not original evidence")
    return command(root, "rev-parse", "HEAD")


class HistoricalA2ReplayTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="a2-replay-test-")
        self.addCleanup(self.temporary.cleanup)
        self.top = Path(self.temporary.name)
        self.root = self.top / "current"
        initialize(self.root)
        (self.root / ".gitignore").write_text(".lake/\n")
        self.package = self.root / ".lake/packages/mockdep"
        initialize(self.package)
        (self.package / "source").write_text("SYNTHETIC dependency\n")
        self.pin = commit(self.package)
        for name in replay.EXECUTORS:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("# Synthetic immutable executor: " + name + "\n")
        (self.root / replay.ORIGINAL_TEST).write_text("# Synthetic original test\n")
        (self.root / "lean-toolchain").write_text("SYNTHETIC toolchain\n")
        (self.root / "lakefile.toml").write_text('name = "synthetic"\n')
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "packagesDir": ".lake/packages", "packages": [
                {"type": "git", "name": "mockdep", "rev": self.pin}]}))
        self.historical = commit(self.root)
        historical_blobs = {
            name: command(self.root, "rev-parse", "HEAD:" + name)
            for name in replay.EXECUTORS}
        original_test = command(self.root, "rev-parse", "HEAD:" + replay.ORIGINAL_TEST)
        # The real historical and current localized_prefix_support.py are NOT
        # identical. Reproduce that difference: the old fixture incorrectly
        # installed the same executor source in both historical/current trees.
        self.support_path = "verification/research/localized_prefix_support.py"
        (self.root / self.support_path).write_text(
            "# SYNTHETIC separately reviewed successor support source\n")
        (self.root / "README.md").write_text("SYNTHETIC future source\n")
        self.head = commit(self.root)
        current_blobs = {
            name: command(self.root, "rev-parse", "HEAD:" + name)
            for name in replay.EXECUTORS}
        self.historical_blobs = historical_blobs
        self.current_blobs = current_blobs
        self.output = self.top / "evidence"
        self.runs = []
        self.current_runs = []
        self.fault = None
        self.declarations = tuple("synthetic.proof%02d" % i for i in range(40))
        self.mutations = {"synthetic_negative_%d" % i: None for i in range(4)}
        historical_module = types.ModuleType("localized_prefix_gate")
        historical_module.check_dependencies = self.dependencies
        historical_module.DECLS = self.declarations
        historical_module.MUTATIONS = self.mutations
        dual = types.ModuleType("pr113_dual_a2_compiler_v2")
        dual.run_historical_verified = self.synthetic_compile
        dual.validate_run = self.validate_run
        semantic = types.ModuleType("pr113_semantic_receipt_v2")
        semantic.validate_compiler_receipt_v2 = self.synthetic_receipt
        router = types.ModuleType("pr113_a2_compiler_route_v3")
        router.select_compiler = lambda root: types.SimpleNamespace(
            checked_sha=command(root, "rev-parse", "HEAD"),
            receipt_format="Permansson.PR113.A2SuccessorCompilerCandidate.v1",
            module=types.SimpleNamespace(verify=self.synthetic_current_compile))
        guards = patch.multiple(replay, HISTORICAL_A2=self.historical,
                                EXECUTORS=current_blobs,
                                HISTORICAL_EXECUTORS=historical_blobs,
                                ORIGINAL_TEST_BLOB=original_test)
        guards.start()
        self.addCleanup(guards.stop)
        modules = patch.dict(sys.modules, {
            "localized_prefix_gate": historical_module,
            "pr113_dual_a2_compiler_v2": dual,
            "pr113_semantic_receipt_v2": semantic,
            "pr113_a2_compiler_route_v3": router,
        })
        modules.start()
        self.addCleanup(modules.stop)

    def dependencies(self, root):
        manifest = json.loads((root / "lake-manifest.json").read_bytes())
        found = {}
        for package in manifest["packages"]:
            path = root / ".lake/packages" / package["name"]
            replay.need(path.is_dir(), "synthetic dependency missing")
            actual = command(path, "rev-parse", "HEAD")
            replay.need(actual == package["rev"], "synthetic dependency revision mismatch")
            replay.need(not command(path, "status", "--porcelain=v1",
                                    "--untracked-files=all"), "synthetic dependency dirty")
            found[package["name"]] = actual
        return found

    def synthetic_compile(self, old, historical, output, mode):
        self.assertNotEqual(old, self.root)
        self.assertEqual(command(old, "rev-parse", "HEAD"), self.historical)
        self.assertEqual(historical, self.historical)
        self.assertEqual(mode, "focused")
        self.assertFalse((old / ".lake/build").exists())
        self.assertEqual((old / ".lake/packages").resolve(),
                         (self.root / ".lake/packages").resolve())
        self.runs.append(str(old))
        output.mkdir(parents=True)
        if self.fault == "compiler_error":
            (output / "compiler.log").write_text("SYNTHETIC compiler unavailable\n")
            raise replay.HistoricalReplayError("SYNTHETIC compiler unavailable")
        row = {
            "format": "Permansson.A2P02.CompilerReceipt.v2",
            "status": "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
            "mode": mode, "source_unchanged": True,
            "source": {"git_head": historical,
                       "git_head_tree": command(old, "rev-parse", "HEAD^{tree}")},
            "declarations": dict.fromkeys(self.declarations, []),
            "mutations": dict.fromkeys(self.mutations, {"status": "SYNTHETIC"}),
        }
        if self.fault == "wrong_head": row["source"]["git_head"] = self.head
        if self.fault == "wrong_tree": row["source"]["git_head_tree"] = "f" * 40
        if self.fault == "wrong_mode": row["mode"] = "full"
        if self.fault == "bad_status": row["status"] = "FAIL_CLOSED"
        if self.fault == "missing_declaration": row["declarations"].pop(self.declarations[0])
        if self.fault == "missing_mutant": row["mutations"].pop(next(iter(self.mutations)))
        (output / "receipt.json").write_text(json.dumps(row))
        if self.fault == "changed_current":
            (self.root / "README.md").write_text("SYNTHETIC source changed while running\n")
        if self.fault == "symlink_artifact":
            (output / "substituted.log").symlink_to(self.root / "README.md")
        if self.fault == "subdirectory_artifact": (output / "unapproved").mkdir()
        return row

    def synthetic_current_compile(self, root, output, *, mode):
        self.assertEqual(root, self.root)
        self.current_runs.append(str(root))
        output.mkdir(parents=True)
        row = {
            "format": "Permansson.PR113.A2SuccessorCompilerCandidate.v1",
            "status": "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
            "mode": mode, "source_unchanged": True,
            "source": {"git_head": command(root, "rev-parse", "HEAD"),
                       "git_head_tree": command(root, "rev-parse", "HEAD^{tree}")},
            "declarations": dict.fromkeys(self.declarations, []),
            "mutations": dict.fromkeys(self.mutations, {"status": "SYNTHETIC"}),
        }
        if self.fault == "current_failure": row["status"] = "FAIL_CLOSED"
        if self.fault == "current_wrong_head": row["source"]["git_head"] = self.historical
        if self.fault == "current_wrong_format": row["format"] = "FORGED_FORMAT"
        (output / "receipt.json").write_text(json.dumps(row))
        return row

    def synthetic_receipt(self, files, prefix, status, mutations):
        raw = files[prefix + "/receipt.json"]
        row = json.loads(raw)
        replay.need(row["status"] == status, "SYNTHETIC receipt rejected")
        return row, hashlib.sha256(raw).hexdigest()

    def validate_run(self, row, status, mutations, declarations):
        replay.need(row["status"] == status and row["source_unchanged"] is True
                    and set(row["mutations"]) == set(mutations)
                    and set(row["declarations"]) == set(declarations),
                    "SYNTHETIC original proof/control inventory incomplete")
        return True

    def no_extra_worktrees(self):
        rows = command(self.root, "worktree", "list", "--porcelain").splitlines()
        self.assertEqual(sum(row.startswith("worktree ") for row in rows), 1)

    def test_fresh_original_source_and_no_current_build_reuse(self):
        self.assertNotEqual(self.historical_blobs[self.support_path],
                            self.current_blobs[self.support_path])
        self.assertEqual(
            self.historical_blobs["verification/research/localized_prefix_gate.py"],
            self.current_blobs["verification/research/localized_prefix_gate.py"])
        (self.root / ".lake/build").mkdir()
        (self.root / ".lake/build/current.olean").write_text("SYNTHETIC current-only cache")
        result = replay.verify(self.root, self.output)
        self.assertEqual(result["historical_source_sha"], self.historical)
        self.assertEqual(result["current_checked_sha"], self.head)
        self.assertEqual(result["execution_scope"], "HISTORICAL_A2_AND_CURRENT_SOURCE")
        self.assertEqual(result["status"], replay.STATUS)
        self.assertTrue(result["current_compiler_required_separately"])
        for flag in ("historical_project_build_imported", "historical_executor_modified",
                     "independent_security_review", "mathematical_acceptance", "merge_authorized"):
            self.assertIs(result[flag], False)
        self.assertEqual(len(self.runs), 1)
        self.assertEqual(len(self.current_runs), 1)
        self.assertTrue(result["current_source_compiler_executed"])
        self.no_extra_worktrees()
        self.assertTrue((self.package / "source").is_file())
        self.assertFalse(command(self.root, "status", "--porcelain=v1", "--untracked-files=all"))

    def test_invalid_original_receipt_never_turns_green(self):
        for fault in ("wrong_head", "wrong_tree", "wrong_mode", "bad_status",
                      "missing_declaration", "missing_mutant", "symlink_artifact",
                      "subdirectory_artifact", "current_failure", "current_wrong_head",
                      "current_wrong_format"):
            self.fault = fault
            with self.subTest(fault=fault), self.assertRaises(replay.HistoricalReplayError):
                replay.verify(self.root, self.top / fault)
            self.no_extra_worktrees()

    def test_failure_retains_logs_and_cleans_checkout(self):
        self.fault = "compiler_error"
        with self.assertRaisesRegex(replay.HistoricalReplayError, "compiler unavailable"):
            replay.verify(self.root, self.output)
        self.assertIn("unavailable", (self.output / "historical_original_A2/compiler.log").read_text())
        self.no_extra_worktrees()

    def test_current_source_cannot_change_during_replay(self):
        self.fault = "changed_current"
        with self.assertRaisesRegex(replay.HistoricalReplayError, "source contains"):
            replay.verify(self.root, self.output)
        self.no_extra_worktrees()

    def test_dirty_current_source_rejects_before_compilation(self):
        (self.root / "untracked").write_text("SYNTHETIC dirt")
        with self.assertRaises(replay.HistoricalReplayError):
            replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_dirty_dependency_rejects_before_compilation(self):
        (self.package / "source").write_text("SYNTHETIC dirty dependency")
        with self.assertRaisesRegex(replay.HistoricalReplayError, "dependency dirty"):
            replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_wrong_dependency_revision_rejects_before_compilation(self):
        (self.package / "source").write_text("SYNTHETIC new dependency revision")
        commit(self.package)
        with self.assertRaisesRegex(replay.HistoricalReplayError, "revision mismatch"):
            replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_changed_dependency_manifest_never_bridges(self):
        (self.root / "lake-manifest.json").write_text('{"packages": []}\n')
        commit(self.root)
        with self.assertRaisesRegex(replay.HistoricalReplayError, "dependency source differs"):
            replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_historical_support_cannot_borrow_current_blob_pin(self):
        with patch.dict(replay.HISTORICAL_EXECUTORS,
                        {self.support_path: self.current_blobs[self.support_path]}):
            with self.assertRaisesRegex(replay.HistoricalReplayError,
                                        "historical A2 executor Git identity changed"):
                replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_current_support_cannot_borrow_historical_blob_pin(self):
        with patch.dict(replay.EXECUTORS,
                        {self.support_path: self.historical_blobs[self.support_path]}):
            with self.assertRaisesRegex(replay.HistoricalReplayError,
                                        "current A2 executor Git identity changed"):
                replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_unreviewed_current_support_change_is_rejected(self):
        (self.root / self.support_path).write_text(
            "# SYNTHETIC unreviewed current support change\n")
        commit(self.root)
        with self.assertRaisesRegex(replay.HistoricalReplayError,
                                    "current A2 executor Git identity changed"):
            replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_changed_original_executor_never_runs(self):
        path = next(iter(replay.EXECUTORS))
        (self.root / path).write_text("# SYNTHETIC changed executor\n")
        commit(self.root)
        with self.assertRaisesRegex(replay.HistoricalReplayError, "executor Git identity"):
            replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_preexisting_historical_build_is_rejected(self):
        genuine = replay.dependency_bridge
        def injected(current, old):
            (old / ".lake/build").mkdir(parents=True)
            return genuine(current, old)
        with patch.object(replay, "dependency_bridge", side_effect=injected):
            with self.assertRaisesRegex(replay.HistoricalReplayError, "build objects"):
                replay.verify(self.root, self.output)
        self.assertFalse(self.runs)
        self.no_extra_worktrees()

    def test_existing_output_is_not_overwritten(self):
        self.output.mkdir()
        marker = self.output / "old.log"
        marker.write_text("SYNTHETIC prior evidence")
        with self.assertRaises(replay.HistoricalReplayError):
            replay.verify(self.root, self.output)
        self.assertEqual(marker.read_text(), "SYNTHETIC prior evidence")
        self.assertFalse(self.runs)

    def test_source_overlap_or_symlink_output_rejected(self):
        alias = self.top / "alias"
        alias.symlink_to(self.root, target_is_directory=True)
        for target in (self.root / "new", alias / "new"):
            with self.subTest(target=target), self.assertRaises(replay.HistoricalReplayError):
                replay.verify(self.root, target)
        self.assertFalse(self.runs)
        self.assertFalse((self.root / "new").exists())

    def test_unknown_compiler_mode_not_a_fallback(self):
        with self.assertRaises(replay.HistoricalReplayError):
            replay.verify(self.root, self.output, mode="pretend")
        self.assertFalse(self.runs)


class RealHistoricalA2GitPins(unittest.TestCase):
    def test_immutable_original_and_current_source_pins_are_revision_scoped(self):
        root = Path(__file__).resolve().parents[2]
        head = replay.scalar(root, "rev-parse", "HEAD")
        self.assertEqual(set(replay.EXECUTORS), set(replay.HISTORICAL_EXECUTORS))
        path = "verification/research/localized_prefix_support.py"
        self.assertNotEqual(replay.EXECUTORS[path],
                            replay.HISTORICAL_EXECUTORS[path])
        gate = "verification/research/localized_prefix_gate.py"
        self.assertEqual(replay.EXECUTORS[gate],
                         replay.HISTORICAL_EXECUTORS[gate])
        for label, revision, pins in (
                ("historical", replay.HISTORICAL_A2,
                 replay.HISTORICAL_EXECUTORS),
                ("current", head, replay.EXECUTORS)):
            for member, oid in pins.items():
                with self.subTest(scope=label, member=member):
                    self.assertEqual(
                        replay.scalar(root, "rev-parse", revision + ":" + member),
                        oid)
                    raw = replay.git(root, "show", revision + ":" + member)
                    self.assertEqual(
                        hashlib.sha1(
                            b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw
                        ).hexdigest(), oid)
                    if label == "current":
                        self.assertEqual((root / member).read_bytes(), raw)
        self.assertEqual(replay.scalar(
            root, "rev-parse", replay.HISTORICAL_A2 + ":" + replay.ORIGINAL_TEST),
            replay.ORIGINAL_TEST_BLOB)


if __name__ == "__main__":
    unittest.main()
