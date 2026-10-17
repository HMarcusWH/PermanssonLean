from dataclasses import replace
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
import zlib
from unittest import mock

from verification.integrity.git_objects import GitRepo
from verification.integrity.inventory import _load_reference_inventory, load_reference_inventory, parse_manifest
from verification.integrity.policy import ACCEPTED_RELEASE, ACCEPTED_RELEASE_TREE
from verification.integrity.reports import HardeningError
from verification.integrity.tests._fixtures import GitFixture, json_bytes


class ReferenceTests(unittest.TestCase):
    def setUp(self):
        self.fixture = GitFixture()
        self.addCleanup(self.fixture.close)

    def assert_code(self, code, callback):
        with self.assertRaises(HardeningError) as raised:
            callback()
        self.assertEqual(code, raised.exception.code)

    def test_ref_01_accepted_authority(self):
        inventory = _load_reference_inventory(self.fixture.repo, self.fixture.policy)
        self.assertEqual(9, len(inventory))
        repo = GitRepo(Path(__file__).resolve().parents[3])
        self.addCleanup(repo._config.cleanup)
        self.assertEqual(ACCEPTED_RELEASE_TREE, repo.commit(ACCEPTED_RELEASE).tree)
        self.assertEqual(369, len(load_reference_inventory(repo)))

    def test_ref_02_missing_authority(self):
        policy = replace(self.fixture.policy, accepted_release="0" * 40)
        self.assert_code("E_REFERENCE_MISSING", lambda: _load_reference_inventory(self.fixture.repo, policy))

    def test_ref_03_candidate_requires_full_identity(self):
        for value in (self.fixture.accepted[:10], "HEAD~1", "--help", "\n" + self.fixture.accepted):
            with self.subTest(value=value):
                self.assert_code("E_REFERENCE_ID", lambda: self.fixture.repo.validate_candidate(
                    value, accepted_sha=self.fixture.accepted))

    def test_ref_04_wrong_authority_tree(self):
        policy = replace(self.fixture.policy, accepted_tree="0" * 40)
        self.assert_code("E_REFERENCE_ID", lambda: _load_reference_inventory(self.fixture.repo, policy))

    def test_ref_05_duplicate_json_key(self):
        self.assert_code("E_POLICY_INVENTORY", lambda: parse_manifest(
            b'{"schema_version":1,"schema_version":1}', self.fixture.policy))

    def test_ref_06_duplicate_historical_path(self):
        data = copy.deepcopy(self.fixture.manifest)
        data["protected_files"][1] = data["protected_files"][0]
        policy = self.fixture.malformed_authority(data)
        self.assert_code("E_POLICY_INVENTORY", lambda: _load_reference_inventory(self.fixture.repo, policy))

    def test_ref_07_historical_count(self):
        for rows in (self.fixture.manifest["protected_files"][:-1],
                     self.fixture.manifest["protected_files"] + [self.fixture.manifest["protected_files"][0]]):
            with self.subTest(count=len(rows)):
                data = dict(self.fixture.manifest, protected_files=rows)
                policy = self.fixture.malformed_authority(data)
                self.assert_code("E_POLICY_INVENTORY", lambda: _load_reference_inventory(self.fixture.repo, policy))

    def test_ref_08_blob_metadata(self):
        for key, value in (("mode", "100755"), ("git_blob_sha1", "0" * 40), ("sha256", "0" * 64)):
            with self.subTest(key=key):
                data = copy.deepcopy(self.fixture.manifest)
                data["protected_files"][0][key] = value
                policy = self.fixture.malformed_authority(data)
                self.assert_code("E_POLICY_INVENTORY", lambda: _load_reference_inventory(self.fixture.repo, policy))

    def test_ref_09_actual_shallow_clone(self):
        target = self.fixture.root / "shallow-clone"
        result = subprocess.run([self.fixture.repo.executable, "-c", "protocol.file.allow=always", "clone", "--depth=1",
                                 self.fixture.root.as_uri(), str(target)], capture_output=True,
                                env={key: value for key, value in self.fixture.repo.env.items()
                                     if key != "GIT_INDEX_FILE"})
        self.assertEqual(0, result.returncode, result.stderr.decode("utf-8", "replace"))
        self.assert_code("E_HISTORY_SHALLOW", lambda: GitRepo(target))

    def test_ref_10_promisor_metadata(self):
        self.fixture.repo.run("config", "remote.origin.promisor", "true")
        self.assert_code("E_HISTORY_EXTERNAL", lambda: GitRepo(self.fixture.root))

    def test_ref_11_borrowed_objects(self):
        alternate = self.fixture.root / ".git" / "objects" / "info" / "alternates"
        alternate.write_text(str(self.fixture.root / "elsewhere") + "\n")
        self.assert_code("E_HISTORY_EXTERNAL", lambda: GitRepo(self.fixture.root))
        alternate.unlink()
        with mock.patch.dict(os.environ, {"GIT_ALTERNATE_OBJECT_DIRECTORIES": str(self.fixture.root)}):
            self.assert_code("E_HISTORY_EXTERNAL", lambda: GitRepo(self.fixture.root))

    def test_ref_12_replace_and_graft(self):
        other = self.fixture.commit({b"docs/new.md": ("100644", b"new\n")})
        self.fixture.repo.run("update-ref", "refs/replace/" + self.fixture.accepted, other)
        self.assert_code("E_HISTORY_EXTERNAL", lambda: GitRepo(self.fixture.root))
        self.fixture.repo.run("update-ref", "-d", "refs/replace/" + self.fixture.accepted)
        graft = self.fixture.root / ".git" / "info" / "grafts"
        graft.write_text(self.fixture.accepted + "\n")
        self.assert_code("E_HISTORY_EXTERNAL", lambda: GitRepo(self.fixture.root))

    def test_ref_13_raw_path_boundaries(self):
        paths = (b"docs/has space.md", b"docs/has\ttab.md", b"docs/has\nnewline.md")
        candidate = self.fixture.commit({path: ("100644", b"unprotected\n") for path in paths})
        self.assertEqual("PASS", self.fixture.compare(candidate).status)
        self.assertTrue(set(paths).issubset(self.fixture.repo.tree(candidate)))

    def test_ref_14_no_refresh_cli(self):
        root = Path(__file__).resolve().parents[3]
        for option in ("--refresh", "--update-baseline", "--policy"):
            with self.subTest(option=option):
                result = subprocess.run([sys.executable, "-B", "-m", "verification.integrity.preservation",
                                         "--repo", str(root), "--candidate", ACCEPTED_RELEASE,
                                         "--report", str(self.fixture.root / "report.json"), option],
                                        cwd=root, capture_output=True)
                self.assertEqual(2, result.returncode, result.stderr)

    def test_ref_15_candidate_outside_ancestry(self):
        unrelated = self.fixture.commit({b"unrelated": ("100644", b"other\n")}, parent=None)
        self.assert_code("E_ANCESTRY", lambda: self.fixture.repo.validate_candidate(
            unrelated, accepted_sha=self.fixture.accepted))

    def test_corrupt_loose_subtree_is_rejected(self):
        # Positive control exercises both the leaf and directory lookup APIs.
        accepted = self.fixture.accepted
        repo = self.fixture.repo
        self.assertIn(b"paper/original.md", repo.tree(accepted))
        subtree = repo.entry(accepted, b"paper")
        self.assertEqual("tree", subtree.object_type)
        self.assertEqual(b"paper/original.md", repo.entry(accepted, b"paper/original.md").path)
        object_type, payload = repo.object(subtree.oid)
        self.assertEqual("tree", object_type)
        altered = payload.replace(b"original.md", b"tampered.md")
        self.assertNotEqual(payload, altered)
        # The zlib framing and declared size are valid. Only the filename-to-OID
        # binding is corrupt, so unchecked ls-tree would silently show new paths.
        loose = repo.common_dir / "objects" / subtree.oid[:2] / subtree.oid[2:]
        loose.chmod(0o600)
        loose.write_bytes(zlib.compress(b"tree " + str(len(altered)).encode() + b"\0" + altered))
        unchecked = repo.run("ls-tree", "-r", "-z", "--full-tree", accepted)
        self.assertIn(b"paper/tampered.md", unchecked)
        for operation in ("tree", "entry"):
            with self.subTest(operation=operation):
                fresh = GitRepo(self.fixture.root)
                self.addCleanup(fresh.close)
                callback = (lambda: fresh.tree(accepted)) if operation == "tree" else (
                    lambda: fresh.entry(accepted, b"paper/original.md"))
                self.assert_code("E_GIT_OBJECT", callback)

    def test_tree_gitlink_target_may_be_external(self):
        external = "3" * 40
        candidate = self.fixture.commit({b"docs/external-submodule": ("160000", external)})
        entry = self.fixture.repo.tree(candidate)[b"docs/external-submodule"]
        self.assertEqual(("160000", "commit", external), (entry.mode, entry.object_type, entry.oid))
