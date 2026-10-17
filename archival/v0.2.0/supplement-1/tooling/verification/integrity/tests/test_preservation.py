import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import unittest
from unittest import mock

from verification.integrity.git_objects import GitEntry, GitRepo
from verification.integrity.inventory import _load_reference_inventory, load_reference_inventory
from verification.integrity.policy import ACCEPTED_RELEASE
from verification.integrity.preservation import (
    compare_preserved, validate_maintenance_scope, verify_preservation,
)
from verification.integrity.reports import HardeningError
from verification.integrity.tests._fixtures import GitFixture, json_bytes


class PreservationTests(unittest.TestCase):
    def setUp(self):
        self.fixture = GitFixture()
        self.addCleanup(self.fixture.close)

    def rejected(self, changes, code):
        self.assertEqual("PASS", self.fixture.compare(self.fixture.accepted).status)
        candidate = self.fixture.commit(changes)
        result = self.fixture.compare(candidate)
        self.assertEqual(code, result.error_code)
        with self.assertRaises(HardeningError) as raised:
            result.require_pass()
        self.assertEqual(code, raised.exception.code)
        return result

    def test_pres_01_actual_369_unchanged(self):
        repo = GitRepo(Path(__file__).resolve().parents[3])
        self.addCleanup(repo._config.cleanup)
        details = verify_preservation(repo, ACCEPTED_RELEASE)
        self.assertEqual(369, details["protected_count"])
        self.assertEqual("canonical_commit_objects", details["scope"])

    def test_pres_02_core_comment(self):
        path = b"PermanssonLean/Regime/Constitution.lean"
        self.rejected({path: ("100644", self.fixture.files[path] + b"-- comment\n")}, "E_PROTECTED_CONTENT")

    def test_pres_03_solver_comment(self):
        path = b"PermanssonResearch/ReverseSolver/C10ReceiptSemantics.lean"
        self.rejected({path: ("100644", self.fixture.files[path] + b"-- comment\n")}, "E_PROTECTED_CONTENT")

    def test_pres_04_semantic_edit(self):
        self.rejected({b"PermanssonLean/Regime/Constitution.lean": ("100644", b"theorem changed : False := by contradiction\n")},
                      "E_PROTECTED_CONTENT")

    def test_pres_05_deletion(self):
        self.rejected({b"paper/original.md": None}, "E_PROTECTED_MISSING")

    def test_pres_06_rename(self):
        self.rejected({b"paper/original.md": None,
                       b"paper/renamed.md": ("100644", self.fixture.files[b"paper/original.md"])},
                      "E_PROTECTED_MISSING")

    def test_pres_07_executable_mode(self):
        self.rejected({b"paper/original.md": ("100755", self.fixture.files[b"paper/original.md"])},
                      "E_PROTECTED_MODE")

    def test_pres_08_symlink_replacement(self):
        self.rejected({b"paper/original.md": ("120000", b"../actual-bytes.md")}, "E_PROTECTED_TYPE")

    def test_pres_09_gitlink_file_and_root(self):
        for path in (b"paper/original.md", b"paper"):
            with self.subTest(path=path):
                self.rejected({path: ("160000", self.fixture.accepted)}, "E_PROTECTED_TYPE")

    def test_pres_10_historical_addition(self):
        self.rejected({b"paper/new.md": ("100644", b"addition\n")}, "E_CLOSED_ADDITION")

    def test_pres_11_version_additions(self):
        for path in (b"release/v0.2.0/new.txt", b"release/v0.2.0/tmp/x", b"release/v0.2.0/__pycache__/x"):
            with self.subTest(path=path):
                self.rejected({path: ("100644", b"addition\n")}, "E_CLOSED_ADDITION")

    def test_pres_12_nested_addition(self):
        self.rejected({b"paper/nested/new.md": ("100644", b"addition\n")}, "E_CLOSED_ADDITION")

    def test_pres_13_prefix_lookalike(self):
        candidate = self.fixture.commit({b"paper2/note.md": ("100644", b"allowed\n")})
        self.assertEqual("PASS", self.fixture.compare(candidate).status)

    def test_pres_14_new_research(self):
        candidate = self.fixture.commit({b"PermanssonResearch/ReverseSolver/NewResearch.lean":
                                         ("100644", b"-- future research\n")})
        self.assertEqual("PASS", self.fixture.compare(candidate).status)

    def test_pres_15_new_documentation(self):
        candidate = self.fixture.commit({b"docs/new-maintenance-guide.md": ("100644", b"allowed\n")})
        self.assertEqual("PASS", self.fixture.compare(candidate).status)

    def test_pres_16_new_release_version(self):
        candidate = self.fixture.commit({b"release/v0.2.1/example.txt": ("100644", b"future\n")})
        self.assertEqual("PASS", self.fixture.compare(candidate).status)

    def test_pres_17_candidate_manifest_repair(self):
        data = copy.deepcopy(self.fixture.manifest)
        data["protected_files"].pop()
        repaired = json_bytes(data)
        self.rejected({b"release/v0.2.0/manifest.json": ("100644", repaired),
                       b"release/Permansson_v0.2.0_research-kit.zip.sha256":
                       ("100644", hashlib.sha256(repaired).hexdigest().encode())}, "E_PROTECTED_CONTENT")

    def test_pres_18_published_zip_replacement(self):
        replacement = b"replacement ZIP\n"
        self.rejected({b"release/Permansson_v0.2.0_research-kit.zip": ("100644", replacement),
                       b"release/Permansson_v0.2.0_research-kit.zip.sha256":
                       ("100644", hashlib.sha256(replacement).hexdigest().encode())}, "E_PROTECTED_CONTENT")

    def test_pres_19_scientific_promotion(self):
        self.rejected({b"release/v0.2.0/manuscript.json": ("100644", b'{"F1.MA2":"PROVED"}\n'),
                       b"release/v0.2.0/output.tex": ("100644", b"Promoted outputs\n")},
                      "E_PROTECTED_CONTENT")

    def test_pres_20_checkout_line_endings(self):
        # This test runs on Windows locally and Linux CI. The checkout settings
        # change working bytes, never the canonical committed blob.
        path = b"paper/original.md"
        self.fixture.repo.run("reset", "--hard", self.fixture.accepted)
        actual = self.fixture.root / os.fsdecode(path)
        observed = []
        for autocrlf in ("false", "true"):
            actual.unlink(missing_ok=True)
            self.fixture.repo.run("-c", "core.autocrlf=" + autocrlf, "checkout-index", "--force", "--", os.fsdecode(path))
            observed.append(actual.read_bytes())
            self.assertEqual("PASS", self.fixture.compare(self.fixture.accepted).status)
        self.assertEqual(b"Accepted paper\n", observed[0])
        self.assertEqual(b"Accepted paper\r\n", observed[1])

    def test_pres_21_committed_crlf(self):
        path = b"paper/original.md"
        self.rejected({path: ("100644", self.fixture.files[path].replace(b"\n", b"\r\n"))},
                      "E_PROTECTED_CONTENT")

    def test_pres_22_dirty_workspace_caveat(self):
        self.fixture.repo.run("reset", "--hard", self.fixture.accepted)
        (self.fixture.root / "paper/original.md").write_bytes(b"dirty working file\n")
        self.assertEqual("PASS", self.fixture.compare(self.fixture.accepted).status)
        # Production report explicitly describes commit objects, never cleanliness.
        repo = GitRepo(Path(__file__).resolve().parents[3])
        self.addCleanup(repo._config.cleanup)
        self.assertEqual("canonical_commit_objects", verify_preservation(repo, ACCEPTED_RELEASE)["scope"])

    def test_pres_23_maintenance_scope_is_separate(self):
        candidate = self.fixture.commit({b"PermanssonResearch/ReverseSolver/NewResearch.lean":
                                         ("100644", b"-- future research\n")})
        self.assertEqual("PASS", self.fixture.compare(candidate).status)
        with mock.patch("verification.integrity.preservation.ACCEPTED_RELEASE", self.fixture.accepted):
            validate_maintenance_scope(self.fixture.repo, self.fixture.accepted)
            with self.assertRaises(HardeningError) as raised:
                validate_maintenance_scope(self.fixture.repo, candidate)
            self.assertEqual("E_MAINTENANCE_SCOPE", raised.exception.code)

    def test_protected_root_symlink_and_file_directory(self):
        self.rejected({b"paper": ("120000", b"elsewhere")}, "E_PROTECTED_TYPE")
        self.rejected({b"paper/original.md": None,
                       b"paper/original.md/child": ("100644", b"directory replacement\n")}, "E_PROTECTED_TYPE")

    def test_empty_tree_closed_topology(self):
        # Empty subtrees cannot be represented by an ordinary index/worktree,
        # but valid Git plumbing can commit them. Exercise those actual objects.
        repo = self.fixture.repo
        empty = repo.run("mktree", input=b"").strip().decode()
        root_records = repo._parse_tree(repo.run("ls-tree", "-z", self.fixture.accepted))

        def commit_tree(records):
            raw = b"".join(entry.mode.encode() + b" " + entry.object_type.encode() + b" "
                           + entry.oid.encode() + b"\t" + path + b"\0"
                           for path, entry in records.items())
            tree = repo.run("mktree", "-z", input=raw).strip().decode()
            return repo.run("-c", "user.name=Topology Fixture", "-c", "user.email=fixture@example.invalid",
                            "commit-tree", tree, "-p", self.fixture.accepted,
                            "-m", "manual empty-tree fixture").strip().decode()

        def compare(candidate):
            reference = _load_reference_inventory(repo, self.fixture.policy)
            return compare_preserved(reference, repo.tree_entries(self.fixture.accepted),
                                     repo.tree_entries(candidate), repo.blob,
                                     closed_roots=self.fixture.policy.closed_roots)

        self.assertEqual("PASS", compare(self.fixture.accepted).status)
        ordinary = dict(root_records)
        ordinary[b"docs-empty"] = GitEntry(b"docs-empty", "040000", "tree", empty)
        self.assertEqual("PASS", compare(commit_tree(ordinary)).status)

        paper = root_records[b"paper"]
        children = repo.run("ls-tree", "-z", paper.oid)
        children += b"040000 tree " + empty.encode() + b"\tzzz-empty\0"
        expanded_paper = repo.run("mktree", "-z", input=children).strip().decode()
        mutated = dict(root_records)
        mutated[b"paper"] = GitEntry(b"paper", "040000", "tree", expanded_paper)
        self.assertEqual("E_CLOSED_ADDITION", compare(commit_tree(mutated)).error_code)

        mutated[b"paper"] = GitEntry(b"paper", "040000", "tree", empty)
        self.assertEqual("E_PROTECTED_MISSING", compare(commit_tree(mutated)).error_code)

        new_closed_root = dict(root_records)
        new_closed_root[b"provenance"] = GitEntry(b"provenance", "040000", "tree", empty)
        self.assertEqual("E_CLOSED_ADDITION", compare(commit_tree(new_closed_root)).error_code)
