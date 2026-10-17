"""Restore real tiny Git graphs and assert precise downstream rejection stages."""
from __future__ import annotations

from copy import deepcopy
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from verification.integrity.git_objects import GitRepo
from verification.integrity.reports import HardeningError
from verification.archive.acquire_evidence import validate_r_identity, validate_r_bytes
from verification.archive.create_bundle import (REF_PREFIX, R_IDENTITY, R_SOURCE, build_history,
                                                object_inventory, validate_bindings)
from verification.archive.manifest import (FORMAT, MAX_BUNDLE, MAX_METADATA, MAX_OBJECT, digest,
                                           read_bounded, safe_path, scan_files, stable_json,
                                           strict_json, validate_manifest)
from verification.archive.offline_smoke import launch_offline, require_dependencies, sanitized_environment, invocation_context
from verification.archive.verify_bundle import (bundle_header, parse_objects, require_commit_targets,
                                                restore_history, validate_c10_content, verify_supplement, require_empty_scratch)


def manifest_fixture(root):
    root = Path(root)
    for name, content in {"history.bundle": b"fixture bundle", "refs.json": b"{}\n", "objects.jsonl": b"{}\n"}.items():
        (root / name).write_bytes(content)
    files = scan_files(root)
    records = {row["path"]: row for row in files}
    return {"format": FORMAT, "schema_version": 1, "repository": "HMarcusWH/PermanssonLean",
            "accepted_release": "a" * 40, "accepted_tree": "b" * 40, "provenance": {},
            "registry": {"path": "refs.json", "sha256": records["refs.json"]["sha256"], "count": 36, "distinct_commits": 26},
            "bundle": {"path": "history.bundle", "format": 2, "size": records["history.bundle"]["size"], "sha256": records["history.bundle"]["sha256"]},
            "object_inventory": {"path": "objects.jsonl", "sha256": records["objects.jsonl"]["sha256"], "count": 1, "uncompressed_size": 0},
            "files": files, "r_c10": {}, "tooling": {"source_commit": "c" * 40, "files": []},
            "dependencies": {"python": "3.13", "git": "SHA-1 Git with bundle v2", "pypdf": "6.10.0"},
            "reproduction_levels": {"source_restore": True, "artifact_replay": True, "fresh_lean_execution": False, "publisher_authentication": False}}


def write_manifest(root, value):
    payload = stable_json(value)
    (Path(root) / "archive-manifest.json").write_bytes(payload)
    (Path(root) / "archive-manifest.sha256").write_bytes((digest(payload) + "  archive-manifest.json\n").encode())


def capture_fixture_path():
    root = Path(__file__).resolve().parents[3]
    locations = [root / "archival/v0.2.0/supplement-1/evidence",
                 root.parent / "artifacts/hardening-capture"]
    for path in locations:
        if (path / "R-c10.zip").is_file():
            return path
    raise HardeningError("E_DEPENDENCY_MISSING", "Real acquired historical evidence fixture is required", 3)


class Graph:
    def __init__(self, root):
        self.root = Path(root)
        subprocess.run([shutil.which("git"), "-c", "init.templateDir=", "init", "--bare", str(self.root)],
                       check=True, capture_output=True, timeout=60)
        self.repo = GitRepo(self.root)
        self.repo.run("config", "user.name", "Archive fixture")
        self.repo.run("config", "user.email", "archive@example.invalid")
        self.t0 = self.tree(b"base\n")
        self.base = self.commit(self.t0, [], "base")
        self.t1 = self.tree(b"head\n")
        self.head = self.commit(self.t1, [self.base], "head")
        self.synthetic = self.commit(self.t1, [self.base, self.head], "synthetic")
        self.main = self.commit(self.t1, [self.base, self.head], "main")
        self.registry = {"refs": [{"ref": REF_PREFIX + name, "commit": oid}
                                  for name, oid in sorted({"base": self.base, "head": self.head,
                                                          "synthetic": self.synthetic, "main": self.main}.items())],
                         "milestones": [{"anchor": "fixture", "head": self.head, "base": self.base,
                                         "synthetic": self.synthetic, "main": self.main}]}

    def tree(self, payload):
        blob = self.repo.run("hash-object", "-w", "--stdin", input=payload).strip().decode()
        return self.repo.run("mktree", input=("100644 blob " + blob + "\tfile.txt\n").encode()).strip().decode()

    def commit(self, tree, parents, message):
        args = ["commit-tree", tree]
        for parent in parents:
            args.extend(["-p", parent])
        return self.repo.run(*args, input=(message + "\n").encode()).strip().decode()


class ArchiveGraphTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="permansson-archive-tests-")
        cls.directory = Path(cls.temporary.name)
        cls.graph = Graph(cls.directory / "source.git")
        cls.bundle = cls.directory / "full.bundle"
        cls.objects = build_history(cls.graph.repo, cls.graph.registry, cls.bundle, production=False)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def scratch(self):
        return self.directory / ("scratch-" + self._testMethodName)

    def reject(self, code, function, *args, **kwargs):
        with self.assertRaises(HardeningError) as caught:
            function(*args, **kwargs)
        self.assertEqual(caught.exception.code, code, str(caught.exception))

    def test_arch_01_named_synthetic_full_restore(self):
        restored = restore_history(self.bundle, self.scratch(), self.graph.registry, self.objects)
        self.assertEqual(restored.commit(self.graph.synthetic).parents, (self.graph.base, self.graph.head))
        self.assertEqual(object_inventory(restored), self.objects)
        self.assertFalse(restored.run("remote").strip())

    def test_arch_02_main_only_omits_synthetic(self):
        registry = deepcopy(self.graph.registry)
        registry["refs"] = [row for row in registry["refs"] if row["ref"].endswith("/main")]
        bundle = self.directory / "main-only.bundle"
        build_history(self.graph.repo, registry, bundle, production=False)
        self.reject("E_BUNDLE_REFS", restore_history, bundle, self.scratch(), self.graph.registry, self.objects)

    def test_arch_03_missing_required_commit_target(self):
        # Exercise the ref-target validator directly after a successful real
        # import, rather than claiming a prior checksum error tested this stage.
        restored = restore_history(self.bundle, self.scratch(), self.graph.registry, self.objects)
        refs = {REF_PREFIX + "missing-synthetic": "0" * 40}
        self.reject("E_BUNDLE_REFS", require_commit_targets, restored, refs)

    def test_arch_04_wrong_valid_ref_target(self):
        registry = deepcopy(self.graph.registry)
        for row in registry["refs"]:
            if row["ref"].endswith("/synthetic"):
                row["commit"] = self.graph.main
        self.reject("E_BUNDLE_REFS", restore_history, self.bundle, self.scratch(), registry, self.objects)

    def test_arch_05_incremental_prerequisite(self):
        ref = REF_PREFIX + "incremental"
        self.graph.repo.run("update-ref", ref, self.graph.main)
        bundle = self.directory / "incremental.bundle"
        self.graph.repo.run("bundle", "create", "--version=2", str(bundle), ref, "^" + self.graph.base)
        self.reject("E_BUNDLE_PREREQUISITE", bundle_header, bundle)

    def test_arch_06_intact_header_truncated_pack_import(self):
        raw = self.bundle.read_bytes()
        pack = raw.index(b"\n\n") + 2
        broken = self.directory / "truncated.bundle"
        broken.write_bytes(raw[:pack + 20])
        self.assertEqual(bundle_header(broken), bundle_header(self.bundle))
        self.reject("E_BUNDLE_IMPORT", restore_history, broken, self.scratch(), self.graph.registry, self.objects)

    def test_arch_08_corrupt_object_fails_strict_fsck(self):
        def corrupt(repo):
            path = repo.common_dir / "objects" / "ab" / ("c" * 38)
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(b"not a zlib Git object")
        self.reject("E_GIT_FSCK", restore_history, self.bundle, self.scratch(), self.graph.registry,
                    self.objects, after_import=corrupt)

    def test_arch_09_extra_ref(self):
        registry = deepcopy(self.graph.registry)
        registry["refs"].append({"ref": REF_PREFIX + "maintenance", "commit": self.graph.main})
        extra = self.directory / "extra-ref.bundle"
        build_history(self.graph.repo, registry, extra, production=False)
        self.reject("E_BUNDLE_REFS", restore_history, extra, self.scratch(), self.graph.registry, self.objects)

    def test_arch_10_extra_object_inventory(self):
        extra = self.graph.repo.run("hash-object", "-w", "--stdin", input=b"unrelated\n").strip().decode()
        expected = sorted([*self.objects, {"oid": extra, "type": "blob", "size": 10, "sha256": digest(b"unrelated\n")}], key=lambda x: x["oid"])
        self.reject("E_OBJECT_INVENTORY", restore_history, self.bundle, self.scratch(), self.graph.registry, expected)

    def test_arch_11_ordered_parent_reversal(self):
        registry = deepcopy(self.graph.registry)
        reverse = self.graph.commit(self.graph.t1, [self.graph.head, self.graph.base], "reversed")
        registry["milestones"][0]["synthetic"] = reverse
        self.reject("E_PARENT_BINDING", validate_bindings, self.graph.repo, registry, production=False)

    def test_arch_12_synthetic_main_tree_difference(self):
        registry = deepcopy(self.graph.registry)
        wrong = self.graph.commit(self.graph.t0, [self.graph.base, self.graph.head], "different tree")
        registry["milestones"][0]["main"] = wrong
        self.reject("E_TREE_BINDING", validate_bindings, self.graph.repo, registry, production=False)

    def test_arch_13_builder_rejects_extra_production_root(self):
        from verification.archive.create_bundle import derive_registry
        # Private authority injection is in the test only, never production CLI.
        approved = deepcopy(self.graph.registry)
        expanded = deepcopy(approved)
        expanded["refs"].append({"ref": REF_PREFIX + "maintenance", "commit": self.graph.main})
        with patch("verification.archive.create_bundle.derive_registry", return_value=approved):
            self.reject("E_BUNDLE_REFS", validate_bindings, self.graph.repo, expanded)

    def test_arch_22_borrowed_offline_prerequisite(self):
        with patch.dict(os.environ, {"GIT_ALTERNATE_OBJECT_DIRECTORIES": str(self.graph.root / "objects")}):
            self.reject("E_HISTORY_EXTERNAL", restore_history, self.bundle, self.scratch(), self.graph.registry, self.objects)

    def test_arch_25_delivered_bytes_unchanged(self):
        before = digest(self.bundle.read_bytes())
        restore_history(self.bundle, self.scratch(), self.graph.registry, self.objects)
        self.assertEqual(before, digest(self.bundle.read_bytes()))

    def test_arch_26_bundle_bytes_and_object_semantics_separate(self):
        duplicate = self.directory / "second.bundle"
        objects = build_history(self.graph.repo, self.graph.registry, duplicate, production=False)
        # No universal pack-byte equality assertion: exact closure is required.
        self.assertEqual(objects, self.objects)
        restored = restore_history(duplicate, self.scratch(), self.graph.registry, objects)
        self.assertEqual(restored.commit(self.graph.main).tree, self.graph.t1)


class ArchiveInputTests(unittest.TestCase):
    def reject(self, code, function, *args, **kwargs):
        with self.assertRaises(HardeningError) as caught:
            function(*args, **kwargs)
        self.assertEqual(caught.exception.code, code, str(caught.exception))

    def test_arch_07_bundle_checksum_mismatch(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest = manifest_fixture(root)
            write_manifest(root, manifest)
            validate_manifest(root)
            (root / "history.bundle").write_bytes(b"changed bundle")
            self.reject("E_BUNDLE_HASH", validate_manifest, root)

    def test_arch_16_r_payload_external_hash(self):
        original = (capture_fixture_path() / "R-c10.zip").read_bytes()
        validate_r_bytes(original)
        changed = original[:-1] + bytes([original[-1] ^ 1])
        self.reject("E_EVIDENCE_HASH", validate_r_bytes, changed)

    def test_arch_17_repaired_hashes_fail_at_c10_content(self):
        root = Path(__file__).resolve().parents[3]
        source = capture_fixture_path() / "R-c10.zip"
        # Mutate only a disposable copy of actual original R bytes.
        with zipfile.ZipFile(source) as archive:
            payloads = {name: archive.read(name) for name in archive.namelist()}
        manifest = strict_json(payloads["evidence_manifest.json"])
        self.assertEqual(manifest["source"], R_SOURCE)
        with tempfile.TemporaryDirectory() as temporary:
            fixture = Path(temporary) / "fixture-source-context.zip"
            def write():
                with zipfile.ZipFile(fixture, "w", zipfile.ZIP_DEFLATED) as archive:
                    for name, value in payloads.items():
                        archive.writestr(name, value)
            write()
            self.assertFalse(validate_c10_content(fixture, root)["compiler_rerun"])
            payloads["C10ReifiedGolden.lean"] += b"\n-- altered proof input\n"
            manifest["artifacts"] = {name: digest(value) for name, value in payloads.items() if name != "evidence_manifest.json"}
            payloads["evidence_manifest.json"] = stable_json(manifest)
            write()
            self.reject("E_C10_CONTENT", validate_c10_content, fixture, root)

    def test_manifest_nested_declarations_cannot_be_repaired_into_promotion(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            approved = manifest_fixture(root)
            write_manifest(root, approved)
            validate_manifest(root)
            mutations = [lambda m: m["registry"].update(path="invented"),
                         lambda m: m["registry"].update(sha256="0" * 64),
                         lambda m: m["registry"].update(count=35),
                         lambda m: m["object_inventory"].update(path="invented"),
                         lambda m: m["object_inventory"].update(sha256="0" * 64),
                         lambda m: m.update(dependencies=None),
                         lambda m: m["reproduction_levels"].update(fresh_lean_execution=True),
                         lambda m: m["reproduction_levels"].update(publisher_authentication=True)]
            for index, mutate in enumerate(mutations):
                with self.subTest(mutation=index):
                    value = deepcopy(approved)
                    mutate(value)
                    write_manifest(root, value)
                    self.reject("E_MANIFEST_FORMAT", validate_manifest, root)

    def test_manifest_extra_payload_and_symlink_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            value = manifest_fixture(root)
            write_manifest(root, value)
            (root / "extra").write_bytes(b"extra")
            self.reject("E_MANIFEST_FORMAT", validate_manifest, root)

    def test_arch_15_wrong_r_capture_identity(self):
        metadata = {"id": R_IDENTITY["artifact_id"], "size_in_bytes": R_IDENTITY["size"],
                    "digest": "sha256:" + R_IDENTITY["sha256"],
                    "workflow_run": {"id": R_IDENTITY["run_id"], "head_sha": R_SOURCE["head_sha"]}}
        validate_r_identity(metadata)
        for field, replacement in (("id", 1), ("size_in_bytes", 1), ("digest", "sha256:" + "0" * 64)):
            with self.subTest(field=field):
                changed = deepcopy(metadata)
                changed[field] = replacement
                self.reject("E_CAPTURE_ID", validate_r_identity, changed)
        for field in ("id", "head_sha"):
            with self.subTest(field=field):
                changed = deepcopy(metadata)
                changed["workflow_run"][field] = 1 if field == "id" else "0" * 40
                self.reject("E_CAPTURE_ID", validate_r_identity, changed)

    def test_dotdot_scratch_overlap_rejected_before_creation(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            supplement = root / "supplement"
            supplement.mkdir()
            (root / "anchor").mkdir()
            scratch = root / "anchor" / ".." / "supplement" / "restore"
            self.assertEqual(scratch.resolve(), require_empty_scratch(scratch, create=False))
            with self.assertRaises(HardeningError) as caught:
                verify_supplement(supplement, scratch, require_isolation=False)
            self.assertEqual("E_MANIFEST_FORMAT", caught.exception.code)
            self.assertIn("separate trees", str(caught.exception))
            self.assertFalse((supplement / "restore").exists())
            alias = root / "anchor" / ".." / "supplement"
            with self.assertRaises(HardeningError) as caught:
                verify_supplement(alias, supplement / "restore", require_isolation=False)
            self.assertEqual("E_MANIFEST_FORMAT", caught.exception.code)
            self.assertFalse((supplement / "restore").exists())
    def test_arch_18_missing_final_code_review(self):
        from verification.archive.acquire_evidence import validate_evidence
        source = capture_fixture_path()
        validate_evidence(source)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "evidence"
            shutil.copytree(source, root)
            (root / "final-code-review-comment.json").unlink()
            index = strict_json((root / "acquisition-index.json").read_bytes())
            key = "entries" if "entries" in index else "records"
            index[key] = [row for row in index[key] if row["path"] != "final-code-review-comment.json"]
            (root / "acquisition-index.json").write_bytes(stable_json(index))
            with self.assertRaises(HardeningError) as caught:
                validate_evidence(root)
            self.assertEqual(caught.exception.code, "E_CAPTURE_ID")
            self.assertIn("final-code-review-comment.json", str(caught.exception))

    def test_final_job_log_omission_repaired_index_rejected(self):
        from verification.archive.acquire_evidence import validate_evidence
        source = capture_fixture_path()
        validate_evidence(source)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "evidence"
            shutil.copytree(source, root)
            log = next((root / "runs").glob("job-*-logs.json"))
            relative = log.relative_to(root).as_posix()
            log.unlink()
            index = strict_json((root / "acquisition-index.json").read_bytes())
            key = "entries" if "entries" in index else "records"
            index[key] = [row for row in index[key] if row["path"] != relative]
            (root / "acquisition-index.json").write_bytes(stable_json(index))
            self.reject("E_CAPTURE_ID", validate_evidence, root)

    def test_arch_19_unsafe_delivered_paths_and_duplicates(self):
        for path in ("../x", "/absolute", "a/../x", "a\\b", "a//b", "a/./b", "C:/x", "a\nx"):
            with self.subTest(path=path):
                self.reject("E_MANIFEST_FORMAT", safe_path, path)
        self.assertEqual(safe_path("ordinary/path.txt"), "ordinary/path.txt")
        self.reject("E_MANIFEST_FORMAT", strict_json, b'{"path":1,"path":2}')

    def test_arch_20_unavailable_isolation_blocks(self):
        with patch("verification.archive.offline_smoke.platform.system", return_value="Windows"):
            self.reject("E_OFFLINE_UNAVAILABLE", launch_offline, "irrelevant", "irrelevant")
        clean = sanitized_environment()
        with patch.dict(os.environ, {"HTTPS_PROXY": "secret", "GH_TOKEN": "secret", "PYTHONPATH": "injected"}):
            clean = sanitized_environment()
        self.assertNotIn("HTTPS_PROXY", clean)
        self.assertNotIn("GH_TOKEN", clean)
        self.assertNotIn("PYTHONPATH", clean)

    def test_arch_24_missing_offline_dependency_blocks(self):
        with patch("verification.archive.offline_smoke.importlib.metadata.version", side_effect=importlib.metadata.PackageNotFoundError):
            self.reject("E_DEPENDENCY_MISSING", require_dependencies)

    def test_arch_27_bounded_archive_metadata(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "large.json"
            with path.open("wb") as output:
                output.truncate(MAX_METADATA + 1)
            self.reject("E_LIMIT", read_bounded, path)
            objects = Path(temporary) / "objects.jsonl"
            objects.write_bytes(stable_json({"oid": "a" * 40, "type": "blob", "size": MAX_OBJECT + 1, "sha256": "b" * 64}).replace(b"\n", b"") + b"\n")
            self.reject("E_LIMIT", parse_objects, objects)
            root = Path(temporary) / "supplement"
            root.mkdir()
            value = manifest_fixture(root)
            next(row for row in value["files"] if row["path"] == "history.bundle")["size"] = MAX_BUNDLE + 1
            write_manifest(root, value)
            self.reject("E_LIMIT", validate_manifest, root)
        self.reject("E_LIMIT", strict_json, b" " * (MAX_METADATA + 1))

    def test_standalone_context_requires_actual_restore_before_pass(self):
        with tempfile.TemporaryDirectory() as temporary:
            previous = Path.cwd()
            try:
                os.chdir(temporary)
                with patch.dict(os.environ, {"GITHUB_ACTIONS": ""}):
                    self.assertIsNone(invocation_context())
                    self.reject("E_REFERENCE_MISSING", invocation_context, ".", None)
                with patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}):
                    self.reject("E_REFERENCE_MISSING", invocation_context)
            finally:
                os.chdir(previous)

    def test_foreign_repository_cannot_supply_local_context(self):
        from verification.integrity.tests._fixtures import GitFixture
        fixture = GitFixture()
        self.addCleanup(fixture.close)
        previous = Path.cwd()
        try:
            os.chdir(fixture.root)
            with patch.dict(os.environ, {"GITHUB_ACTIONS": ""}):
                self.assertIsNone(invocation_context())
                self.reject("E_REFERENCE_MISSING", invocation_context, ".", fixture.accepted)
        finally:
            os.chdir(previous)


class ArchiveIsolationTests(unittest.TestCase):
    def test_arch_21_real_linux_namespace(self):
        # This is intentionally BLOCKED on unsupported hosts. It is never a
        # mocked PASS or a skip that could satisfy a required CI suite.
        if platform.system() != "Linux" or os.getuid() == 0:
            raise HardeningError("E_OFFLINE_UNAVAILABLE", "ARCH-21 requires the supported nonroot Linux namespace runner", 3)
        parent = os.readlink("/proc/self/ns/net")
        source = str(Path(__file__).resolve().parents[3])
        code = ("import json,sys;sys.path.insert(0,sys.argv[1]);"
                "from verification.archive.offline_smoke import isolation_attestation;"
                "print(json.dumps(isolation_attestation(sys.argv[2])))")
        command = ["/usr/bin/sudo", "-n", "/usr/bin/unshare", "--net", "--", "/usr/bin/setpriv",
                   "--reuid=" + str(os.getuid()), "--regid=" + str(os.getgid()), "--clear-groups",
                   "--bounding-set=-all", "--inh-caps=-all", "--ambient-caps=-all", "--no-new-privs",
                   sys.executable, "-B", "-c", code, source, parent]
        done = subprocess.run(command, env=sanitized_environment(), capture_output=True, timeout=30)
        if done.returncode:
            raise HardeningError("E_OFFLINE_UNAVAILABLE", "ARCH-21 namespace launch blocked: " + done.stderr.decode("utf-8", "replace")[-2000:], 3)
        result = strict_json(done.stdout)
        self.assertEqual(result["network_isolation"], "ENFORCED")
        self.assertNotEqual(result["parent_network_namespace"], result["child_network_namespace"])


if __name__ == "__main__":
    unittest.main()
