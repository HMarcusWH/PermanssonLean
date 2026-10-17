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
        if ((path / "R-c10.zip").is_file()
                and (path / "thread-comment-pages/1.json").is_file()
                and ((path / "thread-pages/1.json").is_file()
                     or (path / "pagination/threads-1.json").is_file())):
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

    def repaired_capture(self, temporary, mutate):
        """Repair both outer inventory and inner capture hashes before semantics."""
        source = Path(__file__).resolve().parents[3] / "archival/v0.2.0/supplement-1"
        root = Path(temporary) / "supplement"
        shutil.copytree(source, root)
        shutil.copytree(capture_fixture_path(), root / "evidence", dirs_exist_ok=True)
        evidence = root / "evidence"
        from verification.archive.acquire_evidence import validate_evidence
        validate_evidence(evidence)
        mutate(evidence)
        index = strict_json((evidence / "acquisition-index.json").read_bytes())
        key = "entries" if "entries" in index else "records"
        records = {row["path"]: row for row in index[key]}
        actual = {p.relative_to(evidence).as_posix(): p for p in evidence.rglob("*")
                  if p.is_file() and p.name != "acquisition-index.json"}
        rows = []
        for name, path in sorted(actual.items()):
            match = __import__("re").fullmatch(r"runs/job-([0-9]+)-logs\.txt", name)
            endpoint = ("https://api.github.com/repos/HMarcusWH/PermanssonLean/actions/jobs/" + match.group(1) + "/logs"
                        if match else "https://api.github.com/repos/HMarcusWH/PermanssonLean/actions/runs/39045919531/logs")
            row = records.get(name, {"path": name, "endpoint": endpoint,
                                     "representation": "raw_http", "acquired_on": "2026-10-17"})
            payload = path.read_bytes()
            row.update(size=len(payload), sha256=digest(payload))
            rows.append(row)
        index[key] = rows
        (evidence / "acquisition-index.json").write_bytes(stable_json(index))
        manifest = strict_json((root / "archive-manifest.json").read_bytes())
        manifest["files"] = scan_files(root)
        write_manifest(root, manifest)
        validate_manifest(root)  # Hashes and complete delivered inventory pass.
        return evidence

    def test_review_normalization_is_bound_to_source_pages(self):
        from verification.archive.acquire_evidence import validate_evidence
        def rewrite(path, change):
            def mutate(root):
                target = root / path
                value = strict_json(target.read_bytes())
                replacement = change(value)
                target.write_bytes(stable_json(value if replacement is None else replacement))
            return mutate
        mutations = {
            "empty_review_list": rewrite("final-review-submissions.json", lambda value: []),
            "drop_review": rewrite("final-review-submissions.json", lambda value: value[:-1]),
            "empty_thread_list": rewrite("review-threads.json", lambda value: value.update(review_threads=[])),
            "alter_thread_body": rewrite("review-threads.json", lambda value: value["review_threads"][0]["comments"][0].update(body="erased finding")),
            "wrong_review_pr": rewrite("review-pages/1.json", lambda value: value[0].update(pull_request_url="https://api.github.com/repos/HMarcusWH/PermanssonLean/pulls/77")),
            "wrong_comment_pr": rewrite("thread-comment-pages/1.json", lambda value: value[0].update(pull_request_url="https://api.github.com/repos/HMarcusWH/PermanssonLean/pulls/77")),
            "missing_terminal_comments": lambda root: (root / "thread-comment-pages/2.json").unlink(),
            "erase_rest_comments": rewrite("thread-comment-pages/1.json", lambda value: []),
            "wrong_connector_pr": rewrite("thread-pages/1.json", lambda value: value["request"].update(pr_number=77)),
            "connector_error_envelope": rewrite("thread-pages/1.json", lambda value: value["result"].update(isError=True)),
        }
        # Deleting an optional empty completion probe after a short page is
        # still complete; instead make page1 full before removing page2 below.
        def truncate_comments(root):
            path = root / "thread-comment-pages/1.json"
            value = strict_json(path.read_bytes())
            path.write_bytes(stable_json((value * 8)[:100]))
            (root / "thread-comment-pages/2.json").unlink()
        mutations["missing_terminal_comments"] = truncate_comments
        def wrong_review_pr(root):
            for name in ("review-pages/1.json", "final-review-submissions.json"):
                path = root / name
                value = strict_json(path.read_bytes())
                value[0]["pull_request_url"] = "https://api.github.com/repos/HMarcusWH/PermanssonLean/pulls/77"
                path.write_bytes(stable_json(value))
        mutations["wrong_review_pr"] = wrong_review_pr
        def omit_thread_from_both(root):
            path = root / "thread-pages/1.json"
            value = strict_json(path.read_bytes())
            value["result"]["structuredContent"]["review_threads"].pop()
            path.write_bytes(stable_json(value))
            path = root / "review-threads.json"
            value = strict_json(path.read_bytes())
            value["review_threads"].pop()
            path.write_bytes(stable_json(value))
        mutations["omit_thread_from_both_sources"] = omit_thread_from_both
        def remove_connector_result_status(value):
            value["result"].pop("isError")
        mutations["missing_connector_result_status"] = rewrite("thread-pages/1.json", remove_connector_result_status)
        def edit_both_thread_sources(root, change):
            for name in ("thread-pages/1.json", "review-threads.json"):
                path = root / name
                value = strict_json(path.read_bytes())
                threads = (value["review_threads"] if name == "review-threads.json"
                           else value["result"]["structuredContent"]["review_threads"])
                for thread in threads:
                    for comment in thread["comments"]:
                        change(comment)
                path.write_bytes(stable_json(value))
        def remove_timestamps(comment):
            for key in ("created_at", "updated_at", "createdAt", "updatedAt"):
                comment.pop(key, None)
        mutations["erase_timestamps_from_both_thread_sources"] = lambda root: edit_both_thread_sources(root, remove_timestamps)
        for field in ("created_at", "updated_at"):
            mutations["erase_" + field] = lambda root, field=field: edit_both_thread_sources(root, lambda comment: comment.pop(field))
        mutations["conflicting_timestamp_alias"] = lambda root: edit_both_thread_sources(root, lambda comment: comment.update(createdAt="2026-10-16T00:00:00Z"))
        def erase_review_sources(root):
            for name in ("review-pages/1.json", "final-review-submissions.json"):
                (root / name).write_bytes(stable_json([]))
        mutations["erase_both_review_submission_sources"] = erase_review_sources
        mutations["unknown_comment_review_id"] = rewrite("thread-comment-pages/1.json", lambda value: value[0].update(pull_request_review_id=1))
        mutations["boolean_comment_review_id"] = rewrite("thread-comment-pages/1.json", lambda value: value[0].update(pull_request_review_id=True))
        def remove_rest_created(value):
            value[0].pop("created_at")
        mutations["missing_rest_created_timestamp"] = rewrite("thread-comment-pages/1.json", remove_rest_created)
        mutations["invalid_rest_updated_timestamp"] = rewrite("thread-comment-pages/1.json", lambda value: value[0].update(updated_at="2026-99-99T99:99:99Z"))
        def graphql_names(comment):
            comment["createdAt"] = comment.pop("created_at")
            comment["updatedAt"] = comment.pop("updated_at")
        with self.subTest(control="native_graphql_timestamp_names"), tempfile.TemporaryDirectory() as temporary:
            evidence = self.repaired_capture(temporary, lambda root: edit_both_thread_sources(root, graphql_names))
            validate_evidence(evidence)
        for name, mutate in mutations.items():
            with self.subTest(attack=name), tempfile.TemporaryDirectory() as temporary:
                evidence = self.repaired_capture(temporary, mutate)
                self.reject("E_CAPTURE_ID", validate_evidence, evidence)

    def test_unparsed_run_zip_cannot_replace_per_job_logs(self):
        from verification.archive.acquire_evidence import validate_evidence
        def mutate(root):
            job = strict_json((root / "runs/39045919531-jobs.json").read_bytes())["jobs"][0]
            (root / "runs" / ("job-" + str(job["id"]) + "-logs.json")).unlink()
            (root / "runs/39045919531-logs.zip").write_bytes(b"not a ZIP; mere existence is insufficient")
        with tempfile.TemporaryDirectory() as temporary:
            evidence = self.repaired_capture(temporary, mutate)
            self.reject("E_CAPTURE_ID", validate_evidence, evidence)
        def raw_log(root, payload=None):
            job = strict_json((root / "runs/39045919531-jobs.json").read_bytes())["jobs"][0]
            source = root / "runs" / ("job-" + str(job["id"]) + "-logs.json")
            captured = strict_json(source.read_bytes())
            content = captured["result"]["structuredContent"]["content"].encode("utf-8")
            source.unlink()
            (root / "runs" / ("job-" + str(job["id"]) + "-logs.txt")).write_bytes(content if payload is None else payload)
        for control, payload in (("timestamped_actual_raw_text", None),
                                 ("valid_bom_and_seven_fractional_digits", "\ufeff2026-10-17T15:38:14.1234567Z valid format fixture\n".encode("utf-8"))):
            with self.subTest(control=control), tempfile.TemporaryDirectory() as temporary:
                evidence = self.repaired_capture(temporary, lambda root: raw_log(root, payload))
                validate_evidence(evidence)
        for attack, payload in (("binary_zip_in_raw_path", b"PK\x03\x04\0corrupt ZIP"),
                                ("invalid_utf8_raw_log", b"\xff\xfe"), ("empty_raw_log", b""),
                                ("invalid_calendar_timestamp", b"2026-99-99T99:99:99Z fake log\n"),
                                ("invalid_nonleap_day", b"2026-02-29T15:38:14.1234567Z fake log\n"),
                                ("invalid_zero_year", b"0000-10-17T15:38:14Z fake log\n")):
            with self.subTest(attack=attack), tempfile.TemporaryDirectory() as temporary:
                evidence = self.repaired_capture(temporary, lambda root: raw_log(root, payload))
                self.reject("E_CAPTURE_ID", validate_evidence, evidence)
        def wrong_endpoint(root):
            job = strict_json((root / "runs/39045919531-jobs.json").read_bytes())["jobs"][0]
            index_path = root / "acquisition-index.json"
            index = strict_json(index_path.read_bytes())
            key = "entries" if "entries" in index else "records"
            row = next(row for row in index[key] if row["path"] == "runs/job-" + str(job["id"]) + "-logs.json")
            row["endpoint"] = "https://api.github.com/repos/HMarcusWH/PermanssonLean/actions/jobs/1/logs"
            index_path.write_bytes(stable_json(index))
        with self.subTest(attack="wrong_job_endpoint"), tempfile.TemporaryDirectory() as temporary:
            evidence = self.repaired_capture(temporary, wrong_endpoint)
            self.reject("E_CAPTURE_ID", validate_evidence, evidence)
        def invalid_normalized_utf8(root):
            job = strict_json((root / "runs/39045919531-jobs.json").read_bytes())["jobs"][0]
            path = root / "runs" / ("job-" + str(job["id"]) + "-logs.json")
            value = strict_json(path.read_bytes())
            value["result"]["structuredContent"]["content"] = "2026-10-17T15:38:14Z " + chr(0xD800)
            path.write_bytes(stable_json(value))
        with self.subTest(attack="unpaired_surrogate_in_normalized_log"), tempfile.TemporaryDirectory() as temporary:
            evidence = self.repaired_capture(temporary, invalid_normalized_utf8)
            self.reject("E_CAPTURE_ID", validate_evidence, evidence)

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
