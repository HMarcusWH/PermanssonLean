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
        # The fixed comments are historical content, not merely nonempty JSON.
        # Repair the acquisition index AND complete outer manifest so each
        # semantic pin must reject at E_CAPTURE_ID after the outer gate passes.
        for name in ("final-code-review-comment.json", "acceptance-comment.json"):
            for field in ("body", "body_surrogate", "author.id", "author.login",
                          "author.node_id", "author.type", "created_at", "updated_at",
                          "missing_created_at", "missing_updated_at", "node_id", "endpoint"):
                def mutate(root, name=name, field=field):
                    path = root / name
                    value = strict_json(path.read_bytes())
                    if field == "body":
                        # Preserve byte length: the independently pinned digest
                        # must detect this rather than only a size comparison.
                        value["body"] = ("!" if value["body"][0] != "!" else "?") + value["body"][1:]
                    elif field == "body_surrogate":
                        value["body"] += chr(0xD800)
                    elif field.startswith("author."):
                        key = field.partition(".")[2]
                        value["user"][key] = (value["user"][key] + 1 if key == "id"
                                              else value["user"][key] + "-altered")
                    elif field in ("created_at", "updated_at"):
                        value[field] = "2026-10-16T00:00:00Z"
                    elif field.startswith("missing_"):
                        value.pop(field[len("missing_"):])
                    elif field == "node_id":
                        value["node_id"] += "-altered"
                    else:
                        index_path = root / "acquisition-index.json"
                        index = strict_json(index_path.read_bytes())
                        key = "entries" if "entries" in index else "records"
                        next(row for row in index[key] if row["path"] == name)["endpoint"] = (
                            "https://api.github.com/repos/HMarcusWH/PermanssonLean/issues/comments/1")
                        index_path.write_bytes(stable_json(index))
                    path.write_bytes(stable_json(value))
                with self.subTest(comment=name, altered=field), tempfile.TemporaryDirectory() as temporary:
                    evidence = self.repaired_capture(temporary, mutate)
                    with self.assertRaises(HardeningError) as caught:
                        validate_evidence(evidence)
                    self.assertEqual("E_CAPTURE_ID", caught.exception.code)
                    self.assertIn("Fixed historical comment", str(caught.exception))
                    self.assertIn(name, str(caught.exception))

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
        from verification.archive import manifest as manifest_module
        # Real unknown empty files exceed the actual production count ceiling.
        # Their sizes are zero, so no size or aggregate guard masks this check.
        with self.subTest(attack="many_unknown_empty_files"), tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            value = manifest_fixture(root)
            write_manifest(root, value)
            validate_manifest(root)
            existing = len(list(root.iterdir()))
            for number in range(manifest_module.MAX_FILES + 1 - existing):
                (root / ("unknown-" + str(number) + ".txt")).write_bytes(b"")
            with patch("verification.archive.manifest.file_record", side_effect=AssertionError("hash before count bound")) as hashed:
                self.reject("E_LIMIT", validate_manifest, root)
                hashed.assert_not_called()
        # A private tiny aggregate budget avoids allocating hundreds of MiB;
        # every real fixture payload is individually valid and ordinary UTF-8.
        with self.subTest(attack="aggregate_small_files"), tempfile.TemporaryDirectory() as temporary, \
             patch("verification.archive.manifest.MAX_TOTAL_BYTES", 12):
            root = Path(temporary)
            (root / "a.txt").write_bytes(b"abcdef")
            (root / "b.txt").write_bytes(b"ghijkl")
            self.assertEqual(12, sum(row["size"] for row in scan_files(root)))
            (root / "c.txt").write_bytes(b"m")
            with patch("verification.archive.manifest.file_record", side_effect=AssertionError("hash before aggregate bound")) as hashed:
                self.reject("E_LIMIT", scan_files, root)
                hashed.assert_not_called()
        with self.subTest(attack="many_empty_directories"), tempfile.TemporaryDirectory() as temporary, \
             patch("verification.archive.manifest.MAX_DIRECTORIES", 3):
            root = Path(temporary)
            for number in range(4):
                (root / str(number)).mkdir()
            with patch("verification.archive.manifest.file_record", side_effect=AssertionError("hash before directory bound")) as hashed:
                self.reject("E_LIMIT", scan_files, root)
                hashed.assert_not_called()
        with self.subTest(attack="directory_depth"), tempfile.TemporaryDirectory() as temporary, \
             patch("verification.archive.manifest.MAX_DIRECTORY_DEPTH", 2):
            root = Path(temporary)
            (root / "a/b/c").mkdir(parents=True)
            self.reject("E_LIMIT", scan_files, root)
        with self.subTest(attack="declared_count_before_scan"), tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            value = manifest_fixture(root)
            value["files"] = [{"path": "unknown-" + str(i), "size": 0, "sha256": "a" * 64}
                              for i in range(manifest_module.MAX_FILES + 1)]
            write_manifest(root, value)
            with patch("verification.archive.manifest.scan_files", side_effect=AssertionError("scan before declared count bound")):
                self.reject("E_LIMIT", validate_manifest, root)
        with self.subTest(attack="declared_aggregate_before_scan"), tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            value = manifest_fixture(root)
            for row, size in zip(value["files"], (6, 6, 1)):
                row["size"] = size
            write_manifest(root, value)
            with patch("verification.archive.manifest.MAX_TOTAL_BYTES", 12), \
                 patch("verification.archive.manifest.scan_files", side_effect=AssertionError("scan before declared aggregate bound")):
                self.reject("E_LIMIT", validate_manifest, root)
        # Reparse metadata is exercised explicitly rather than claiming that a
        # mocked directory entry is a real Windows junction execution.
        from types import SimpleNamespace
        with self.subTest(attack="Windows_reparse_directory_metadata"), tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            metadata = SimpleNamespace(st_mode=__import__("stat").S_IFDIR, st_file_attributes=0x400)
            entry = SimpleNamespace(path=str(root / "junction"), stat=lambda **kwargs: metadata)
            with patch("verification.archive.manifest.os.scandir") as scanned:
                scanned.return_value.__enter__.return_value = [entry]
                self.reject("E_MANIFEST_FORMAT", scan_files, root)

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


class GuideClosureTests(unittest.TestCase):
    def test_guide_closure_canonical_and_standalone(self):
        """Repaired outer hashes must not hide drift from canonical T/C guides."""
        from verification.archive.create_bundle import GUIDE_PATH, _snapshot_tooling
        from verification.archive.verify_bundle import require_source_pair, validate_tooling
        from verification.integrity.tests._fixtures import GitFixture
        from verification.archive import offline_smoke, _offline_worker

        original = GitRepo(Path(__file__).resolve().parents[3])
        try:
            head = original.run("rev-parse", "HEAD").decode().strip()
            guide = original.blob(original.tree(head)[GUIDE_PATH.encode()].oid)
        finally:
            original.close()
        fixture = GitFixture()
        self.addCleanup(fixture.close)
        code = {b"verification/archive/verify_bundle.py": b"# fixture archive code\n",
                b"verification/integrity/__init__.py": b"# fixture integrity code\n"}
        changes = {path: ("100644", payload) for path, payload in code.items()}
        changes[GUIDE_PATH.encode()] = ("100644", guide)
        tooling_commit = fixture.commit(changes)
        fixture.repo.run("update-ref", "refs/heads/main", tooling_commit)
        for name, (_, payload) in changes.items():
            target = fixture.root / name.decode()
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)

        def reject(code, function, *args, **kwargs):
            with self.assertRaises(HardeningError) as caught:
                function(*args, **kwargs)
            self.assertEqual(code, caught.exception.code, str(caught.exception))

        with tempfile.TemporaryDirectory(prefix="permansson-guide-") as temporary:
            supplement = Path(temporary) / "supplement"
            supplement.mkdir()
            rows = _snapshot_tooling(fixture.repo, tooling_commit, supplement)
            manifest = manifest_fixture(supplement)
            manifest["tooling"] = {"source_commit": tooling_commit, "files": rows}

            def repair(value):
                value["files"] = scan_files(supplement)
                write_manifest(supplement, value)
                return validate_manifest(supplement)  # outer PASS precedes every semantic attack

            manifest = repair(manifest)
            bound = {"source_repo": fixture.root, "source_candidate": tooling_commit}
            source_file = fixture.root / "verification/archive/verify_bundle.py"
            with patch("verification.archive.verify_bundle.__file__", str(source_file)), \
                 patch("verification.archive.verify_bundle.ACCEPTED", fixture.accepted), \
                 patch("verification.archive.verify_bundle.ACCEPTED_TREE", fixture.repo.commit(fixture.accepted).tree):
                with self.subTest(control="canonical_original_guide"):
                    self.assertEqual(guide, (supplement / "OFFLINE_REPRODUCTION.md").read_bytes())
                    result = validate_tooling(supplement, manifest, **bound)
                    self.assertEqual("canonical_T_C_and_executing_code", result["binding"])
                    self.assertEqual(3, result["files"])
                    self.assertTrue(result["reproduction_instructions_match"])
                with self.subTest(control="checkout_CRLF_is_not_canonical_drift"):
                    (fixture.root / GUIDE_PATH).write_bytes(guide.replace(b"\n", b"\r\n"))
                    self.assertEqual(result, validate_tooling(supplement, manifest, **bound))
                    (fixture.root / GUIDE_PATH).write_bytes(guide)
                with self.subTest(attack="committed_guide_changes_after_packaging"):
                    candidate = fixture.commit({GUIDE_PATH.encode(): ("100644", guide + b"\nChanged guide.\n")},
                                               parent=tooling_commit)
                    fixture.repo.run("update-ref", "refs/heads/main", candidate)
                    validate_manifest(supplement)
                    reject("E_TOOLING_CLOSURE", validate_tooling, supplement, manifest,
                           source_repo=fixture.root, source_candidate=candidate)
                    fixture.repo.run("update-ref", "refs/heads/main", tooling_commit)
                with self.subTest(attack="repaired_outer_instructions_only"):
                    (supplement / "OFFLINE_REPRODUCTION.md").write_bytes(guide + b"\nChanged instructions.\n")
                    altered = repair(deepcopy(manifest))
                    reject("E_TOOLING_CLOSURE", validate_tooling, supplement, altered, **bound)
                    (supplement / "OFFLINE_REPRODUCTION.md").write_bytes(guide)
                with self.subTest(attack="repaired_snapshot_and_instructions_and_blob"):
                    payload = guide + b"\nSelf-consistent altered guide.\n"
                    (supplement / "OFFLINE_REPRODUCTION.md").write_bytes(payload)
                    (supplement / "tooling" / GUIDE_PATH).write_bytes(payload)
                    altered = deepcopy(manifest)
                    row = next(row for row in altered["tooling"]["files"] if row["path"] == GUIDE_PATH)
                    row.update(sha256=digest(payload), blob=fixture.blob(payload))
                    altered = repair(altered)
                    reject("E_TOOLING_CLOSURE", validate_tooling, supplement, altered, **bound)
                    (supplement / "OFFLINE_REPRODUCTION.md").write_bytes(guide)
                    (supplement / "tooling" / GUIDE_PATH).write_bytes(guide)
                    manifest = repair(manifest)
                with self.subTest(attack="T_file_omitted_from_C_snapshot_and_executing_code"):
                    path = b"verification/integrity/__init__.py"
                    candidate = fixture.commit({path: None}, parent=tooling_commit)
                    fixture.repo.run("update-ref", "refs/heads/main", candidate)
                    (fixture.root / path.decode()).unlink()
                    (supplement / "tooling" / path.decode()).unlink()
                    altered = deepcopy(manifest)
                    altered["tooling"]["files"] = [row for row in altered["tooling"]["files"] if row["path"] != path.decode()]
                    altered = repair(altered)
                    reject("E_TOOLING_CLOSURE", validate_tooling, supplement, altered,
                           source_repo=fixture.root, source_candidate=candidate)
                    fixture.repo.run("update-ref", "refs/heads/main", tooling_commit)
                    (fixture.root / path.decode()).write_bytes(code[path])
                    (supplement / "tooling" / path.decode()).write_bytes(code[path])
                    manifest = repair(manifest)

            delivered_source = supplement / "tooling/verification/archive/verify_bundle.py"
            with patch("verification.archive.verify_bundle.__file__", str(delivered_source)):
                with self.subTest(control="standalone_delivered_guide_no_git_autodiscovery"), \
                     patch("verification.archive.verify_bundle.GitRepo", side_effect=AssertionError("unexpected Git autodiscovery")):
                    result = validate_tooling(supplement, manifest)
                    self.assertEqual("standalone_content_hashes_only", result["binding"])
                    self.assertIsNone(result["source_candidate"])
                with self.subTest(attack="standalone_unapproved_guide_hash"):
                    (supplement / "tooling" / GUIDE_PATH).write_bytes(guide + b"\nUnapproved.\n")
                    (supplement / "OFFLINE_REPRODUCTION.md").write_bytes(guide + b"\nUnapproved.\n")
                    altered = repair(deepcopy(manifest))
                    reject("E_TOOLING_CLOSURE", validate_tooling, supplement, altered)
                    (supplement / "tooling" / GUIDE_PATH).write_bytes(guide)
                    (supplement / "OFFLINE_REPRODUCTION.md").write_bytes(guide)
                    manifest = repair(manifest)
                with self.subTest(attack="guide_omitted_from_declared_closure"):
                    altered = deepcopy(manifest)
                    altered["tooling"]["files"] = [row for row in altered["tooling"]["files"] if row["path"] != GUIDE_PATH]
                    altered = repair(altered)
                    reject("E_TOOLING_CLOSURE", validate_tooling, supplement, altered)

        for source_repo, candidate in ((fixture.root, None), (None, tooling_commit), (fixture.root, "short")):
            with self.subTest(attack="incomplete_binding", source_repo=str(source_repo), candidate=candidate):
                reject("E_CONTEXT", require_source_pair, source_repo, candidate)
                reject("E_CONTEXT", launch_offline, "unused", "unused", source_repo=source_repo, source_candidate=candidate)

        # These are argument-plumbing controls, not claims of namespace execution.
        flags = ["--supplement", "unused", "--scratch", "unused", "--report", "unused.json"]
        payload = {"status": "PASS"}
        with self.subTest(control="bound_parent_propagates_checked_pair"), \
             patch.object(offline_smoke, "invocation_context", return_value=object()) as context, \
             patch.object(offline_smoke, "launch_offline", return_value={"completed_stages": []}) as launch, \
             patch.object(offline_smoke, "check_report", return_value=payload), \
             patch.object(offline_smoke, "write_report"):
            self.assertEqual(0, offline_smoke.main(flags + ["--repo", str(fixture.root), "--candidate", tooling_commit]))
            context.assert_called_once_with(str(fixture.root), tooling_commit)
            launch.assert_called_once_with("unused", "unused", source_repo=str(fixture.root), source_candidate=tooling_commit)
        with self.subTest(control="standalone_parent_does_not_discover_repository"), \
             patch.dict(os.environ, {"GITHUB_ACTIONS": ""}), \
             patch.object(offline_smoke, "invocation_context", side_effect=AssertionError("unexpected context autodiscovery")), \
             patch.object(offline_smoke, "restored_artifact_context", return_value=object()) as restored, \
             patch.object(offline_smoke, "launch_offline", return_value={"completed_stages": []}) as launch, \
             patch.object(offline_smoke, "check_report", return_value=payload), \
             patch.object(offline_smoke, "write_report"):
            self.assertEqual(0, offline_smoke.main(flags))
            launch.assert_called_once_with("unused", "unused", source_repo=None, source_candidate=None)
            restored.assert_called_once_with("unused")
        with self.subTest(control="privilege_dropped_worker_receives_pair"), \
             patch.object(_offline_worker, "isolation_attestation", return_value={}), \
             patch.object(_offline_worker, "verify_supplement", return_value={"completed_stages": []}) as verify, \
             patch.object(_offline_worker, "check_report", return_value=payload), \
             patch.object(_offline_worker, "write_report"), patch.dict(os.environ):
            self.assertEqual(0, _offline_worker.main(flags + ["--parent-netns", "net:[fixture]", "--source-repo", str(fixture.root),
                                                           "--source-candidate", tooling_commit]))
            verify.assert_called_once_with("unused", "unused", require_isolation=True,
                                           source_repo=str(fixture.root), source_candidate=tooling_commit)


class PublicationTests(unittest.TestCase):
    def test_committed_publication_matches_verified_inner_objects(self):
        from io import BytesIO
        import stat
        import struct
        import zlib
        from verification.archive.create_bundle import GUIDE_PATH, _snapshot_tooling
        from verification.archive.publication import (SUPPLEMENT_PREFIX, ZIP_PATH, FIXED_TIME,
                                                       validate_committed_publication)
        from verification.archive.verify_bundle import validate_tooling
        from verification.integrity.tests._fixtures import GitFixture

        fixture = GitFixture()
        self.addCleanup(fixture.close)
        code = {b"verification/archive/verify_bundle.py": b"# fixture publication source\n",
                b"verification/integrity/__init__.py": b"# fixture integrity source\n",
                GUIDE_PATH.encode(): b"Canonical fixture guide\n"}
        source = fixture.commit({path: ("100644", value) for path, value in code.items()})
        for path, content in code.items():
            target = fixture.root / path.decode()
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)

        def zip_bytes(contents, *, symlink=False, duplicate=False):
            buffer = BytesIO()
            with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED) as archive:
                for i, (name, content) in enumerate(sorted(contents.items())):
                    info = zipfile.ZipInfo(name, FIXED_TIME)
                    info.create_system = 3
                    info.compress_type = zipfile.ZIP_DEFLATED
                    info.external_attr = ((stat.S_IFLNK | 0o777) if symlink and i == 0 else (stat.S_IFREG | 0o644)) << 16
                    archive.writestr(info, content)
                if duplicate:
                    # A second central-directory member cannot be hidden by
                    # repairing the publisher checksum.
                    info = zipfile.ZipInfo(next(iter(sorted(contents))), FIXED_TIME)
                    info.create_system = 3
                    info.external_attr = (stat.S_IFREG | 0o644) << 16
                    with __import__("warnings").catch_warnings():
                        __import__("warnings").simplefilter("ignore", UserWarning)
                        archive.writestr(info, contents[info.filename])
            return buffer.getvalue()

        def reject(function, *args, **kwargs):
            with self.assertRaises(HardeningError) as caught:
                function(*args, **kwargs)
            self.assertEqual("E_PUBLICATION_INTEGRITY", caught.exception.code, str(caught.exception))
            return caught.exception

        with tempfile.TemporaryDirectory(prefix="permansson-publication-") as temporary:
            supplement = Path(temporary) / "supplement"
            supplement.mkdir()
            tooling = _snapshot_tooling(fixture.repo, source, supplement)
            manifest = manifest_fixture(supplement)
            manifest["tooling"] = {"source_commit": source, "files": tooling}
            write_manifest(supplement, manifest)
            validate_manifest(supplement)
            contents = {path.relative_to(supplement).as_posix(): path.read_bytes()
                        for path in supplement.rglob("*") if path.is_file()}
            good_zip = zip_bytes(contents)

            def publish(payload, *, parent=source, extras=None):
                changes = {SUPPLEMENT_PREFIX.encode() + name.encode(): ("100644", value)
                           for name, value in contents.items()}
                changes[ZIP_PATH.encode()] = ("100644", payload)
                changes[(ZIP_PATH + ".sha256").encode()] = (
                    "100644", (digest(payload) + "  " + Path(ZIP_PATH).name + "\n").encode())
                changes.update(extras or {})
                candidate = fixture.commit(changes, parent=parent)
                fixture.repo.run("update-ref", "refs/heads/main", candidate)
                return candidate

            accepted_tree = fixture.repo.commit(fixture.accepted).tree
            with patch("verification.archive.verify_bundle.__file__", str(fixture.root / "verification/archive/verify_bundle.py")), \
                 patch("verification.archive.verify_bundle.ACCEPTED", fixture.accepted), \
                 patch("verification.archive.verify_bundle.ACCEPTED_TREE", accepted_tree), \
                 patch("verification.archive.publication.ACCEPTED", fixture.accepted), \
                 patch("verification.archive.publication.ACCEPTED_TREE", accepted_tree):
                def prior_stages(candidate, current_manifest=manifest):
                    self.assertEqual(current_manifest, validate_manifest(supplement))
                    validate_tooling(supplement, current_manifest,
                                     source_repo=fixture.root, source_candidate=candidate)

                with self.subTest(control="canonical_C_positive"):
                    candidate = publish(good_zip)
                    prior_stages(candidate)
                    result = validate_committed_publication(fixture.repo, candidate, supplement, manifest)
                    self.assertEqual("PASS", result["status"])
                    self.assertEqual(len(contents), result["members"])
                    self.assertTrue(result["verified_filesystem_matches_C"])

                altered_contents = {**contents, "history.bundle": b"!" + contents["history.bundle"][1:]}
                attacks = {"stale_payload_repaired_sidecar": zip_bytes(altered_contents),
                           "unsafe_member": zip_bytes({("../" + name if i == 0 else name): value
                                                       for i, (name, value) in enumerate(sorted(contents.items()))}),
                           "symlink_member": zip_bytes(contents, symlink=True),
                           "duplicate_member": zip_bytes(contents, duplicate=True)}
                encrypted, bomb = bytearray(good_zip), bytearray(good_zip)
                central = good_zip.index(b"PK\x01\x02")
                struct.pack_into("<H", encrypted, 6, 1)
                struct.pack_into("<H", encrypted, central + 8, 1)
                struct.pack_into("<L", bomb, central + 24, MAX_BUNDLE + 1)
                attacks.update(encrypted_member=bytes(encrypted), declared_size_bomb=bytes(bomb))
                concealed = bytearray(attacks["duplicate_member"])
                struct.pack_into("<2H", concealed, len(concealed) - 22 + 8, len(contents), len(contents))
                attacks["concealed_duplicate_count"] = bytes(concealed)
                corrupted = bytearray(good_zip)
                name_size, extra_size = struct.unpack_from("<2H", corrupted, 26)
                corrupted[30 + name_size + extra_size] = 7  # reserved raw-DEFLATE block type
                attacks["corrupt_deflate_stream"] = bytes(corrupted)
                for name, payload in attacks.items():
                    with self.subTest(attack=name):
                        candidate = publish(payload)  # both ZIP and publisher sidecar repaired in C
                        prior_stages(candidate)
                        if name == "concealed_duplicate_count":
                            with patch("verification.archive.publication.zipfile.ZipFile", side_effect=AssertionError("unbounded parser invoked")):
                                reject(validate_committed_publication, fixture.repo, candidate, supplement, manifest)
                        else:
                            error = reject(validate_committed_publication, fixture.repo, candidate, supplement, manifest)
                            if name == "corrupt_deflate_stream":
                                self.assertIsInstance(error.__cause__, zlib.error)

                with self.subTest(attack="canonical_extra_inner_path"):
                    candidate = publish(good_zip, extras={(SUPPLEMENT_PREFIX + "extra.txt").encode(): ("100644", b"extra")})
                    prior_stages(candidate)
                    reject(validate_committed_publication, fixture.repo, candidate, supplement, manifest)
                with self.subTest(attack="filesystem_cannot_define_publication_authority"):
                    candidate = publish(good_zip)
                    (supplement / "history.bundle").write_bytes(b"altered filesystem fixture")
                    altered = deepcopy(manifest)
                    altered["files"] = scan_files(supplement)
                    row = next(row for row in altered["files"] if row["path"] == "history.bundle")
                    altered["bundle"].update(size=row["size"], sha256=row["sha256"])
                    write_manifest(supplement, altered)
                    prior_stages(candidate, altered)
                    reject(validate_committed_publication, fixture.repo, candidate, supplement, altered)


if __name__ == "__main__":
    unittest.main()
