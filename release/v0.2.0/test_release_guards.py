"""Independent release guards on disposable copies with repaired bookkeeping.

These controls exercise final-mode verification, not a mocked acceptance gate.
Only Git's current-HEAD tree is injected to model an unpreserved release PR.
Captured publisher/compile receipts retain their documented offline trust; no
test authenticates GitHub or reruns Lean. Source and export bytes stay untouched.
"""
import contextlib
from functools import lru_cache
import hashlib
import io
import json
from pathlib import Path
import shutil
import struct
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import package_release as packager
import verify_release as verifier

KIT = Path(__file__).resolve().parent
ROOT = KIT.parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def mutate_json(kit, name, mutate):
    value = json.loads((kit / name).read_bytes())
    mutate(value)
    (kit / name).write_bytes(encoded(value))


def rehash_inventory(kit):
    """Give each adversary valid ordinary bookkeeping, not an early hash error."""
    manifest = json.loads((kit / "manifest.json").read_bytes())
    manifest["artifact_files"] = {
        path.relative_to(kit).as_posix(): digest(path.read_bytes())
        for path in kit.rglob("*")
        if path.is_file() and path != kit / "manifest.json"
        and not any(part in {"tmp", "__pycache__"} for part in path.relative_to(kit).parts)
    }
    manifest["manuscript_sha256"] = digest((kit / "manuscript.json").read_bytes())
    manifest["acceptance_evidence_sha256"] = digest((kit / "acceptance-evidence.json").read_bytes())
    (kit / "manifest.json").write_bytes(encoded(manifest))


def claims(data):
    return [claim for section in data["sections"] for claim in section.get("claims", [])]


def inner_json(payloads, name, mutate):
    value = json.loads(payloads[name])
    mutate(value)
    payloads[name] = encoded(value)


def rehashed_c10(kit, mutate):
    origins_path = kit / "evidence/c10/artifact-origins.json"
    origins = json.loads(origins_path.read_bytes())
    origin = next(item for item in origins["artifacts"] if item["anchor"] == "X1")
    archive = kit / origin["path"]
    with zipfile.ZipFile(archive) as zipped:
        payloads = {name: zipped.read(name) for name in zipped.namelist()}
    mutate(payloads)
    manifest = json.loads(payloads["evidence_manifest.json"])
    manifest["artifacts"] = {name: digest(data) for name, data in payloads.items()
                             if name != "evidence_manifest.json"}
    payloads["evidence_manifest.json"] = encoded(manifest)
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as zipped:
        for name, data in payloads.items():
            zipped.writestr(name, data)
    origin["sha256"] = digest(archive.read_bytes())
    origins_path.write_bytes(encoded(origins))


class C10ArchivePreflightTests(unittest.TestCase):
    def test_outer_gate_rejects_size_and_inventory_before_first_content_read(self):
        from c10_archive_validation import preflight_c10_zip, validate_c10_archive

        evidence = json.loads((KIT / "acceptance-evidence.json").read_bytes())
        original_archives = {path: digest(path.read_bytes())
                             for path in (KIT / "evidence/c10").glob("*.zip")}
        # Positive control uses the same final-mode outer entry point.
        verifier.validate_c10_archives(KIT, ROOT, evidence, False)

        def declared_sizes(archive, sizes):
            # Only a small fixture's central-directory declarations change.
            # No inflated payload is allocated, compressed or decompressed.
            payload = bytearray(archive.read_bytes())
            with zipfile.ZipFile(archive) as zipped:
                offset, entries = zipped.start_dir, zipped.infolist()
            for entry in entries:
                self.assertEqual(payload[offset:offset + 4], b"PK\x01\x02")
                name_length, extra_length, comment_length = struct.unpack_from("<HHH", payload, offset + 28)
                if entry.filename in sizes:
                    struct.pack_into("<I", payload, offset + 24, sizes[entry.filename])
                offset += 46 + name_length + extra_length + comment_length
            archive.write_bytes(payload)

        def replace_inventory(archive, duplicate=False):
            with zipfile.ZipFile(archive) as zipped:
                payloads = [(entry.filename, zipped.read(entry)) for entry in zipped.infolist()]

            def write_entries():
                with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as zipped:
                    for name, data in payloads:
                        # Preserve count while breaking fixed names/uniqueness.
                        renamed = "input.json" if duplicate else "unexpected.json"
                        zipped.writestr(renamed if name == "receipt.json" else name, data)

            if duplicate:
                with self.assertWarnsRegex(UserWarning, "Duplicate name: 'input.json'"):
                    write_entries()
            else:
                write_entries()

        cases = [
            ("oversize manifest", lambda archive: declared_sizes(archive, {"evidence_manifest.json": 4_000_001}), "C10 ZIP.*size"),
            ("oversize ordinary member", lambda archive: declared_sizes(archive, {"receipt.json": 4_000_001}), "C10 ZIP.*size"),
            ("oversize total", lambda archive: declared_sizes(archive, {
                name: 1_300_000 for name in zip_names(archive)}), "C10 ZIP.*size"),
            ("wrong fixed inventory", lambda archive: replace_inventory(archive), "C10 ZIP.*inventory"),
            ("duplicate inventory", lambda archive: replace_inventory(archive, True), "C10 ZIP.*inventory"),
        ]

        def zip_names(archive):
            with zipfile.ZipFile(archive) as zipped:
                return zipped.namelist()

        with tempfile.TemporaryDirectory(prefix="c10-preflight-") as temporary:
            for index, (label, mutate, message) in enumerate(cases):
                with self.subTest(label=label):
                    kit = Path(temporary) / str(index) / "release" / "v0.2.0"
                    shutil.copytree(KIT, kit, ignore=shutil.ignore_patterns("tmp", "__pycache__"))
                    origins_path = kit / "evidence/c10/artifact-origins.json"
                    origins = json.loads(origins_path.read_bytes())
                    first = origins["artifacts"][0]
                    archive = kit / first["path"]
                    receipt = next(row for row in evidence["receipts"] if row["anchor"] == first["anchor"])
                    source = {"repository": evidence["repository"], "pr_number": receipt["pr"],
                              "head_sha": receipt["source_sha"], "base_sha": receipt["base_sha"],
                              "synthetic_merge_sha": receipt["synthetic_merge_sha"]}
                    mutate(archive)
                    self.assertLess(archive.stat().st_size, 1_000_000)
                    first["sha256"] = digest(archive.read_bytes())
                    origins_path.write_bytes(encoded(origins))
                    rehash_inventory(kit)
                    # An attempted read is a test failure, not an accepted
                    # exception. Only the intended preflight ValueError passes.
                    endpoints = {
                        "outer": lambda: verifier.validate_c10_archives(kit, ROOT, evidence, False),
                        "direct helper": lambda: validate_c10_archive(archive, source, ROOT),
                    }
                    for endpoint, validate in endpoints.items():
                        with self.subTest(endpoint=endpoint), patch.object(zipfile.ZipFile, "read",
                                side_effect=AssertionError("C10 content read before resource preflight")) as read:
                            with self.assertRaisesRegex(ValueError, message):
                                validate()
                            read.assert_not_called()

            # Test inclusive resource boundaries on central metadata only.
            # These are preflight successes, not claims of payload validity.
            source_archive = next(iter(original_archives))
            names = zip_names(source_archive)
            limits = [
                {name: 4_000_000 if name == "evidence_manifest.json" else 0 for name in names},
                {name: 4_000_000 if index < 4 else 0 for index, name in enumerate(names)},
            ]
            for index, sizes in enumerate(limits):
                with self.subTest(inclusive_boundary=index):
                    archive = Path(temporary) / ("boundary-" + str(index) + ".zip")
                    shutil.copyfile(source_archive, archive)
                    declared_sizes(archive, sizes)
                    with zipfile.ZipFile(archive) as zipped, patch.object(zipfile.ZipFile, "read",
                            side_effect=AssertionError("Metadata-only preflight read content")) as read:
                        self.assertEqual(preflight_c10_zip(zipped, ROOT), set(names))
                        read.assert_not_called()
        self.assertEqual(original_archives, {path: digest(path.read_bytes()) for path in original_archives})


class ReleaseGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original_git = verifier.git

        @lru_cache(maxsize=None)
        def immutable_git(*args):
            return cls.original_git(ROOT, *args)

        # The accepted SHA-addressed blobs are immutable. Reuse their exact
        # canonical bytes between cases; current-HEAD reads remain fresh.
        cls.immutable_git = staticmethod(immutable_git)
        cls.temporary = tempfile.TemporaryDirectory(prefix="release-guard-")
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.scratch = Path(cls.temporary.name)
        cls.baseline = cls.scratch / "baseline" / "release" / "v0.2.0"
        cls.exports = [KIT / "manuscript.json", *sorted((KIT / "output/pdf").glob("*.tex")),
                       *sorted((KIT / "output/pdf").glob("*.pdf")),
                       KIT / "output/pdf/theorem-map.json", KIT / "output/pdf/theorem-map.csv"]
        cls.before = {path: digest(path.read_bytes()) for path in cls.exports}
        shutil.copytree(KIT, cls.baseline, ignore=shutil.ignore_patterns("tmp", "__pycache__"))
        # The CI verifies the real inventory separately. Here a legitimate
        # inventory rebuild must not bypass any semantic or receipt guard.
        # Review/code hashes and protected snapshots are deliberately retained.
        rehash_inventory(cls.baseline)
        cls.verify_copy(cls.baseline)

    @classmethod
    def tearDownClass(cls):
        if cls.before != {path: digest(path.read_bytes()) for path in cls.exports}:
            raise AssertionError("Release guard tests modified frozen manuscript/exports")

    @classmethod
    def verify_copy(cls, kit, allow_draft=False, head_mutation=None):
        original_tree = verifier.tree

        def read_tree(root, revision):
            rows = original_tree(root, revision)
            if revision == "HEAD" and head_mutation:
                head_mutation(rows)
            return rows

        def canonical_git(root, *args):
            if any("HEAD" in value for value in args):
                return cls.original_git(ROOT, *args)
            return cls.immutable_git(*args)

        with patch.object(verifier, "git", side_effect=canonical_git), \
                patch.object(verifier, "tree", side_effect=read_tree), \
                contextlib.redirect_stdout(io.StringIO()):
            return verifier.verify(kit, allow_draft)

    def new_copy(self):
        parent = Path(tempfile.mkdtemp(prefix="case-", dir=self.scratch))
        kit = parent / "release" / "v0.2.0"
        shutil.copytree(self.baseline, kit)
        return kit

    def rejects(self, mutate, message, head_mutation=None):
        kit = self.new_copy()
        mutate(kit)
        rehash_inventory(kit)
        with self.assertRaisesRegex(ValueError, message):
            self.verify_copy(kit, head_mutation=head_mutation)

    def test_current_release_head_preserves_core_and_paper(self):
        mutations = [
            lambda rows: rows["PermanssonLean.lean"].update(mode="100755"),
            lambda rows: rows.pop(next(path for path in rows
                                      if path.startswith("paper/") and path.endswith(".pdf"))),
        ]
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                self.rejects(lambda kit: None, "current release HEAD", mutate)

    def test_compile_and_review_receipts_are_required(self):
        for name in ("compile-evidence.json", "review-evidence.json"):
            with self.subTest(name=name):
                self.rejects(lambda kit: (kit / name).unlink(), "required new artifacts")

    def test_receipts_bind_source_exports_compilers_and_reviewed_code(self):
        cases = [
            ("source", "compile-evidence.json", lambda value: value.update(research_source_sha="0" * 40), "source/schema"),
            ("manuscript", "compile-evidence.json", lambda value: value.update(manuscript_json_sha256="0" * 64), "manuscript/TeX"),
            ("pdf", "compile-evidence.json", lambda value: value["primary_pdf"].update(sha256="0" * 64), "primary PDF"),
            ("desktop", "compile-evidence.json", lambda value: value["desktop_tex_compiler"].update(input_sha256="0" * 64), "Desktop compile"),
            ("independent", "compile-evidence.json", lambda value: value["independent_tex_compiler"].update(exit_code=1), "Independent compile"),
            ("code", "review-evidence.json", lambda value: value["reviewed_code_sha256"].update({"package_release.py": "0" * 64}), "Reviewed code hash"),
        ]
        for label, filename, mutate, message in cases:
            with self.subTest(label=label):
                self.rejects(lambda kit: mutate_json(kit, filename, mutate), message)

        def alter_tex(kit):
            tex = kit / "output/pdf/Permansson_Research_Companion_v0.2.0.tex"
            tex.write_bytes(tex.read_bytes() + b"\n% adversary\n")

        self.rejects(alter_tex, "manuscript/TeX")

    def test_stale_recorded_main_merge_is_rejected(self):
        self.rejects(lambda kit: mutate_json(kit, "acceptance-evidence.json",
                     lambda value: next(row for row in value["receipts"] if row["anchor"] == "X1").update(
                         main_merge_sha="bc7617e15084673aa6053ab58282260226344c2b")), "main merge")

    def test_open_scientific_obligations_cannot_be_deleted_promoted_or_reworded(self):
        def delete_ma2(data):
            for section in data["sections"]:
                section["claims"] = [row for row in section.get("claims", []) if row["anchor"] != "F1.MA2"]

        cases = [
            ("deleted", delete_ma2, "anchors/statuses"),
            ("promoted", lambda value: next(row for row in claims(value) if row["anchor"] == "F1.MA2").update(status="PROVED"), "anchors/statuses"),
            ("nonempty false prose", lambda value: next(row for row in claims(value) if row["anchor"] == "F1.MA2").update(open="This obligation has been fulfilled."), "scientific contract"),
        ]
        for label, mutate, message in cases:
            with self.subTest(label=label):
                self.rejects(lambda kit: mutate_json(kit, "manuscript.json", mutate), message)
        self.rejects(lambda kit: mutate_json(kit, "acceptance-evidence.json",
                     lambda value: value["open_boundaries"].__setitem__(0, "This obligation has been fulfilled.")), "OPEN boundaries")

    def test_repaired_archive_hashes_do_not_certify_failed_c10_proof_content(self):
        cases = [
            ("failed status", lambda data: inner_json(data, "evidence_manifest.json", lambda value: value["proof"].update(status="FAILED"))),
            ("missing theorem", lambda data: inner_json(data, "evidence_manifest.json", lambda value: value["proof"]["theorems"].pop())),
            ("forbidden axiom", lambda data: inner_json(data, "evidence_manifest.json", lambda value: value["proof"]["transitive_axioms_allowlist"].append("sorryAx"))),
            ("corrupt Lean", lambda data: data.update({"C10ReifiedGolden.lean": data["C10ReifiedGolden.lean"] + b"\nexample : False := by\n  exact True.intro\n"})),
            ("wrong number", lambda data: inner_json(data, "receipt.json", lambda value: value["members"][0].update(margin="0"))),
            ("failed compiler", lambda data: data.update({"lean_check.stderr.txt": data["lean_check.stderr.txt"] + b"error: process exited with code 1\n"})),
            ("missing capture", lambda data: data.update({"mixed_check.stdout.txt": b""})),
        ]
        for label, mutate in cases:
            with self.subTest(label=label):
                message = "Unexpected compiler stderr/failed execution" if label == "failed compiler" else "C10"
                self.rejects(lambda kit: rehashed_c10(kit, mutate), message)

    def test_package_metadata_cannot_change_with_repaired_archive_checksum(self):
        kit = self.new_copy()
        with patch.object(packager, "verify", side_effect=self.verify_copy), \
                contextlib.redirect_stdout(io.StringIO()):
            packager.package(kit)
            archive = kit.parent / packager.ARCHIVE
            checksum = kit.parent / (packager.ARCHIVE + ".sha256")
            original = archive.read_bytes()
            metadata = {
                "date_time": (2026, 10, 18, 0, 0, 0), "create_system": 0,
                "external_attr": 0o100755 << 16, "compress_type": zipfile.ZIP_STORED,
                "create_version": 21, "extract_version": 21, "internal_attr": 1,
                "reserved": 1, "comment": b"mutated", "extra": b"\xfe\xca\x00\x00",
            }
            for field, value in metadata.items():
                with self.subTest(field=field):
                    with zipfile.ZipFile(io.BytesIO(original)) as zipped:
                        entries = [(info, zipped.read(info)) for info in zipped.infolist()]
                    with zipfile.ZipFile(archive, "w") as zipped:
                        for info, data in entries:
                            if info.filename.endswith("manuscript.json"):
                                setattr(info, field, value)
                            zipped.writestr(info, data)
                    checksum.write_text(digest(archive.read_bytes()) + "  " + packager.ARCHIVE + "\n",
                                        encoding="ascii", newline="\n")
                    with self.assertRaisesRegex(ValueError, field):
                        packager.package(kit, True)

            with zipfile.ZipFile(io.BytesIO(original)) as zipped:
                entries = [(info, zipped.read(info)) for info in zipped.infolist()]
            with zipfile.ZipFile(archive, "w") as zipped:
                for info, data in entries:
                    zipped.writestr(info, data)
                zipped.comment = b"mutated"
            checksum.write_text(digest(archive.read_bytes()) + "  " + packager.ARCHIVE + "\n",
                                encoding="ascii", newline="\n")
            with self.assertRaisesRegex(ValueError, "Archive comment"):
                packager.package(kit, True)


if __name__ == "__main__":
    unittest.main()
