"""Adversarial release-source archive verification. Fake bytes are DRAFT ONLY."""
import copy
import hashlib
import json
from pathlib import Path
import stat
import tempfile
import unittest
import zipfile

import archive_integrity as a
import verify_release as verifier


def sha(b):
    return hashlib.sha256(b).hexdigest()


class CompleteDraftArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="perm-draft-check-")
        self.addCleanup(self.temp.cleanup)
        self.out = Path(self.temp.name)
        self.source = {
            "manuscript/" + name: ("synthetic test source: " + name).encode()
            for name in a.SOURCE_FILES
        }
        self.generated = {
            "Permansson_Mathematical_Closure.pdf": b"%PDF-1.4\nSYNTHETIC TEST BYTES\n",
            "Permansson_Mathematical_Closure.tex": b"\\documentclass{article}",
            "latex_build.log": b"fake normalized LaTeX log",
            "source_ci_receipts.lock.json": json.dumps({
                "status": "MISSING_POST_MERGE_SOURCE_AND_REVIEWS",
                "ci_receipts": [], "independent_reviews": [],
            }).encode(),
        }
        pdf = self.generated["Permansson_Mathematical_Closure.pdf"]
        self.manifest = {
            "format": "Permansson.MathClosure.BuildReceipt.v1",
            "mode": "DRAFT", "status": "DRAFT_NOT_ACCEPTED",
            "source_commit_sha": "a"*40, "pdf_sha256": sha(pdf),
            "tex_sha256": sha(self.generated["Permansson_Mathematical_Closure.tex"]),
            "latex_log_sha256": sha(self.generated["latex_build.log"]),
            "pdf_page_count": 2,
            "empirical_identification_status": "NOT_ESTABLISHED",
            "source_tree_files": {
                "research_papers/mathematical_closure/" + name:
                    sha(self.source["manuscript/" + name])
                for name in a.SOURCE_FILES
            },
        }
        self.generated["manifest.lock.json"] = json.dumps(self.manifest).encode()
        self.save()

    def save(self, *, extra=None, override=None, mode_override=None):
        members = dict(self.source, **self.generated)
        if override:
            members.update(override)
        if extra:
            members.update(extra)
        path = self.out / "Permansson_Mathematical_Closure_E2E.zip"
        with zipfile.ZipFile(path, "w") as z:
            for name, raw in sorted(members.items()):
                info = zipfile.ZipInfo(name, (1980, 1, 1, 0, 0, 0))
                info.external_attr = (mode_override.get(name, 0o100644)
                                      if mode_override else 0o100644) << 16
                z.writestr(info, raw)
        for name, raw in self.generated.items():
            (self.out / name).write_bytes(raw)
        ledger = ""
        for name in a.SUMMED:
            ledger += sha((self.out/name).read_bytes()) + "  " + name + "\n"
        (self.out / "SHA256SUMS.txt").write_text(ledger)
        return path

    def test_complete_13_sources_and_draft_ledger_pass(self):
        got = a.verify_draft_archive(self.out, self.manifest)
        self.assertEqual(got["canonical_sources"], 13)
        self.assertEqual(got["archived_outputs"], 5)
        self.assertEqual(verifier.verify(self.out/"manifest.lock.json")["integrity"],
                         "PASS")

    def test_extra_or_missing_archive_members_never_pass(self):
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(
                self.out, dict(self.manifest, source_tree_files={}))
        self.save(extra={"manuscript/unexpected.tex": b"hello"})
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)
        self.save(extra={"../escape.txt": b"x"})
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)

    def test_modified_bibliography_or_generated_pdf_rejected(self):
        self.save(override={"manuscript/references.bib": b"silently changed"})
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)
        self.save()
        (self.out/"Permansson_Mathematical_Closure.pdf").write_bytes(b"%PDF-BAD")
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)

    def test_symlink_member_is_not_a_source_file(self):
        self.save(mode_override={"manuscript/main.tex": stat.S_IFLNK | 0o777})
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)

    def test_unbound_source_ci_receipt_is_rejected(self):
        replacement = json.dumps({
            "status": "ACCEPTED", "ci_receipts": [17],
            "independent_reviews": [{"review": "faked"}],
        }).encode()
        self.save(override={"source_ci_receipts.lock.json": replacement})
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)

    def test_altered_checksum_ledger_and_duplicate_line_rejected(self):
        p = self.out/"SHA256SUMS.txt"
        p.write_text(p.read_text() + "0"*64 + "  " + a.SUMMED[0] + "\n")
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)
        self.save()
        p.write_text(p.read_text().replace("a", "b", 1))
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)

    def test_page_images_must_match_entire_1_to_n_set(self):
        pages = self.out/"pages"
        pages.mkdir()
        (pages/"page-1.png").write_bytes(b"fake")
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)
        (pages/"page-02.png").write_bytes(b"fake")
        self.assertEqual(a.verify_draft_archive(self.out, self.manifest)
                         ["status"], "COMPLETE_UNAPPROVED_DRAFT")
        (pages/"irrelevant.png").write_bytes(b"fake")
        with self.assertRaises(a.DraftArchiveError):
            a.verify_draft_archive(self.out, self.manifest)


if __name__ == "__main__":
    unittest.main()
