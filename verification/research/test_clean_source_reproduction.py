"""Synthetic command stubs test two-source-root control flow, not PDF evidence."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

RELEASE = Path(__file__).resolve().parents[2] / "release/mathematical-closure-1"
sys.path.insert(0, str(RELEASE))
import reproduce_clean_sources as clean

H = "a"*40
T = "b"*40


class CleanSourceRootRebuildTests(unittest.TestCase):
    def test_invalid_sha_and_source_checkout_output_rejected(self):
        with tempfile.TemporaryDirectory(prefix="clean-root-unit-") as td:
            out = Path(td)/"new"
            with self.assertRaises(clean.CleanReproductionError):
                clean.reproduce_from_clean_source_roots(out, head="x")
            with self.assertRaises(clean.CleanReproductionError):
                clean.reproduce_from_clean_source_roots(
                    clean.ROOT / "release" / "illegal", head=H)
            out.mkdir()
            with self.assertRaises(clean.CleanReproductionError):
                clean.reproduce_from_clean_source_roots(out, head=H)

    def test_diagnostic_mismatches_never_pass_as_reproducible(self):
        with tempfile.TemporaryDirectory(prefix="clean-root-negative-") as td:
            target = Path(td) / "output"
            completed = []
            def git(args, cwd):
                if args == ["rev-parse", "HEAD"]: return H
                if args == ["rev-parse", "HEAD^{tree}"]: return T
                if args == ["status", "--porcelain", "--untracked-files=no"]: return ""
                if args[:2] == ["checkout", "--detach"]: return ""
                raise AssertionError(args)
            def run(arguments, *, cwd=None, timeout=600):
                if len(arguments) > 1 and "build.py" in str(arguments[1]):
                    dest = Path(arguments[arguments.index("--out")+1])
                    dest.mkdir(parents=True)
                    serial = "d"*64 if len(completed) == 0 else "e"*64
                    completed.append(serial)
                    (dest / "manifest.lock.json").write_text(json.dumps({
                        "status": "DRAFT_NOT_ACCEPTED",
                        "source_commit_sha": H,
                        "pdf_sha256": serial,
                        "pdf_page_count": 1,
                    }))
                    (dest / "Permansson_Mathematical_Closure_E2E.zip").write_bytes(b"Z")
                    (dest / "pages").mkdir()
                return ""
            with mock.patch.object(clean, "git_object", side_effect=git), \
                 mock.patch.object(clean, "cmd", side_effect=run):
                with self.assertRaises(clean.CleanReproductionError) as ctx:
                    clean.reproduce_from_clean_source_roots(target, head=H)
            self.assertIn("pdf_sha256", str(ctx.exception))
            report = json.loads((target/"reproduction_failure.json").read_text())
            self.assertEqual(report["status"], "TWO_CLEAN_SOURCE_BUILDS_BLOCKED")
            self.assertIn("pdf_sha256", report["differences"])
            self.assertFalse(report["scientific_release_approved"])

    def test_mismatch_diagnostic_names_real_manifest_log_and_zip_fields(self):
        with tempfile.TemporaryDirectory(prefix="perm-r02-diff-") as td:
            one, two = Path(td)/"first", Path(td)/"second"
            one.mkdir(); two.mkdir()
            (one/"manifest.lock.json").write_text(
                json.dumps({"pdf_sha256":"a"*64,"latex_log_sha256":"b"*64}))
            (two/"manifest.lock.json").write_text(
                json.dumps({"pdf_sha256":"a"*64,"latex_log_sha256":"c"*64}))
            (one/"latex_build.log").write_text("ok\n<ROOT>/one\nwarning: A\n")
            (two/"latex_build.log").write_text("ok\n<ROOT>/two\nwarning: A\n")
            import zipfile
            for path, body in ((one,b"alpha"),(two,b"bravo")):
                with zipfile.ZipFile(path/"Permansson_Mathematical_Closure_E2E.zip","w") as z:
                    z.writestr("manifest.lock.json",body)
                    z.writestr("stable.txt",b"same")
            left=clean.diagnose_root_differences(one,two)
            self.assertEqual(list(left["manifest_changed_fields"]),["latex_log_sha256"])
            self.assertEqual(left["differing_logs"]["latex_build.log"]
                             ["first_differing_line_index"],1)
            self.assertEqual(left["draft_archive"]["all_changed_member_count"],1)
            self.assertIn("manifest.lock.json",
                          left["draft_archive"]["first_different_members"])
            self.assertFalse(left["byte_identity_waived"])
            self.assertFalse(left["scientific_release_approved"])

    def test_different_zip_member_order_is_detected(self):
        with tempfile.TemporaryDirectory(prefix="perm-r02-order-") as td:
            import zipfile
            one,two=Path(td)/"first.zip",Path(td)/"second.zip"
            with zipfile.ZipFile(one,"w") as z:
                z.writestr("a.txt",b"A");z.writestr("b.txt",b"B")
            with zipfile.ZipFile(two,"w") as z:
                z.writestr("b.txt",b"B");z.writestr("a.txt",b"A")
            detail=clean._zip_delta(one,two)
            self.assertFalse(detail["member_order_matches"])
            self.assertEqual(detail["all_changed_member_count"],0)

    def test_missing_or_altered_page_is_reported(self):
        with tempfile.TemporaryDirectory(prefix="perm-r02-page-") as td:
            one,two=Path(td)/"first",Path(td)/"second"
            for root in (one,two):
                (root/"pages").mkdir(parents=True)
            (one/"pages/page-1.png").write_bytes(b"page-A")
            (two/"pages/page-1.png").write_bytes(b"page-B")
            detail=clean.diagnose_root_differences(one,two)
            self.assertEqual(detail["rendered_pages"]["changed"],["page-1.png"])
            (two/"pages/page-1.png").unlink()
            detail=clean.diagnose_root_differences(one,two)
            self.assertEqual(detail["rendered_pages"]["changed"],["page-1.png"])

    def test_fixed_pdftex_trailer_identity_is_explicit_and_source_bound(self):
        """Different output-root paths must not randomize the PDF backend ID."""
        preamble = (clean.ROOT / "research_papers/mathematical_closure" /
                    "preamble.tex").read_text(encoding="utf-8")
        self.assertIn(r"\ifdefined\pdftrailerid", preamble)
        self.assertIn(
            r"\pdftrailerid{<5045524D414E53534F4E2D4D41544821> "
            r"<5045524D414E53534F4E2D4D41544821>}",
            preamble)
        self.assertIn(r"\fi", preamble)

    def test_mock_two_distinct_clones_and_no_approval(self):
        with tempfile.TemporaryDirectory(prefix="clean-root-unit-") as td:
            target = Path(td)/"output"
            calls = []
            pdf_sha = "d"*64
            zip_sha = "e"*64
            manifest_sha = None

            def git(args, cwd):
                if args == ["rev-parse", "HEAD"]: return H
                if args == ["rev-parse", "HEAD^{tree}"]: return T
                if args == ["status", "--porcelain", "--untracked-files=no"]: return ""
                if args[:2] == ["checkout", "--detach"]: return ""
                raise AssertionError(args)

            def runner(arguments, *, cwd=None, timeout=600):
                calls.append(tuple(str(x) for x in arguments))
                if "build.py" in str(arguments[1]) if len(arguments) > 1 else False:
                    pos = arguments.index("--out") + 1
                    out = Path(arguments[pos])
                    out.mkdir(parents=True)
                    (out/"manifest.lock.json").write_text(json.dumps({
                        "status": "DRAFT_NOT_ACCEPTED",
                        "source_commit_sha": H,
                        "pdf_sha256": pdf_sha,
                        "pdf_page_count": 1,
                    }))
                    (out/"Permansson_Mathematical_Closure_E2E.zip").write_bytes(b"ZIP")
                    (out/"pages").mkdir()
                return ""

            from hashlib import sha256
            real_zip_sha = sha256(b"ZIP").hexdigest()
            with mock.patch.object(clean, "git_object", side_effect=git), \
                 mock.patch.object(clean, "cmd", side_effect=runner), \
                 mock.patch.object(clean.reproduce, "compare_artifacts",
                                   return_value={"status": "REPRODUCIBLE_DRAFT_ONLY",
                                                 "pdf_sha256": pdf_sha,
                                                 "zip_sha256": real_zip_sha}):
                result = clean.reproduce_from_clean_source_roots(target, head=H)
            clones = [c for c in calls if c[:3] == ("git", "clone", "--local")]
            self.assertEqual(len(clones), 2)
            self.assertNotEqual(clones[0][-1], clones[1][-1])
            self.assertIn("--no-hardlinks", clones[0])
            self.assertIn("--no-hardlinks", clones[1])
            self.assertEqual(result["independent_source_roots"], 2)
            self.assertEqual(result["source_commit_sha"], H)
            self.assertTrue(result["two_complete_archive_audits"])
            self.assertFalse(result["authenticated_ci_artifact"])
            self.assertFalse(result["scientific_release_approved"])
            self.assertTrue((target/"reproduction_receipt.json").is_file())


if __name__ == "__main__":
    unittest.main()
