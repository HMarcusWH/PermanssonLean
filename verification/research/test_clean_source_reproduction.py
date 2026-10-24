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
