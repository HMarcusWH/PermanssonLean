"""Pure-Python verification of source-bound CI owner packaging."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from pr113_pack_ci_positive_owners import owner_manifest, ProducerError


HEAD = "a" * 40
OUT = b""
ERR = b"Ran 1 test in 0.001s\n\nOK\n"
LEAN = b"Lean source compiles; no errors.\n"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fixture(root, count=45):
    source = root / "source"
    source.mkdir()
    records = []
    for index in range(count):
        cid = f"Q-{index:02d}"
        path = source / cid
        path.mkdir()
        logs = {
            "unittest_stdout.log": OUT,
            "unittest_stderr.log": ERR,
            "source_positive.log": LEAN,
        }
        data = {
            "format": "Permansson.PR113.OriginalCasePositiveCandidate.v1",
            "status": "SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED",
            "head_sha": HEAD,
            "case_id": cid,
            "positive_role": "COMPILER_SOURCE",
            "source_positive_exit_code": 0,
            "registered_method_exit_code": 0,
            "actual_producing_check_run_id": None,
            "authenticated_ci_artifact": False,
            "independent_case_review": False,
            "scientific_release_approved": False,
            "unittest_stdout_sha256": sha(OUT),
            "unittest_stderr_sha256": sha(ERR),
            "source_positive_log_sha256": sha(LEAN),
        }
        records.append(data)
        (path / "unreviewed_positive.json").write_text(
            json.dumps(data, sort_keys=True))
        for name, raw in logs.items():
            (path / name).write_bytes(raw)
    summary = {
        "format": "Permansson.PR113.Original45PositiveRoutesCandidate.v1",
        "status": "EXECUTED_NO_PRODUCING_CI_OR_MATH_REVIEW",
        "head_sha": HEAD,
        "actual_positive_cases": count,
        "positive_route_records": records,
        "authenticated_ci_artifact": False,
        "scientific_release_approved": False,
    }
    (source / "unreviewed_45_positive_routes.json").write_text(
        json.dumps(summary, sort_keys=True))
    return source


class SourceOwnedPositivePackerTests(unittest.TestCase):
    def test_forty_five_original_bytes_but_no_approval(self):
        with tempfile.TemporaryDirectory() as base:
            root = Path(base)
            src = fixture(root)
            target = root / "output"
            result = owner_manifest(HEAD, 123, 1, src, target)
            self.assertEqual(len(result["owners"]), 45)
            self.assertEqual(result["github_run_id"], 123)
            self.assertFalse(result["independent_review"])
            self.assertEqual(result["accepted_cases"], 0)
            self.assertEqual(result["accepted_claims"], 0)
            self.assertEqual(
                result["owners"][0]["receipt_member"],
                "positive/Q-00/unreviewed_positive.json")

    def test_one_missing_case_rejects_total(self):
        with tempfile.TemporaryDirectory() as base:
            root = Path(base)
            src = fixture(root, count=44)
            with self.assertRaises(ProducerError):
                owner_manifest(HEAD, 123, 1, src, root / "output")

    def test_tampered_lean_log_fails(self):
        with tempfile.TemporaryDirectory() as base:
            root = Path(base)
            src = fixture(root)
            (src / "Q-11" / "source_positive.log").write_bytes(
                b"error: forged source proof\n")
            with self.assertRaisesRegex(ProducerError, "digest"):
                owner_manifest(HEAD, 123, 1, src, root / "output")

    def test_self_awarded_review_rejected(self):
        with tempfile.TemporaryDirectory() as base:
            root = Path(base)
            src = fixture(root)
            record = src / "Q-11" / "unreviewed_positive.json"
            data = json.loads(record.read_text())
            data["independent_case_review"] = True
            record.write_text(json.dumps(data))
            with self.assertRaises(ProducerError):
                owner_manifest(HEAD, 123, 1, src, root / "output")

    def test_no_boolean_git_run_id(self):
        with tempfile.TemporaryDirectory() as base:
            root = Path(base)
            src = fixture(root)
            with self.assertRaises(ProducerError):
                owner_manifest(HEAD, True, 1, src, root / "output")


if __name__ == "__main__":
    unittest.main()
