"""Pure-Python adversarial preseal input carrier tests (no release approval)."""
import io
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from pr113_preseal_input_carrier import (
    EXPECTED_FILES, PresealInputError, digest, extract,
    inspect_original_carrier, verified_transport,
)

M = "a" * 40


def zipped(override=None):
    files = {name: b"source-bound-but-unreviewed-" + name.encode()
             for name in EXPECTED_FILES}
    files["reviewed/additional_zips/101.zip"] = b"synthetic GH artifact bytes"
    if override:
        files.update(override)
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for name, data in sorted(files.items()):
            z.writestr(name, data)
    return buf.getvalue()


def originals(raw):
    run = {
        "id": 101, "head_sha": M, "head_branch": "main",
        "status": "completed", "conclusion": "success",
        "event": "workflow_dispatch", "run_attempt": 2,
        "path": ".github/workflows/preseal-input-transport.yml",
    }
    job = {
        "id": 102, "name": "review-evidence-transport",
        "run_id": 101, "run_attempt": 2, "head_sha": M,
        "status": "completed", "conclusion": "success",
        "check_run_url": "https://api.github.com/repos/a/b/check-runs/103",
        "started_at": "2026-10-24T12:00:00Z",
        "completed_at": "2026-10-24T12:15:00Z",
    }
    check = {
        "id": 103, "name": "review-evidence-transport",
        "head_sha": M, "status": "completed", "conclusion": "success",
        "app": {"slug": "github-actions"},
    }
    artifact = {
        "id": 104, "name": "pr113-preseal-review-inputs",
        "digest": "sha256:" + digest(raw), "expired": False,
        "created_at": "2026-10-24T12:10:00Z",
        "workflow_run": {"id": 101, "head_sha": M},
    }
    return {"merged": M, "run_id": 101, "attempt": 2,
            "job_id": 102, "check_id": 103, "artifact_id": 104,
            "meta": artifact, "run": run,
            "jobs": {"jobs": [job]}, "check": check, "raw": raw}


class PresealOriginalTransportTests(unittest.TestCase):
    def test_valid_transport_still_has_zero_approvals(self):
        payload = originals(zipped())
        result = verified_transport(**payload)
        self.assertEqual(result["source_commit_sha"], M)
        self.assertEqual(result["status"],
                         "TRANSPORT_BYTES_BOUND_NOT_APPROVED")

    def test_failed_or_wrong_attempt_cannot_supply_evidence(self):
        for name, edit in (
            ("failed run", lambda x: x["run"].update(conclusion="failure")),
            ("wrong head", lambda x: x["run"].update(head_sha="b" * 40)),
            ("wrong branch", lambda x: x["run"].update(head_branch="feature")),
            ("stale attempt", lambda x: x["jobs"]["jobs"][0].update(run_attempt=1)),
            ("failed job", lambda x: x["jobs"]["jobs"][0].update(conclusion="failure")),
            ("failed check", lambda x: x["check"].update(conclusion="failure")),
            ("wrong check", lambda x: x["check"].update(head_sha="c" * 40)),
            ("expired", lambda x: x["meta"].update(expired=True)),
            ("digest", lambda x: x["meta"].update(digest="sha256:" + "0" * 64)),
            ("wrong artifact", lambda x: x["meta"].update(name="other")),
            ("early artifact", lambda x: x["meta"].update(
                created_at="2026-10-24T11:00:00Z")),
            ("late artifact", lambda x: x["meta"].update(
                created_at="2026-10-24T12:20:00Z")),
            ("wrong run", lambda x: x["meta"]["workflow_run"].update(id=202)),
        ):
            with self.subTest(case=name):
                payload = originals(zipped())
                edit(payload)
                with self.assertRaises(PresealInputError):
                    verified_transport(**payload)

    def test_all_reviewed_file_names_are_required(self):
        entries = inspect_original_carrier(zipped())
        self.assertEqual(set(EXPECTED_FILES).issubset(entries), True)
        missing = dict((name, b"x") for name in EXPECTED_FILES
                       if not name.endswith("approved_claim_manifest.json"))
        missing["reviewed/additional_zips/101.zip"] = b"zip"
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
            for name, raw in missing.items():
                z.writestr(name, raw)
        with self.assertRaises(PresealInputError):
            inspect_original_carrier(buf.getvalue())

    def test_arbitrary_zip_member_and_traversal_are_rejected(self):
        for name in (
            "reviewed/../../evil.txt",
            "reviewed/additional_zips/../../evil.zip",
            "reviewed/additional_zips/abc.zip",
            "reviewed/approved_manifest.json",
        ):
            with self.subTest(name=name):
                with self.assertRaises(PresealInputError):
                    inspect_original_carrier(zipped({name: b"bad"}))

    def test_valid_transport_does_not_become_math_acceptance(self):
        with tempfile.TemporaryDirectory(prefix="pr113-transport-") as td:
            root = Path(td)
            payload = originals(zipped())
            src = root / "upstream.zip"
            src.write_bytes(payload.pop("raw"))
            target = root / "out"
            result = extract(src, target, **payload)
            self.assertIs(result["independent_review"], False)
            self.assertIs(result["mathematical_acceptance"], False)
            self.assertIs(result["publication_authorized"], False)
            self.assertEqual(
                result["status"],
                "GH_SOURCE_TRANSPORT_VERIFIED__RELEASE_REVIEW_PENDING")
            persisted = json.loads(
                (target / "transport_diagnostics.json").read_text())
            self.assertEqual(persisted, result)
            self.assertEqual(
                persisted["transport_artifact_sha256"], digest(src.read_bytes()))
            self.assertTrue((target / "additional_zips/101.zip").is_file())
            self.assertFalse((target / "approved_claim_manifest.json").is_symlink())



    def test_traversing_and_symlinked_carrier_paths_fail_before_intake(self):
        from unittest import mock
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            original = root / "original.zip"
            raw = zipped()
            original.write_bytes(raw)
            target_dir = root / "target"
            target_dir.mkdir()
            options = {key:value for key,value in originals(raw).items()
                       if key != "raw"}
            with mock.patch("pr113_preseal_input_carrier.verified_transport") as authenticate:
                with self.assertRaises(ValueError):
                    extract(original, target_dir / ".." / "other", **options)
                authenticate.assert_not_called()
            alias = root / "alias"
            alias.symlink_to(target_dir, target_is_directory=True)
            with self.assertRaises(ValueError):
                extract(original, alias / "evidence", **options)
            self.assertFalse((target_dir / "evidence").exists())

    def test_staged_preseal_consumer_uses_exact_outer_status_and_digest(self):
        yaml = (Path(__file__).resolve().parents[2] /
                "docs/operations/pr113_unapproved_workflows/"
                "pr113-preseal-fullscope.yml").read_text()
        self.assertIn('input_report["status"]', yaml)
        self.assertIn(
            '"GH_SOURCE_TRANSPORT_VERIFIED__RELEASE_REVIEW_PENDING"', yaml)
        self.assertIn('input_report["transport_artifact_sha256"]', yaml)
        self.assertIn('input_report["independent_review"] is False', yaml)


if __name__ == "__main__":
    unittest.main()
