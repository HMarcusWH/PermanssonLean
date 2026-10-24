"""Synthetic GitHub API responses test candidate artifact authenticity gates.

No mocked GitHub response is an actual check run, true source compiler output
or independent scientific review. Real mode must query the live GitHub API.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import zipfile

import final_closure_candidate_artifact_auth as auth
from final_closure_authenticate import AuthenticationError

H = "a" * 40
RUN, CHECK, ARTIFACT = 111, 222, 333


class CandidateArtifactIntegrity(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="pr113-artifact-auth-")
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.artifact = root / "artifact.zip"
        cases = ["A-01", "B-01"]
        self.manifest = {
            "format": "Permansson.AllOriginalSemanticCandidateShard.v1",
            "status": "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED_RECEIPT",
            "head": H, "shard_index": 0, "shard_count": 9,
            "case_ids": cases,
            "completed": [{"case_id": case} for case in cases],
            "independent_review": False,
            "ci_check_run_id": None, "mathematical_acceptance": False,
        }
        with zipfile.ZipFile(self.artifact, "w") as archive:
            archive.writestr("unreviewed_shard_manifest.json",
                             json.dumps(self.manifest))
        digest = hashlib.sha256(self.artifact.read_bytes()).hexdigest()
        self.responses = {
            f"/actions/runs/{RUN}": {
                "id": RUN, "head_sha": H,
                "head_branch": "research/final-mathematical-closure",
                "event": "push", "status": "completed",
                "conclusion": "success", "run_attempt": 1,
                "path": ".github/workflows/pr113-all-original-semantic-candidates.yml",
            },
            f"/check-runs/{CHECK}": {
                "id": CHECK, "head_sha": H,
                "status": "completed", "conclusion": "success",
                "app": {"slug": "github-actions"},
            },
            f"/actions/artifacts/{ARTIFACT}": {
                "id": ARTIFACT,
                "name": "pr113-all-original-semantic-candidates-0",
                "expired": False,
                "digest": "sha256:" + digest,
                "workflow_run": {"id": RUN, "head_sha": H},
            },
        }
        self.jobs = [{
            "name": "semantic-candidate-shard (0)",
            "run_id": RUN, "head_sha": H,
            "run_attempt": 1, "status": "completed",
            "conclusion": "success",
            "check_run_url":
              f"https://api.github.com/repos/HMarcusWH/PermanssonLean/check-runs/{CHECK}",
        }]

    def evaluate(self):
        with (
            mock.patch.dict(os.environ, {"GITHUB_TOKEN": "fake-test-token"}),
            mock.patch.object(auth, "git_head", return_value=H),
            mock.patch.object(auth, "live",
                              side_effect=lambda path: self.responses[path]),
            mock.patch.object(auth, "paginate", return_value=self.jobs),
            mock.patch.object(auth, "select_cases",
                              return_value=("A-01", "B-01")),
        ):
            return auth.verify_artifact(
                kind="append", shard=0, head=H,
                run_id=RUN, artifact_id=ARTIFACT,
                artifact_zip=self.artifact)

    def test_verified_git_origin_still_remains_unreviewed(self):
        report = self.evaluate()
        self.assertEqual(report["actual_check_run_id"], CHECK)
        self.assertEqual(report["run_id"], RUN)
        self.assertEqual(report["artifact_id"], ARTIFACT)
        self.assertIn("UNREVIEWED", report["status"])
        self.assertFalse(report["mathematical_acceptance"])
        self.assertFalse(report["independent_review"])
        self.assertFalse(report["scientific_release_approved"])
        self.assertIsNone(report["merged_main_sha"])

    def test_wrong_job_status_run_head_and_artifact_digest_rejected(self):
        wrongs = (
            ("run", lambda: self.responses[f"/actions/runs/{RUN}"].update(
                head_sha="b"*40)),
            ("job", lambda: self.jobs[0].update(conclusion="failure")),
            ("artifact", lambda: self.responses[
                f"/actions/artifacts/{ARTIFACT}"].update(digest="sha256:"+"0"*64)),
            ("expired", lambda: self.responses[
                f"/actions/artifacts/{ARTIFACT}"].update(expired=True)),
            ("app", lambda: self.responses[
                f"/check-runs/{CHECK}"]["app"].update(slug="untrusted")),
        )
        baseline_resp = copy.deepcopy(self.responses)
        baseline_jobs = copy.deepcopy(self.jobs)
        for label, mutate in wrongs:
            self.responses = copy.deepcopy(baseline_resp)
            self.jobs = copy.deepcopy(baseline_jobs)
            mutate()
            with self.subTest(label=label), self.assertRaises(
                    AuthenticationError):
                self.evaluate()
        self.responses = baseline_resp
        self.jobs = baseline_jobs

    def test_false_approval_in_candidate_manifest_rejected(self):
        modified = dict(self.manifest, independent_review=True)
        with zipfile.ZipFile(self.artifact, "w") as archive:
            archive.writestr("unreviewed_shard_manifest.json",
                             json.dumps(modified))
        new_digest = hashlib.sha256(self.artifact.read_bytes()).hexdigest()
        self.responses[f"/actions/artifacts/{ARTIFACT}"]["digest"] = (
            "sha256:" + new_digest)
        with self.assertRaises(AuthenticationError):
            self.evaluate()


if __name__ == "__main__":
    unittest.main()
