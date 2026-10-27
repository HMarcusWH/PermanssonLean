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
import pr113_producer_target_v3 as producer
from release_target import B113
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
        self.synthetic_source_event = {
            "GITHUB_ACTIONS": "true", "GITHUB_REPOSITORY": "HMarcusWH/PermanssonLean",
            "GITHUB_SHA": H, "GITHUB_EVENT_NAME": "push",
            "GITHUB_REF": "refs/heads/research/final-mathematical-closure",
        }
        self.synthetic_live_pr = {
            "number": 113, "merged": False,
            "head": {"sha": H, "ref": "research/final-mathematical-closure"},
            "base": {"sha": B113},
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
        # Explicit synthetic event/PR/Git fixture, retaining the actual
        # production source guard and all of its fail-closed conditions.
        real_guard = producer.authenticated_producer_branch
        def git(*args):
            if args == ("rev-parse", "HEAD"):
                return H
            if args == ("cat-file", "-t", H):
                return "commit"
            raise AssertionError("unmocked producer Git command: " + repr(args))
        def synthetic_source_guard(head):
            def live(url):
                if url == "/pulls/113":
                    return self.synthetic_live_pr
                raise AssertionError("unmocked producer GitHub path: " + url)
            return real_guard(head, env=self.synthetic_source_event, live=live, git=git)
        with (
            mock.patch.dict(os.environ, {"GITHUB_TOKEN": "fake-test-token"}),
            mock.patch.object(producer, "authenticated_producer_branch",
                              side_effect=synthetic_source_guard),
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


    def test_synthetic_wrong_source_event_or_pr_fails_before_artifact(self):
        original_event = copy.deepcopy(self.synthetic_source_event)
        for key, value in (
            ("GITHUB_ACTIONS", "false"),
            ("GITHUB_SHA", "f"*40),
            ("GITHUB_REF", "refs/heads/invalid"),
            ("GITHUB_REPOSITORY", "foreign/repository"),
        ):
            self.synthetic_source_event = dict(original_event, **{key: value})
            with self.subTest(event=key), self.assertRaises(
                    producer.ProducerTargetError):
                self.evaluate()
        self.synthetic_source_event = original_event
        original_pr = copy.deepcopy(self.synthetic_live_pr)
        for edit in (
            lambda pr: pr["head"].update(sha="f"*40),
            lambda pr: pr["base"].update(sha="f"*40),
            lambda pr: pr.update(merged=True),
        ):
            self.synthetic_live_pr = copy.deepcopy(original_pr)
            edit(self.synthetic_live_pr)
            with self.subTest(pr=self.synthetic_live_pr), self.assertRaises(
                    producer.ProducerTargetError):
                self.evaluate()
        self.synthetic_live_pr = original_pr

    def test_attestation_output_traversal_rejects_before_live_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            destination = base / "outside"
            destination.mkdir()
            args = [
                "--head", H, "--kind", "append", "--shard", "0",
                "--run-id", str(RUN), "--artifact-id", str(ARTIFACT),
                "--artifact-zip", str(self.artifact),
                "--output", str(destination / ".." / "forged.json"),
            ]
            with mock.patch.object(auth, "verify_artifact") as external:
                self.assertEqual(auth.main(args), 2)
                external.assert_not_called()
            self.assertFalse((base / "forged.json").exists())

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
