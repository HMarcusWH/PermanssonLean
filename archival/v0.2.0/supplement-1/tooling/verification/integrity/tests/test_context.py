import json
from dataclasses import asdict
import os
from pathlib import Path
import unittest
from unittest import mock

from verification.integrity.ci_context import capture_context, require_pr_acceptance, REPOSITORY, main as context_cli
from verification.integrity.reports import HardeningError
from verification.integrity.tests._fixtures import GitFixture


class ContextTests(unittest.TestCase):
    def setUp(self):
        self.fixture = GitFixture()
        self.addCleanup(self.fixture.close)
        self.base = self.fixture.accepted
        self.head = self.fixture.commit({b"docs/new.md": ("100644", b"new\n")})
        tree = self.fixture.repo.commit(self.head).tree
        self.synthetic = self.fixture.repo.run("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit-tree", tree, "-p", self.base, "-p", self.head, "-m", "Synthetic").strip().decode()
        self.fixture.repo.run("update-ref", "refs/heads/main", self.synthetic)
        self.event_path = self.fixture.root / "event.json"
        self.event = {"number": 999, "repository": {"full_name": REPOSITORY}, "pull_request": {
            "head": {"sha": self.head}, "base": {"sha": self.base, "ref": "main", "repo": {"full_name": REPOSITORY}}}}
        self.env = {"GITHUB_ACTIONS": "true", "GITHUB_REPOSITORY": REPOSITORY,
                    "GITHUB_SHA": self.synthetic, "GITHUB_REF": "refs/pull/999/merge",
                    "GITHUB_EVENT_NAME": "pull_request", "GITHUB_EVENT_PATH": str(self.event_path),
                    "GITHUB_RUN_ID": "1234", "GITHUB_RUN_ATTEMPT": "1"}

    def capture(self, candidate=None):
        self.event_path.write_text(json.dumps(self.event), encoding="utf-8")
        with mock.patch.dict(os.environ, self.env):
            return capture_context(self.fixture.repo, candidate or self.synthetic)

    def assert_context_error(self, callback):
        with self.assertRaises(HardeningError) as error:
            callback()
        self.assertEqual("E_CONTEXT", error.exception.code)

    def test_genuine_pr_positive(self):
        ctx = self.capture()
        require_pr_acceptance(ctx, head=self.head, base=self.base, synthetic=self.synthetic)
        self.assertEqual(self.synthetic, ctx.checked_sha)
        self.assertEqual("canonical_commit_objects", ctx.scope)

    def test_ci_03_wrong_checkout_context(self):
        self.assert_context_error(lambda: self.capture(self.head))
        self.event["pull_request"]["head"]["sha"] = self.base
        self.assert_context_error(self.capture)
        self.event["pull_request"]["head"]["sha"] = self.head
        self.env["GITHUB_REF"] = "refs/heads/main"
        self.assert_context_error(self.capture)

    def test_previous_head_and_base_reports_rejected_unit_controls(self):
        # These controls do not discharge the required live CI-04/CI-05 exercises.
        ctx = self.capture()
        self.assert_context_error(lambda: require_pr_acceptance(ctx, head=self.base, base=self.base, synthetic=self.synthetic))
        self.assert_context_error(lambda: require_pr_acceptance(ctx, head=self.head, base=self.head, synthetic=self.synthetic))
        for field, value in (("repository", "other/repository"), ("accepted_release", "0" * 40), ("run_id", True)):
            forged = dict(asdict(ctx), **{field: value})
            self.assert_context_error(lambda: require_pr_acceptance(forged, head=self.head, base=self.base, synthetic=self.synthetic))

    def test_ci_09_manual_not_pr_acceptance(self):
        self.env.update(GITHUB_EVENT_NAME="workflow_dispatch", GITHUB_REF="refs/heads/maintenance")
        ctx = self.capture()
        self.assertEqual("workflow_dispatch", ctx.event)
        self.assert_context_error(lambda: require_pr_acceptance(ctx, head=self.head, base=self.base, synthetic=self.synthetic))
        report = self.fixture.root / ".hardening-reports" / "manual-context.json"
        with mock.patch.dict(os.environ, self.env):
            result = context_cli(["--repo", str(self.fixture.root),
                                  "--event-file", str(self.event_path), "--report", str(report)])
        self.assertEqual(1, result)
        payload = json.loads(report.read_bytes())
        self.assertEqual("FAIL", payload["status"])
        self.assertEqual("E_CONTEXT", payload["error_code"])

    def test_push_positive_and_after_binding(self):
        self.env.update(GITHUB_EVENT_NAME="push", GITHUB_REF="refs/heads/main")
        self.event.update(ref="refs/heads/main", after=self.synthetic)
        self.assertEqual("push", self.capture().event)
        self.event["after"] = self.head
        self.assert_context_error(self.capture)

    def test_local_cannot_fabricate_ci_event(self):
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "false"}):
            ctx = capture_context(self.fixture.repo, self.synthetic)
            self.assertEqual("local", ctx.event)
            self.assertEqual(self.synthetic, ctx.checked_sha)
            self.assert_context_error(lambda: capture_context(self.fixture.repo, self.synthetic, self.event_path))
            for stale in (self.head, self.base):
                with self.subTest(stale=stale):
                    self.assert_context_error(lambda: capture_context(self.fixture.repo, stale))
            advanced = self.fixture.commit({b"docs/newer.md": ("100644", b"later checkout\n")},
                                           parent=self.synthetic)
            self.fixture.repo.run("update-ref", "refs/heads/main", advanced)
            self.assertEqual(advanced, capture_context(self.fixture.repo, advanced).checked_sha)
            self.assert_context_error(lambda: capture_context(self.fixture.repo, self.synthetic))
