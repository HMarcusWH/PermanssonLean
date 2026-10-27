"""Mock-only source-input checks. No GitHub or mathematical approval implied."""
import json
import unittest

import pr113_ci_producer_source_v3 as source

H = "a" * 40
REPO = "HMarcusWH/PermanssonLean"


def event(kind, mode, branch, *, cert=""):
    env = {
        "GITHUB_ACTIONS": "true", "GITHUB_REPOSITORY": REPO,
        "GITHUB_SHA": H, "GITHUB_REF": "refs/heads/" + branch,
        "GITHUB_EVENT_NAME": kind,
        "PERMANSSON_CERT_PR_NUMBER": cert,
        "PR113_REQUESTED_SOURCE_HEAD": H if kind == "workflow_dispatch" else "",
        "PR113_REQUESTED_RUN_MODE": mode if kind == "workflow_dispatch" else "",
    }
    payload = {"repository": {"full_name": REPO}}
    if kind == "workflow_dispatch":
        payload["inputs"] = {
            "run_mode": mode, "source_head": H, "cert_pr_number": cert}
    else:
        payload["ref"] = env["GITHUB_REF"]
        payload["after"] = H
    return env, payload


class ProducerSourceTests(unittest.TestCase):
    def check(self, env, payload, mode):
        return source.authenticate(H, mode, env=env,
                   event_data=json.dumps(payload).encode(),
                   branch_check=lambda head, *, env: env["GITHUB_REF"].split(
                       "refs/heads/", 1)[1])

    def test_original_push_and_future_cert_dispatch_are_unapproved(self):
        env, payload = event("push", "source_controls",
                             "research/final-mathematical-closure")
        receipt = self.check(env, payload, "source_controls")
        self.assertEqual(receipt["pr_number"], 113)
        self.assertFalse(receipt["case_acceptance"])
        env, payload = event("workflow_dispatch", "source_controls",
                             "research/cert-real", cert="115")
        receipt = self.check(env, payload, "source_controls")
        self.assertEqual(receipt["pr_number"], 115)
        self.assertFalse(receipt["claim_acceptance"])
        env, payload = event("workflow_dispatch", "reviewed_legacy20",
                             "research/cert-real", cert="115")
        receipt = self.check(env, payload, "reviewed_legacy20")
        self.assertFalse(receipt["reviewer_selected"])

    def test_borrowed_pr_head_mode_and_repo_fail(self):
        env, payload = event("workflow_dispatch", "reviewed_legacy20",
                             "research/cert-real", cert="115")
        for change in (
            lambda e, p: p["inputs"].update(source_head="b"*40),
            lambda e, p: p["inputs"].update(run_mode="source_controls"),
            lambda e, p: p["inputs"].update(cert_pr_number="116"),
            lambda e, p: p["repository"].update(full_name="attacker/foreign"),
            lambda e, p: e.update(GITHUB_SHA="c"*40),
        ):
            e = dict(env)
            p = json.loads(json.dumps(payload))
            change(e, p)
            with self.subTest(change=str(change)), self.assertRaises(
                    source.SourceDispatchError):
                self.check(e, p, "reviewed_legacy20")

    def test_legacy_replay_cannot_run_on_push(self):
        env, payload = event("push", "reviewed_legacy20",
                             "research/final-mathematical-closure")
        with self.assertRaises(source.SourceDispatchError):
            self.check(env, payload, "reviewed_legacy20")


if __name__ == "__main__":
    unittest.main()
