"""Original21 producer branch identity must come from real GitHub/Git ancestry."""
import unittest

import pr113_producer_target_v3 as subject
from release_target import B113

H113 = "b"*40
M113 = "c"*40
B_CERT = "d"*40
H_CERT = "e"*40


class ProducerBranchTests(unittest.TestCase):
    def env(self, head, branch, cert=""):
        return {
            "GITHUB_ACTIONS":"true",
            "GITHUB_REPOSITORY":"HMarcusWH/PermanssonLean",
            "GITHUB_SHA":head, "GITHUB_EVENT_NAME":"workflow_dispatch",
            "GITHUB_REF":"refs/heads/"+branch,
            "PERMANSSON_CERT_PR_NUMBER":cert,
        }

    def git(self, *args):
        if args == ("rev-parse", "HEAD"):
            return self.head
        if args[:2] == ("cat-file", "-t"):
            return "commit"
        if args == ("show", "-s", "--format=%P", M113):
            return B113+" "+H113
        if args[0] == "rev-parse" and args[1].endswith("^{tree}"):
            return "reviewed_tree"
        if args[:2] == ("merge-base", "--is-ancestor"):
            return ""
        raise AssertionError(args)

    def live(self, endpoint):
        if endpoint == "/pulls/113":
            if self.head == H113:
                return {"number":113,"merged":False,
                        "head":{"sha":H113,"ref":subject.BRANCH113},
                        "base":{"sha":B113}}
            return {"number":113,"state":"closed","merged":True,
                    "merge_commit_sha":M113,"head":{"sha":H113}}
        if endpoint == "/pulls/115":
            return {"number":115,"state":"open","merged":False,
                    "head":{"sha":H_CERT,"ref":"research/cert-real",
                            "repo":{"full_name":"HMarcusWH/PermanssonLean"}},
                    "base":{"sha":B_CERT,"ref":"main"}}
        if endpoint == "/branches/main":
            return {"commit":{"sha":B_CERT}}
        raise AssertionError(endpoint)

    def test_original_and_successor_are_distinct_authentic_targets(self):
        self.head = H113
        self.assertEqual(subject.authenticated_producer_branch(
            H113, env=self.env(H113,subject.BRANCH113),git=self.git,live=self.live),
            subject.BRANCH113)
        self.head = H_CERT
        self.assertEqual(subject.authenticated_producer_branch(
            H_CERT,env=self.env(H_CERT,"research/cert-real","115"),
            git=self.git,live=self.live), "research/cert-real")

    def test_missing_or_wrong_cert_PR_does_not_borrow_original_branch(self):
        self.head = H_CERT
        for env in (self.env(H_CERT,"research/cert-real"),
                    self.env(H_CERT,"research/cert-real","113"),
                    self.env(H_CERT,"research/cert-real","114"),
                    self.env(H_CERT,"research/cert-fake","115"),
                    self.env(H113,"research/cert-real","115")):
            with self.subTest(env=env), self.assertRaises(subject.ProducerTargetError):
                subject.authenticated_producer_branch(
                    H_CERT, env=env, git=self.git, live=self.live)

    def test_wrong_ancestry_must_fail_even_with_live_pr(self):
        self.head = H_CERT
        def wrong_git(*args):
            if args[:2] == ("merge-base","--is-ancestor"):
                return "not ancestor"
            return self.git(*args)
        with self.assertRaises(subject.ProducerTargetError):
            subject.authenticated_producer_branch(
                H_CERT,env=self.env(H_CERT,"research/cert-real","115"),
                git=wrong_git,live=self.live)
