"""Source event topology adversaries. These tests never approve historical CI."""
import json
import unittest

from pr113_lifecycle_source_v3 import actual_source, LifecycleError
from release_target import B113

H113 = "b" * 40
S113 = "c" * 40
M113 = "d" * 40
NEXT_H = "e" * 40
NEXT_S = "f" * 40
LATER_M = "a" * 40


class LifecycleTests(unittest.TestCase):
    def example(self, *, number=113, event_name="pull_request"):
        self.current = S113 if number == 113 else NEXT_S
        self.base = B113 if number == 113 else M113
        self.head = H113 if number == 113 else NEXT_H
        if event_name == "push":
            self.current = LATER_M
        self.env = {
            "GITHUB_ACTIONS": "true",
            "GITHUB_REPOSITORY": "HMarcusWH/PermanssonLean",
            "GITHUB_EVENT_NAME": event_name,
            "GITHUB_REF": ("refs/pull/" + str(number) + "/merge"
                           if event_name == "pull_request" else "refs/heads/main"),
            "GITHUB_SHA": self.current,
            "GITHUB_JOB": "research",
            "GITHUB_WORKFLOW": "Research Lean",
            "GITHUB_RUN_ID": "1000",
            "GITHUB_RUN_ATTEMPT": "1",
        }
        self.pr = {
            "number": number,
            "repository": {"full_name": "HMarcusWH/PermanssonLean"},
            "pull_request": {
                "base": {"ref": "main", "sha": self.base,
                         "repo": {"full_name": "HMarcusWH/PermanssonLean"}},
                "head": {"ref": ("research/final-mathematical-closure"
                                 if number == 113 else "research/cert-proof"),
                         "sha": self.head,
                         "repo": {"full_name": "HMarcusWH/PermanssonLean"}},
            },
        }
        if event_name == "push":
            self.pr = {"repository": {"full_name": "HMarcusWH/PermanssonLean"},
                       "after": self.current, "ref": "refs/heads/main"}

    def git(self, *arguments):
        if arguments == ("rev-parse", "HEAD"):
            return self.current
        if arguments[0:2] == ("cat-file", "-t"):
            return "commit"
        if arguments == ("show", "-s", "--format=%P", M113):
            return B113 + " " + H113
        if arguments == ("show", "-s", "--format=%P", self.current):
            return self.base + " " + self.head
        if arguments[0:2] == ("rev-parse", M113 + "^{tree}"):
            return "x"
        if arguments[0:2] == ("rev-parse", H113 + "^{tree}"):
            return "x"
        if arguments[0:2] == ("rev-parse", self.current + "^{tree}"):
            return "x"
        if arguments[0:2] == ("rev-parse", self.head + "^{tree}"):
            return "x"
        if arguments[0:2] == ("merge-base", "--is-ancestor"):
            return "" if arguments[2] in (M113, LATER_M) else "wrong"
        raise ValueError("unexpected Git probe: " + repr(arguments))

    def live(self, path):
        if path == "/branches/main":
            return {"commit": {"sha": (self.base
                    if self.env["GITHUB_EVENT_NAME"] == "pull_request"
                    else self.current)}}
        if path == "/pulls/113":
            if self.base == B113:
                return {"number": 113, "merged": False,
                        "base": {"sha": B113}, "head": {"sha": H113}}
            return {"number": 113, "state": "closed", "merged": True,
                    "head": {"sha": H113}, "merge_commit_sha": M113}
        if path.startswith("/pulls/"):
            return {"number": int(path.rsplit("/", 1)[1]), "merged": False,
                    "base": {"sha": self.base}, "head": {"sha": self.head}}
        raise ValueError(path)

    def invoke(self):
        return actual_source(env=self.env,
                             event_bytes=json.dumps(self.pr).encode(),
                             git=self.git, live=self.live)

    def test_original_required_PR113_is_source_only(self):
        self.example()
        receipt = self.invoke()
        self.assertEqual(receipt["phase"], "initial_113_pr")
        self.assertFalse(receipt["required_ci_accepted"])

    def test_successor_requires_authentic_merge_ancestry(self):
        self.example(number=115)
        self.assertEqual(self.invoke()["phase"], "main_descendant_pr")
        old_git = self.git
        def invalid_git(*args):
            if args[:2] == ("merge-base", "--is-ancestor"):
                return "not an ancestor"
            return old_git(*args)
        with self.assertRaises(LifecycleError):
            actual_source(env=self.env, event_bytes=json.dumps(self.pr).encode(),
                          git=invalid_git, live=self.live)

    def test_current_main_descendant_is_not_misclassified_as_M113(self):
        self.example(number=115, event_name="push")
        receipt = self.invoke()
        self.assertEqual(receipt["phase"], "main_descendant_push")
        self.assertFalse(receipt["publication_authorized"])

    def test_foreign_repo_and_wrong_pr_ref_reject(self):
        self.example(number=115)
        self.pr["repository"]["full_name"] = "attacker/forged"
        with self.assertRaises(LifecycleError):
            self.invoke()
        self.pr["repository"]["full_name"] = "HMarcusWH/PermanssonLean"
        self.env["GITHUB_REF"] = "refs/pull/113/merge"
        with self.assertRaises(LifecycleError):
            self.invoke()


if __name__ == "__main__":
    unittest.main()
