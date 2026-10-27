"""Synthetic GitHub ancestry fixtures; never authorizes historical evidence."""
import unittest

import pr113_reviewed_producer_branch_v3 as target
from release_target import B113

H113 = "a"*40
M113 = "b"*40
BASE = "c"*40
H = "d"*40
M = "e"*40
BRANCH = "research/cert-real"


class BoundBranchTests(unittest.TestCase):
    def git(self, *args):
        if args[:2] == ("cat-file", "-t"):
            return "commit"
        if args == ("show", "-s", "--format=%P", M113):
            return B113+" "+H113
        if args == ("show", "-s", "--format=%P", M):
            return BASE+" "+H
        if args[0] == "rev-parse" and args[1].endswith("^{tree}"):
            return "reviewed_tree"
        if args[:2] == ("merge-base", "--is-ancestor"):
            return ""
        raise AssertionError(args)

    def live(self, path):
        if path == "/pulls/113":
            return {"number":113,"state":"closed","merged":True,
                    "merge_commit_sha":M113,"head":{"sha":H113}}
        if path == "/branches/main":
            return {"commit":{"sha":BASE}}
        if path == "/commits/"+H+"/pulls?per_page=100":
            return [self.pr()]
        raise AssertionError(path)

    def pr(self):
        return {"number":115, "state":"closed", "merged":True,
                "merge_commit_sha":M,
                "head":{"ref":BRANCH,"sha":H,
                        "repo":{"full_name":"HMarcusWH/PermanssonLean"}},
                "base":{"sha":BASE,"ref":"main",
                        "repo":{"full_name":"HMarcusWH/PermanssonLean"}}}

    def test_original_branch_behavior_remains_but_cert_needs_real_ancestry(self):
        self.assertEqual(target.authentic_branch(H113,target.ORIGINAL_BRANCH),
                         target.ORIGINAL_BRANCH)
        self.assertEqual(target.authentic_branch(H,BRANCH,
                         live=self.live,git=self.git),BRANCH)

    def test_foreign_pr_wrong_number_branch_or_merge_fail(self):
        for patch in (
            {"number":114},
            {"merged":False,"state":"closed"},
            {"merge_commit_sha":"f"*40},
            {"head":{"ref":BRANCH,"sha":"f"*40,
                    "repo":{"full_name":"HMarcusWH/PermanssonLean"}}},
            {"head":{"ref":BRANCH,"sha":H,
                    "repo":{"full_name":"attacker/repo"}}},
        ):
            def invalid(path):
                value=self.live(path)
                if path.startswith("/commits/"):
                    value=[{**value[0],**patch}]
                return value
            with self.subTest(patch=patch),self.assertRaises(target.ProducerBranchError):
                target.authentic_branch(H,BRANCH,live=invalid,git=self.git)

    def test_missing_m113_ancestry_rejects(self):
        def wrong(*args):
            if args[:2] == ("merge-base","--is-ancestor"):
                return "not ancestor"
            return self.git(*args)
        with self.assertRaises(target.ProducerBranchError):
            target.authentic_branch(H,BRANCH,live=self.live,git=wrong)


if __name__ == "__main__":
    unittest.main()
