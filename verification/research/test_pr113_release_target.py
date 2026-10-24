"""Synthetic Git/GitHub target verification; never owner review or approval."""
import copy
import json
import unittest
from unittest import mock

import release_target as target


B = target.B113
H = "a" * 40
S = "b" * 40
M = "c" * 40
BC = M
HC = "d" * 40
SC = "e" * 40


def fake_intent():
    return {
        "format": target.FORMAT,
        "repository": target.REPOSITORY,
        "original_base_sha": B,
        "historical_T_sha": target.T,
        "infrastructure_pr": 113,
        "certification_pr": None,
        "status": "CERTIFICATION_NOT_YET_BOUND",
        "independent_security_review": False,
        "independent_mathematical_review": False,
        "publication_authorized": False,
    }


def fake_target(cert=False):
    return {
        "format": target.BINDING_FORMAT,
        "phase": "certification_premerge" if cert else "infrastructure_premerge",
        "repository": target.REPOSITORY,
        "pr_number": 116 if cert else 113,
        "branch": "research/certification-mathematical" if cert
                  else "research/final-mathematical-closure",
        "base_sha": BC if cert else B,
        "head_sha": HC if cert else H,
        "synthetic_sha": SC if cert else S,
        "infrastructure_merge_sha": M if cert else None,
    }


def fake_apis(cert=False):
    binding = fake_target(cert)
    base, head, syn = (binding[k] for k in (
        "base_sha", "head_sha", "synthetic_sha"))
    p = {
        "number": binding["pr_number"], "state": "open",
        "merged": False, "draft": True,
        "base": {"ref": "main", "sha": base},
        "head": {"ref": binding["branch"], "sha": head,
                 "repo": {"full_name": target.REPOSITORY}},
        "merge_commit_sha": syn,
    }
    lookup = {
        "/branches/main": {"commit": {"sha": base}},
        "/pulls/" + str(binding["pr_number"]): p,
    }
    if cert:
        lookup["/pulls/113"] = {
            "number": 113, "merged": True, "merge_commit_sha": M,
            "head": {"sha": H},
        }

    def gh(path):
        return lookup[path]

    def git(*args):
        if args[:2] == ("cat-file", "-t"):
            return "commit"
        if args[:3] == ("show", "-s", "--format=%P"):
            return base + " " + head
        if args[:2] == ("rev-parse", syn + "^{tree}"):
            return "same_tree"
        if args[:2] == ("rev-parse", head + "^{tree}"):
            return "same_tree"
        if args[:2] == ("rev-parse", M + "^{tree}"):
            return "original_merged_tree"
        if args[:2] == ("rev-parse", H + "^{tree}"):
            return "original_merged_tree"
        if args == ("merge-base", "--is-ancestor", M, BC):
            return ""
        raise AssertionError("unexpected Git op " + repr(args))
    return gh, git, lookup


class ReleaseTargetTests(unittest.TestCase):
    def test_intent_is_unbound_and_never_self_approves(self):
        target.intent_contract(fake_intent())
        for mutation in (
            lambda x: x.update(certification_pr=115),
            lambda x: x.update(publication_authorized=True),
            lambda x: x.update(original_base_sha="0" * 40),
            lambda x: x.update(fake_approval=True),
            lambda x: x.update(independent_security_review=True),
        ):
            with self.subTest(str(mutation)), self.assertRaises(target.TargetError):
                obj = fake_intent()
                mutation(obj)
                target.intent_contract(obj)

    def test_genuine_infrastructure_target_is_bound_but_unaccepted(self):
        gh, git, _ = fake_apis()
        r = target.bind(fake_target(), intent=fake_intent(), git=git, live=gh)
        self.assertEqual(r["status"], "GENUINE_PR_AND_GIT_IDENTITY_BOUND_NOT_REVIEWED")
        self.assertEqual(r["pr_number"], 113)
        self.assertFalse(r["independent_security_review"])
        self.assertFalse(r["merge_authorized"])

    def test_certification_requires_real_M113_and_new_pr(self):
        gh, git, api = fake_apis(cert=True)
        r = target.bind(fake_target(True), intent=fake_intent(), git=git, live=gh)
        self.assertEqual(r["phase"], "certification_premerge")
        self.assertFalse(r["independent_mathematical_review"])
        for bad in (113, 114, 0):
            row = fake_target(True)
            row["pr_number"] = bad
            with self.assertRaises(target.TargetError):
                target.candidate_bindings(row)
        api["/pulls/113"]["merged"] = False
        with self.assertRaises(target.TargetError):
            target.bind(fake_target(True), intent=fake_intent(), git=git, live=gh)

    def test_certification_wrong_parent_or_stale_pr_blocks(self):
        gh, git, api = fake_apis(True)
        api["/pulls/116"]["head"]["sha"] = "f" * 40
        with self.assertRaises(target.TargetError):
            target.bind(fake_target(True), intent=fake_intent(), git=git, live=gh)
        gh, git, api = fake_apis(True)
        api["/pulls/113"]["merge_commit_sha"] = "0" * 40
        with self.assertRaises(target.TargetError):
            target.bind(fake_target(True), intent=fake_intent(), git=git, live=gh)

    def test_pr_borrowing_base_branch_state_and_foreign_repo_block(self):
        for modifier in (
            lambda p: p["head"].update(ref="research/foreign"),
            lambda p: p["base"].update(sha="0" * 40),
            lambda p: p["head"]["repo"].update(full_name="other/PermanssonLean"),
            lambda p: p.update(merged=True),
            lambda p: p.update(draft=False),
            lambda p: p.update(merge_commit_sha="f" * 40),
        ):
            gh, git, api = fake_apis()
            modifier(api["/pulls/113"])
            with self.subTest(modifier=modifier), self.assertRaises(target.TargetError):
                target.bind(fake_target(), intent=fake_intent(), git=git, live=gh)

    def test_synthetic_parent_or_source_tree_mismatch_blocks(self):
        gh, git, _ = fake_apis()
        def wrong_parents(*args):
            if args[:3] == ("show", "-s", "--format=%P"):
                return H + " " + B
            return git(*args)
        with self.assertRaises(target.TargetError):
            target.bind(fake_target(), intent=fake_intent(),
                        git=wrong_parents, live=gh)
        def wrong_tree(*args):
            if args == ("rev-parse", S + "^{tree}"):
                return "changed"
            return git(*args)
        with self.assertRaises(target.TargetError):
            target.bind(fake_target(), intent=fake_intent(),
                        git=wrong_tree, live=gh)

    def test_extra_runtime_approval_fields_never_accepted(self):
        b = fake_target()
        b["reviewer_approved"] = True
        with self.assertRaises(target.TargetError):
            target.candidate_bindings(b)
        b = fake_target(True)
        b["infrastructure_merge_sha"] = None
        with self.assertRaises(target.TargetError):
            target.candidate_bindings(b)

    def test_git_source_intent_not_dirty_checkout(self):
        intent = fake_intent()
        calls = []
        def fake_git(*args):
            calls.append(args)
            if args[:2] == ("cat-file", "-t"):
                return "commit"
            if args[:2] == ("show", B + ":" + target.INTENT_PATH):
                return json.dumps(intent)
            raise AssertionError(args)
        self.assertEqual(target.exact_intent(B, git=fake_git), intent)
        self.assertTrue(any(a[0] == "show" for a in calls))


if __name__ == "__main__":
    unittest.main()
