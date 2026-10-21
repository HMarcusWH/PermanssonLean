"""No self-claimed CI or reviewer receipt can pass final B/H/S/M authentication.

These tests use forged stand-ins only to challenge the gate's logic; they
do not create or claim real approvals, CI checks, or merged commits.
"""
from __future__ import annotations

from pathlib import Path
import sys
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verification/research"))
import final_closure_authenticate as source

B = source.BASE
H = "a" * 40
S = "b" * 40
M = "c" * 40
T = "d" * 40


def genuine_shape():
    checked = [
        {"name": name, "id": i + 1, "head_sha": H,
         "status": "completed", "conclusion": "success"}
        for i, name in enumerate(sorted(source.REQUIRED))
    ]
    pr = {
        "number": 113, "merged": True,
        "base": {"sha": B}, "head": {"sha": H},
        "merge_commit_sha": M, "user": {"login": "owner"},
    }
    reviews = [{
        "id": 42, "state": "APPROVED", "commit_id": H,
        "submitted_at": "2026-10-21T00:00:00Z",
        "user": {"login": "independent_reviewer"},
    }]
    receipts = {
        "base_sha": B, "head_sha": H, "synthetic_sha": S,
        "merged_main_sha": M, "source_bound_ci": [
            {"name": x["name"], "id": x["id"], "head_sha": x["head_sha"]}
            for x in checked
        ],
        "independent_source_reviews": [{"id": 42}],
    }
    return receipts, pr, checked, reviews


def git_stub(*args):
    if args[:2] == ("cat-file", "-t"):
        return "commit"
    if args[:3] == ("show", "-s", "--format=%P"):
        return B + " " + H
    if args[:1] == ("rev-parse",):
        return T
    if args[:2] == ("merge-base", "--is-ancestor"):
        return ""
    raise AssertionError("unexpected Git query: " + repr(args))


class FinalSourceAuthenticationTests(unittest.TestCase):
    def _invoke(self, receipts, pr, checks, reviews):
        def github_stub(path):
            if path == "/pulls/113":
                return pr
            if path == "/pulls/113/reviews?per_page=100":
                return reviews
            if path == "/commits/" + H + "/check-runs?per_page=100":
                return {"check_runs": checks}
            raise AssertionError("unexpected endpoint " + path)
        with mock.patch.object(source, "git", side_effect=git_stub), \
             mock.patch.object(source, "live", side_effect=github_stub):
            return source.verify_source(receipts)

    def test_boolean_authenticated_flag_never_suffices(self):
        with self.assertRaises(source.AuthenticationError):
            source.verify_source({"authenticated": True})

    def test_forged_non_git_synthetic_parents_rejected(self):
        receipts, pr, checks, reviews = genuine_shape()
        with mock.patch.object(source, "git", side_effect=lambda *args:
                "0" * 40 + " " + H if args[:3] == ("show", "-s", "--format=%P")
                else git_stub(*args)), \
             mock.patch.object(source, "live", return_value=pr):
            with self.assertRaises(source.AuthenticationError):
                source.verify_source(receipts)

    def test_source_head_ci_must_be_complete(self):
        receipts, pr, checks, reviews = genuine_shape()
        with self.assertRaises(source.AuthenticationError):
            self._invoke(receipts, pr, checks[1:], reviews)

    def test_author_approval_is_not_independent_review(self):
        receipts, pr, checks, reviews = genuine_shape()
        reviews[0]["user"]["login"] = "owner"
        with self.assertRaises(source.AuthenticationError):
            self._invoke(receipts, pr, checks, reviews)

    def test_stale_review_commit_is_rejected(self):
        receipts, pr, checks, reviews = genuine_shape()
        reviews[0]["commit_id"] = "9" * 40
        with self.assertRaises(source.AuthenticationError):
            self._invoke(receipts, pr, checks, reviews)

    def test_claimed_ci_id_must_match_live_check(self):
        receipts, pr, checks, reviews = genuine_shape()
        receipts["source_bound_ci"][0]["id"] = 999999
        with self.assertRaises(source.AuthenticationError):
            self._invoke(receipts, pr, checks, reviews)

    def test_live_merge_and_read_only_checks_are_all_bound(self):
        receipts, pr, checks, reviews = genuine_shape()
        got = self._invoke(receipts, pr, checks, reviews)
        self.assertEqual((got["B"], got["H"], got["S"], got["M"]), (B, H, S, M))
        self.assertEqual(got["reviewer_ids"], {42})


if __name__ == "__main__":
    unittest.main()
