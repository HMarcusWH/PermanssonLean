"""Negative/positive v2 auth logic tests with mocked GitHub, NOT real approvals."""
import copy
import json
import unittest
from unittest import mock

import final_closure_authenticate as auth

B = auth.BASE
H = "a" * 40
S = "b" * 40
M = "c" * 40
T = "d" * 40
BUNDLE = "e" * 64


def fixture(merged=False):
    checks = [
        {"name": name, "head_sha": H, "id": i + 10,
         "status": "completed", "conclusion": "success",
         "app": {"slug": "github-actions"}}
        for i, name in enumerate(sorted(auth.REQUIRED))]
    integrated = [dict(c, head_sha=M, id=c["id"]+100) for c in checks]
    pr = {
        "number": 113, "state": "closed" if merged else "open",
        "merged": merged,
        "user": {"login": "author"},
        "head": {"sha": H}, "base": {"sha": "f"*40 if merged else B},
        "merge_commit_sha": M if merged else S,
    }
    reviews = [{
        "id": 88, "state": "APPROVED", "submitted_at": "2026-10-21T17:00:00Z",
        "commit_id": H, "user": {"login": "external"},
        "body": auth.REVIEW_PREFIX + " " +
        json.dumps({"head_sha": H, "evidence_bundle_sha256": BUNDLE,
                    "cases": {"C-01": "VERIFIED_SELECTED_SCOPE"},
                    "claims": ["Q1"]}, sort_keys=True),
    }]
    receipts = {
        "base_sha": B, "head_sha": H, "synthetic_sha": S,
        "merged_main_sha": M if merged else None,
        "evidence_bundle_sha256": BUNDLE,
        "source_bound_ci": [
            {"name": c["name"], "id": c["id"], "head_sha": H}
            for c in checks],
        "merged_bound_ci": [
            {"name": c["name"], "id": c["id"], "head_sha": M}
            for c in integrated],
        "independent_source_reviews": [{"id": 88}],
    }
    return receipts, pr, checks, integrated, reviews


class AuthenticationV2Tests(unittest.TestCase):
    def run_gate(self, *, merged=False, mutate=None):
        receipts, pr, checks, integrated, reviews = fixture(merged)
        parent_s = [B, H]
        parent_m = [B, H]
        trees = {"S": T, "M": T, "H": T}
        main_ref = B
        if mutate:
            mutate(receipts, pr, checks, integrated, reviews,
                   parent_s, parent_m, trees)

        def git(*parts):
            if parts[:2] == ("cat-file", "-t"):
                return "commit"
            if parts[:3] == ("show", "-s", "--format=%P"):
                return " ".join(parent_m if parts[3] == M else parent_s)
            if parts == ("rev-parse", "main"):
                return main_ref
            if parts[:1] == ("rev-parse",):
                value = parts[1].split("^")[0]
                return trees["M" if value == M else "S" if value == S else "H"]
            if parts[:2] == ("merge-base", "--is-ancestor"):
                return ""
            raise AssertionError("unexpected Git call " + repr(parts))

        def live(path):
            if path == "/pulls/113":
                return pr
            if path == "/pulls/113/reviews?per_page=100":
                return reviews
            if path.startswith("/commits/") and path.endswith("/check-runs?per_page=100"):
                sha = path.split("/")[2]
                return {"check_runs": integrated if sha == M else checks}
            raise AssertionError("unexpected GitHub endpoint " + path)

        with mock.patch.object(auth, "git", side_effect=git), \
             mock.patch.object(auth, "live", side_effect=live):
            if merged:
                return auth.verify_merged_v2(receipts)
            return auth.verify_premerge(receipts)

    def test_valid_mocked_premerge_review_scopes(self):
        outcome = self.run_gate()
        self.assertEqual(outcome["H"], H)
        self.assertEqual(outcome["review_scopes"][88]["cases"]["C-01"],
                         "VERIFIED_SELECTED_SCOPE")
        self.assertIsNone(outcome["M"])

    def test_valid_mocked_merged_exact_BH_and_integrated_checks(self):
        outcome = self.run_gate(merged=True)
        self.assertEqual(outcome["M"], M)
        self.assertEqual(len(outcome["integrated_checks"]), len(auth.REQUIRED))

    def test_fake_check_run_id_rejected(self):
        def mutate(r, p, c, i, reviews, ps, pm, ts):
            r["source_bound_ci"][0]["id"] = 9999
        with self.assertRaises(auth.AuthenticationError):
            self.run_gate(mutate=mutate)

    def test_stale_review_or_owner_approval_rejected(self):
        for mode in ("stale", "author", "wrong-digest"):
            def mutate(r, p, c, i, reviews, ps, pm, ts):
                if mode == "stale":
                    reviews[0]["commit_id"] = "f" * 40
                elif mode == "author":
                    reviews[0]["user"]["login"] = "author"
                else:
                    reviews[0]["body"] = reviews[0]["body"].replace(BUNDLE, "0"*64)
            with self.subTest(mode=mode):
                with self.assertRaises(auth.AuthenticationError):
                    self.run_gate(mutate=mutate)

    def test_synthetic_wrong_parent_rejected(self):
        def mutate(r, p, c, i, reviews, ps, pm, ts):
            ps[0] = "f"*40
        with self.assertRaises(auth.AuthenticationError):
            self.run_gate(mutate=mutate)

    def test_merged_wrong_parent_and_tree_rejected(self):
        for mode in ("parent", "tree"):
            def mutate(r, p, c, i, reviews, ps, pm, ts):
                if mode == "parent":
                    pm[0] = "f"*40
                else:
                    ts["M"] = "0"*40
            with self.subTest(mode=mode):
                with self.assertRaises(auth.AuthenticationError):
                    self.run_gate(merged=True, mutate=mutate)

    def test_changed_main_base_premerge_rejected(self):
        def mutate(r, p, c, i, reviews, ps, pm, ts):
            p["base"]["sha"] = "f"*40
        with self.assertRaises(auth.AuthenticationError):
            self.run_gate(mutate=mutate)

    def test_old_author_comment_cannot_authenticate(self):
        def mutate(r, p, c, i, reviews, ps, pm, ts):
            reviews[0]["state"] = "COMMENTED"
        with self.assertRaises(auth.AuthenticationError):
            self.run_gate(mutate=mutate)


if __name__ == "__main__":
    unittest.main()
