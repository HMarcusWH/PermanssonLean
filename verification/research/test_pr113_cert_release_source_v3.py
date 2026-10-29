"""Authenticated CERT PR identity requires actual B/H/M and M113 ancestry."""
import unittest
import pr113_cert_release_source_v3 as v3
from release_target import B113

H113 = "a"*40
M113 = "b"*40
B = "c"*40
H = "d"*40
M = "e"*40


class ReleaseTargetTests(unittest.TestCase):
    def git(self, *a):
        if a[:2] == ("cat-file", "-t"):
            return "commit"
        if a == ("show", "-s", "--format=%P", M113):
            return B113+" "+H113
        if a == ("show", "-s", "--format=%P", M):
            return B+" "+H
        if a[0] == "rev-parse" and a[1].endswith("^{tree}"):
            return "source_tree"
        if a == ("merge-base", "--is-ancestor", M113, B):
            return ""
        return "not expected"

    def original(self, merged=True):
        return {"number":113,"state":"closed" if merged else "open",
                "merged":merged,"merge_commit_sha":M113 if merged else None,
                "head":{"sha":H113}}

    def cert(self, merged=True):
        return {"number":115,"state":"closed" if merged else "open",
                "merged":merged,"merge_commit_sha":M if merged else None,
                "head":{"sha":H,"ref":"research/cert-original",
                        "repo":{"full_name":"HMarcusWH/PermanssonLean"}},
                "base":{"sha":B,"ref":"main",
                        "repo":{"full_name":"HMarcusWH/PermanssonLean"}}}

    def live(self, url):
        if url == "/pulls/113":
            return self.original()
        if url == "/pulls/115":
            return self.cert()
        if url == "/commits/"+H+"/pulls?per_page=100":
            return [self.cert()]
        raise AssertionError(url)

    def test_original_and_cert_merge_targets_distinct(self):
        self.assertEqual(v3.source_pr(B113,H113,M113,git=self.git,live=self.live)[0],113)
        self.assertEqual(v3.source_pr(B,H,M,git=self.git,live=self.live)[0],115)

    def test_merged_CERT_base_display_can_move_without_changing_git_parents(self):
        def advanced(url):
            if url == "/pulls/115":
                updated = self.cert()
                updated["base"]["sha"] = "f"*40
                return updated
            return self.live(url)
        self.assertEqual(v3.source_pr(B,H,M,git=self.git,live=advanced)[0],115)

    def test_wrong_merge_or_ancestry_rejected(self):
        with self.assertRaises(v3.ReleaseSourceError):
            v3.source_pr(B,H,"f"*40,git=self.git,live=self.live)
        def wrong_git(*a):
            if a[:2] == ("merge-base","--is-ancestor"):
                return "not descendant"
            return self.git(*a)
        with self.assertRaises(v3.ReleaseSourceError):
            v3.source_pr(B,H,M,git=wrong_git,live=self.live)

    def test_original_current_pr_not_secretly_merged(self):
        def live(url):
            if url == "/pulls/113":
                return self.original(False)
            return self.live(url)
        self.assertEqual(v3.source_pr(B113,H113,git=self.git,live=live)[0],113)
        with self.assertRaises(v3.ReleaseSourceError):
            v3.source_pr(B113,H113,M113,git=self.git,live=live)

    def test_other_pr_number_or_wrong_repo_rejected(self):
        for edit in ({"number":114},
                     {"head":{"sha":H,"ref":"research/cert-original",
                              "repo":{"full_name":"untrusted/repo"}}}):
            def tampered(url):
                if url == "/pulls/115":
                    return {**self.cert(),**edit}
                return self.live(url)
            with self.assertRaises(v3.ReleaseSourceError):
                v3.source_pr(B,H,M,git=self.git,live=tampered)


if __name__ == "__main__":
    unittest.main()
