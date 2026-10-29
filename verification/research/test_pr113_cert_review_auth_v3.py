"""Mock integration: real PR113 and later CERT may not borrow review scopes."""
import unittest
from unittest import mock

import final_closure_authenticate as source
from release_target import B113

H113="a"*40
M113="b"*40
B="c"*40
H="d"*40
S="e"*40
M="f"*40


def git(*args):
    if args[:2] == ("cat-file", "-t"):
        return "commit"
    if args == ("show", "-s", "--format=%P", M113):
        return B113+" "+H113
    if args == ("show", "-s", "--format=%P", S):
        return B+" "+H
    if args == ("show", "-s", "--format=%P", M):
        return B+" "+H
    if args[0] == "rev-parse" and args[1].endswith("^{tree}"):
        return "same_tree"
    if args[:2] == ("merge-base", "--is-ancestor"):
        return ""
    return "unexpected"


def pr(num):
    if num==113:
        return {"number":113,"state":"closed","merged":True,
                "head":{"sha":H113},"merge_commit_sha":M113}
    return {"number":115,"state":"closed","merged":True,
            "merge_commit_sha":M,"user":{"login":"HMarcusWH"},
            "head":{"sha":H,"ref":"research/cert-real",
                    "repo":{"full_name":"HMarcusWH/PermanssonLean"}},
            "base":{"sha":B,"ref":"main",
                    "repo":{"full_name":"HMarcusWH/PermanssonLean"}}}


def live(endpoint):
    if endpoint == "/pulls/113":
        return pr(113)
    if endpoint == "/pulls/115":
        return pr(115)
    if endpoint == "/commits/"+H+"/pulls?per_page=100":
        return [pr(115)]
    raise AssertionError(endpoint)


class AuthenticatedCertMergeTests(unittest.TestCase):

    def test_duplicate_GitHub_review_field_rejected_before_acceptance(self):
        import json
        sha = "e"*64
        payload = ('{"head_sha":"' + H + '","head_sha":"' + H +
                   '","evidence_bundle_sha256":"' + sha +
                   '","receipt_payload_sha256":"' + sha +
                   '","cases":{},"claims":[]}')
        review = {"id":991,"state":"APPROVED","commit_id":H,
                  "submitted_at":"2026-10-27T01:00:00Z",
                  "user":{"login":"independent-reviewer"},
                  "body":source.REVIEW_PREFIX+" "+payload}
        with mock.patch.object(source,"paginate",return_value=[review]), \
             mock.patch.object(source,"reviewer_authorized",return_value=True):
            with self.assertRaises(source.AuthenticationError):
                source.authenticate_scoped_reviews(
                    H,"HMarcusWH",sha,[{"id":991}],sha,pr_number=115)

    def test_edited_scholarly_comment_does_not_become_approval(self):
        import json
        pr = {"merged_at": "2026-10-27T01:00:00Z",
              "user": {"login": "HMarcusWH"}}
        claim = {
            "head_sha": H, "merged_main_sha": M,
            "pdf_sha256": "e"*64,
            "pages": {"page-1.png": "f"*64},
            "approved_claim_ids": ["Q1"],
            "scholarly_review": "APPROVED",
            "all_pages_visually_inspected": True,
        }
        comment = {
            "id": 777, "user": {"login": "independent-scholarly"},
            "created_at": "2026-10-27T01:05:00Z",
            "updated_at": "2026-10-27T02:05:00Z",
            "body": source.SCHOLARLY_PREFIX + json.dumps(claim),
        }
        with mock.patch.object(source, "paginate", return_value=[comment]), \
             mock.patch.object(source, "reviewer_authorized", return_value=True):
            with self.assertRaises(source.AuthenticationError):
                source.authentic_scholarly_attestations(
                    pr, H, M, pr_number=115)

    def test_v2_source_gate_uses_real_cert_not_original_pr_reviewer_records(self):
        def checks(commit):
            return {name:{"id":i+1,"head_sha":commit,
                          "status":"completed","conclusion":"success"}
                    for i,name in enumerate(sorted(source.REQUIRED))}
        receipt={"base_sha":B,"head_sha":H,"synthetic_sha":S,
                 "merged_main_sha":M,
                 "source_bound_ci":[{"name":k,"id":v["id"],"head_sha":H}
                     for k,v in checks(H).items()],
                 "merged_bound_ci":[{"name":k,"id":v["id"],"head_sha":M}
                     for k,v in checks(M).items()],
                 "evidence_bundle_sha256":"0"*64,
                 "independent_source_reviews":[]}
        with mock.patch.object(source,"git",side_effect=git), \
             mock.patch.object(source,"live",side_effect=live), \
             mock.patch.object(source,"authenticated_checks",side_effect=checks), \
             mock.patch.object(source,"authenticate_scoped_reviews",
                               return_value={123:{"claims":["Q1"]}}) as reviewed, \
             mock.patch.object(source,"authentic_scholarly_attestations",
                               return_value=[]) as scholarly:
            result=source.verify_merged_v2(receipt)
        self.assertEqual(result["M"],M)
        self.assertEqual(result["H"],H)
        self.assertEqual(reviewed.call_args.kwargs["pr_number"],115)
        self.assertEqual(scholarly.call_args.kwargs["pr_number"],115)
        self.assertEqual(len(result["checks"]),12)


if __name__ == "__main__":
    unittest.main()
