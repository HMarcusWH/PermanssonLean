"""Synthetic authorization fixtures; real GitHub review is still mandatory."""
import json
import unittest

import pr113_secure_security_review_v3 as gate
from infrastructure_acceptance import InfrastructureError
from release_target import B113

H = "a"*40
REVIEWER = "external-security-reviewer"
AUTHOR = "HMarcusWH"
RID = 2026


def fixture():
    att = {"head_sha": H, "workflow_sha256": "b"*64,
           "T_artifact_sha256":"c"*64,"A2_artifact_sha256":"d"*64,
           "original_base_sha": B113}
    policy={"format":"Permansson.InfrastructureReviewerAuthority.v1",
            "status":"OWNER_AUTHORIZED","owner":AUTHOR,
            "reviewers":[{"login":REVIEWER,"approved_by":AUTHOR,
                          "independence_disclosed":True}]}
    review={"id":RID,"state":"APPROVED","commit_id":H,
            "submitted_at":"2026-10-27T01:00:00Z",
            "user":{"login":REVIEWER},
            "body":gate.REVIEW_PREFIX + json.dumps(att)}
    return att, policy, review


class ExactSecurityReviewTests(unittest.TestCase):
    def check(self, changed=None):
        att,policy,review=fixture()
        if changed: changed(att,policy,review)
        return gate.approved_security_review(
            RID, AUTHOR, H, att, policy,
            paginate=lambda endpoint:[review])

    def test_full_source_authorization_shape_remains_live_review(self):
        self.assertIs(self.check(), True)

    def test_no_bool_ids_self_reviews_or_unauthorized_roles(self):
        att,policy,review=fixture()
        with self.assertRaises(InfrastructureError):
            gate.approved_security_review(True,AUTHOR,H,att,policy,
                                          paginate=lambda endpoint:[review])
        for mutate in (
            lambda a,p,r: r["user"].update(login=AUTHOR),
            lambda a,p,r: r.update(state="DISMISSED"),
            lambda a,p,r: r.update(commit_id="e"*40),
            lambda a,p,r: r.update(submitted_at=None),
            lambda a,p,r: p.update(status="UNCONFIGURED"),
            lambda a,p,r: p["reviewers"][0].update(independence_disclosed=False),
            lambda a,p,r: p["reviewers"].append(dict(p["reviewers"][0])),
            lambda a,p,r: a.update(workflow_sha256="f"*64),
        ):
            with self.subTest(mutate=str(mutate)), self.assertRaises(
                    InfrastructureError):
                self.check(mutate)

    def test_duplicates_unknown_fields_and_incomplete_comment_reject(self):
        att,policy,review=fixture()
        record=json.dumps(att,sort_keys=True)
        forged=record.replace('"head_sha": "'+H+'"',
                              '"head_sha": "f", "head_sha": "'+H+'"')
        self.assertNotEqual(forged,record)
        for body in (
            gate.REVIEW_PREFIX+forged,
            gate.REVIEW_PREFIX+record+"\n"+gate.REVIEW_PREFIX+record,
            gate.REVIEW_PREFIX+json.dumps({**att,"acceptance":True}),
            gate.REVIEW_PREFIX+"{}",
            "",
        ):
            def broken(a,p,r):
                r["body"]=body
            with self.subTest(body=body[:60]), self.assertRaises(
                    InfrastructureError):
                self.check(broken)

    def test_latest_dismissal_cannot_borrow_an_earlier_green_review(self):
        att,policy,approved=fixture()
        newer=dict(approved,id=RID+1,state="DISMISSED",
                   submitted_at="2026-10-27T02:00:00Z")
        with self.assertRaises(InfrastructureError):
            gate.approved_security_review(
                RID,AUTHOR,H,att,policy,
                paginate=lambda endpoint:[approved,newer])

    def test_committed_roster_duplicate_authority_keys_reject(self):
        original='{"format":"Permansson.InfrastructureReviewerAuthority.v1",'
        raw=(original+'"status":"UNCONFIGURED","status":"OWNER_AUTHORIZED",'
             '"owner":"HMarcusWH","reviewers":[{"login":"x"}]}')
        def git(*args):
            if args[0]=="show":
                return raw
            raise AssertionError(args)
        with self.assertRaises(InfrastructureError):
            gate.authority_policy(H,git=git)


if __name__=="__main__":
    unittest.main()
