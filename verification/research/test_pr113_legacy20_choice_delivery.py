"""Authenticated legacy reviewer choice binding; synthetic fixtures only."""
import copy
import json
import unittest
from unittest import mock

import pr113_legacy20_choice_delivery as deliver
from pr113_legacy20_runtime_resolution import FORMAT_REPORT


H = "a" * 40
IDS = {"run_id": 100, "run_attempt": 1, "job_id": 200,
       "check_run_id": 300, "artifact_id": 400}
AUTHOR = "HMarcusWH"
REVIEWER = "external-math-reviewer"


def fixture():
    options = []
    for k in range(1, 21):
        cid = f"C-{k:02}"
        options.append({"case_id": cid, "options": [{
            "case_id": cid, "test_index": k, "observation_id": f"event-1-{k:06}",
            "producing_artifact_id": 500+k,
            "test_method": f"test_{k}", "original_provider": "P.lean",
        }]})
    report = {
        "format": FORMAT_REPORT,
        "status": "ACTUAL_CAPTURE_OPTIONS_UNREVIEWED",
        "source_head": H, "original_legacy_case_count": 20,
        "cases": options, "all_cases_have_candidates": True,
        "independent_case_review": False, "mathematical_acceptance": False,
    }
    member = (json.dumps(report, sort_keys=True)+"\n").encode()
    # Real transport accepts only an original bounded ZIP.
    import io, zipfile
    buf=io.BytesIO()
    with zipfile.ZipFile(buf,"w",zipfile.ZIP_DEFLATED) as z:
        z.writestr(deliver.SURVEY_MEMBER,member)
    raw = buf.getvalue()
    att = {
        "format":deliver.REVIEW_FORMAT,
        "status":"RELEVANCE_CHOICES_ONLY_NOT_CASE_ACCEPTANCE",
        "head_sha":H,
        "survey_zip_sha256":deliver.digest(raw),
        "survey_member_sha256":deliver.digest(member),
        "observation_artifact_id":400,
        "cases":[{k:opt[k] for k in deliver.SELECTION_FIELDS}
                 for entry in options for opt in entry["options"]],
    }
    comment = {
        "id": 700,
        "issue_url":"https://api.github.com/repos/HMarcusWH/PermanssonLean/issues/113",
        "created_at":"2026-10-25T01:00:00Z",
        "updated_at":"2026-10-25T01:00:00Z",
        "user":{"login":REVIEWER},
        "body":deliver.PREFIX+json.dumps(att,sort_keys=True),
    }
    api={
      "/actions/runs/100":{
        "id":100,"head_sha":H,
        "head_branch":"research/final-mathematical-closure",
        "status":"completed","conclusion":"success",
        "run_attempt":1,"event":"push",
        "path":deliver.ACTIVE_WORKFLOW,
      },
      "/actions/runs/100/jobs?per_page=100":{"jobs":[{
        "id":200,"run_id":100,"run_attempt":1,"head_sha":H,
        "name":deliver.SURVEY_JOB,"status":"completed","conclusion":"success",
        "check_run_url":"https://api.github.com/check-runs/300",
        "started_at":"2026-10-25T00:00:00Z",
        "completed_at":"2026-10-25T00:30:00Z",
      }]},
      "/check-runs/300":{
        "id":300,"name":deliver.SURVEY_JOB,"head_sha":H,
        "status":"completed","conclusion":"success",
        "app":{"slug":"github-actions"},
      },
      "/actions/artifacts/400":{
        "id":400,"name":deliver.SURVEY_ARTIFACT,"expired":False,
        "digest":"sha256:"+deliver.digest(raw),
        "created_at":"2026-10-25T00:20:00Z",
        "workflow_run":{"id":100,"head_sha":H},
      },
      "/issues/comments/700":comment,
      "/pulls/113":{"state":"open","merged":False,"head":{"sha":H},
                    "user":{"login":AUTHOR}},
    }
    policy={"format":"Permansson.PR113.LegacyEventReviewerAuthority.v1",
            "status":"OWNER_AUTHORIZED","owner":AUTHOR,
            "reviewers":[{"login":REVIEWER,"approved_by":AUTHOR,
                           "independence_disclosed":True}]}
    return raw, member, api, policy, att


class LegacyDeliveryTests(unittest.TestCase):
    def run_delivery(self, modify=None):
        raw, member, api, policy, att = fixture()
        if modify: modify(raw,member,api,policy,att)
        def git(*args):
            if args==("rev-parse","HEAD"):
                return H
            if args==("show",H+":"+deliver.POLICY):
                return json.dumps(policy)
            raise AssertionError(args)
        # Selection matching is independently checked by original code.
        with mock.patch.object(deliver,"decision_to_selection",
                               return_value={"cases":[]}) as binder:
            result=deliver.deliver(H,IDS,raw,700,git=git,live=api.__getitem__)
            self.assertEqual(binder.call_count,1)
        return result

    def test_full_genuine_selection_transport_remains_unapproved(self):
        result = self.run_delivery()
        selection=result["selection"]
        self.assertEqual(len(selection["cases"]),20)
        self.assertFalse(selection["independent_case_review"])
        self.assertFalse(selection["mathematical_acceptance"])
        self.assertFalse(result["diagnostic"]["publication_authorized"])

    def test_incomplete_or_unobserved_reviewer_selection_fails(self):
        def missing(raw,member,api,policy,att):
            att["cases"].pop()
            api["/issues/comments/700"]["body"]=deliver.PREFIX+json.dumps(att)
        with self.assertRaises(deliver.ChoiceDeliveryError):
            self.run_delivery(missing)
        def fake(raw,member,api,policy,att):
            att["cases"][0]["observation_id"]="event-999-000001"
            api["/issues/comments/700"]["body"]=deliver.PREFIX+json.dumps(att)
        with self.assertRaises(deliver.ChoiceDeliveryError):
            self.run_delivery(fake)

    def test_author_self_review_and_unauthorized_reviewer_fail(self):
        def author(raw,member,api,policy,att):
            api["/issues/comments/700"]["user"]["login"]=AUTHOR
        with self.assertRaises(deliver.ChoiceDeliveryError):
            self.run_delivery(author)
        def no_policy(raw,member,api,policy,att):
            policy["status"]="UNCONFIGURED"
        with self.assertRaises(deliver.ChoiceDeliveryError):
            self.run_delivery(no_policy)

    def test_wrong_survey_artifact_source_and_early_review_fail(self):
        for mutate in (
            lambda api,att: api["/actions/runs/100"].update(conclusion="failure"),
            lambda api,att: api["/actions/runs/100/jobs?per_page=100"]["jobs"][0].update(conclusion="failure"),
            lambda api,att: api["/actions/artifacts/400"].update(digest="sha256:"+"0"*64),
            lambda api,att: api["/actions/artifacts/400"].update(expired=True),
            lambda api,att: api["/issues/comments/700"].update(created_at="2026-10-24T01:00:00Z"),
            lambda api,att: att.update(head_sha="b"*40),
        ):
            def bad(raw,member,api,policy,att):
                mutate(api,att)
                api["/issues/comments/700"]["body"]=deliver.PREFIX+json.dumps(att)
            with self.subTest(mutate=mutate),self.assertRaises(
                    deliver.ChoiceDeliveryError):
                self.run_delivery(bad)

    def test_post_edit_reviewer_comment_is_never_source_authority(self):
        for edited in (
            "2026-10-25T01:00:01Z",
            "2026-10-25T09:30:00Z",
            None,
        ):
            def tamper(raw,member,api,policy,att):
                api["/issues/comments/700"]["updated_at"]=edited
            with self.subTest(edited=edited), self.assertRaises(
                    deliver.ChoiceDeliveryError):
                self.run_delivery(tamper)

    def test_reviewer_comment_body_digest_retained_but_unapproved(self):
        result=self.run_delivery()
        diagnostic=result["diagnostic"]
        self.assertRegex(diagnostic["review_comment_body_sha256"],r"^[0-9a-f]{64}$")
        self.assertEqual(diagnostic["review_comment_created_at"],
                         "2026-10-25T01:00:00Z")
        self.assertFalse(diagnostic["mathematical_acceptance"])

    def test_foreign_issue_or_stale_PR_rejected(self):
        def wrong(raw,member,api,policy,att):
            api["/issues/comments/700"]["issue_url"] = (
                "https://api.github.com/repos/HMarcusWH/PermanssonLean/issues/114")
        with self.assertRaises(deliver.ChoiceDeliveryError):
            self.run_delivery(wrong)
        def stale(raw,member,api,policy,att):
            api["/pulls/113"]["head"]["sha"]="b"*40
        with self.assertRaises(deliver.ChoiceDeliveryError):
            self.run_delivery(stale)


if __name__ == "__main__":
    unittest.main()
