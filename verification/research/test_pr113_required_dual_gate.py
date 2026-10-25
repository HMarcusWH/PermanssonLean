"""Adversarial original-event binding tests; no real approvals manufactured."""
import json
import unittest
from unittest import mock

import pr113_required_dual_gate as gate

B = "1"*40
H = "2"*40
S = "3"*40

def fake_event():
    return json.dumps({
        "number":113,
        "repository":{"full_name":gate.REPOSITORY},
        "pull_request":{
            "base":{"sha":B,"ref":"main",
                    "repo":{"full_name":gate.REPOSITORY}},
            "head":{"sha":H,"ref":"research/final-mathematical-closure",
                    "repo":{"full_name":gate.REPOSITORY}},
        },
    }).encode()

def fake_env():
    return {
        "GITHUB_ACTIONS":"true",
        "GITHUB_REPOSITORY":gate.REPOSITORY,
        "GITHUB_EVENT_NAME":"pull_request",
        "GITHUB_REF":"refs/pull/113/merge",
        "GITHUB_SHA":S,
        "GITHUB_RUN_ID":"2468",
        "GITHUB_RUN_ATTEMPT":"2",
        "GITHUB_JOB":"archive-reproducibility",
        "GITHUB_WORKFLOW":"Research integrity",
    }

def payload():
    return {"target":{"base_sha":B,"head_sha":H,"synthetic_sha":S}}

def original():
    return {
        "status":"HISTORICAL_T_AND_A2_GENUINE_WITH_INDEPENDENT_SECURITY_REVIEW",
        "source_head":H,
        "historical_source_and_security_review_authenticated":True,
        "required_ci_successful":0,
        "merge_authorized":False,
        "publication_authorized":False,
        "independent_mathematical_review":False,
        "genuine_artifacts":{"T":{"sha256":"a"*64},"A2":{"sha256":"b"*64}},
        "T_execution":{"status":"OLD_T_COMPILER_PASS"},
        "A2_execution":{"status":"OLD_A2_COMPILER_PASS"},
    }

def git(*args):
    if args==("rev-parse","HEAD"):
        return S
    raise AssertionError("unexpected Git operation")

class RequiredDualGateTests(unittest.TestCase):
    def check(self, *, env=None, event=None, target=None, source=None):
        return gate.verify(
            payload() if target is None else target,
            b"real T ZIP",b"real A2 ZIP",
            env=fake_env() if env is None else env,
            event_data=fake_event() if event is None else event,
            git=git, historical_gate=(lambda *args: original() if source is None else source))

    def test_proposed_gate_is_still_not_mathematical_or_merge_approval(self):
        r=self.check()
        self.assertEqual(r["head_sha"],H)
        self.assertEqual(r["synthetic_sha"],S)
        self.assertEqual(r["github_job"],"archive-reproducibility")
        self.assertRegex(r["event_sha256"],r"^[0-9a-f]{64}$")
        for key in ("all_required_CI_accepted","mathematical_acceptance",
                    "owner_merge_authorized","publication_authorized"):
            self.assertFalse(r[key])

    def test_wrong_pr_event_or_borrowed_merge_rejected_before_gate(self):
        for mutation in (
            lambda e:e.update(GITHUB_ACTIONS=""),
            lambda e:e.update(GITHUB_EVENT_NAME="push"),
            lambda e:e.update(GITHUB_REF="refs/heads/main"),
            lambda e:e.update(GITHUB_SHA="9"*40),
            lambda e:e.update(GITHUB_JOB="compiler-shard"),
            lambda e:e.update(GITHUB_WORKFLOW="Other"),
            lambda e:e.update(GITHUB_RUN_ATTEMPT="0"),
        ):
            env=fake_env()
            mutation(env)
            with self.subTest(mutation=mutation),self.assertRaises(
                    gate.RequiredGateError):
                self.check(env=env)
        wrong=payload()
        wrong["target"]["head_sha"]="9"*40
        with self.assertRaises(gate.RequiredGateError):
            self.check(target=wrong)
        untrusted=json.loads(fake_event())
        untrusted["number"]=114
        with self.assertRaises(gate.RequiredGateError):
            self.check(event=json.dumps(untrusted).encode())

    def test_research_workflow_may_use_same_approved_both_legs(self):
        env=fake_env()
        env.update(GITHUB_JOB="research",GITHUB_WORKFLOW="Research Lean")
        r=self.check(env=env)
        self.assertEqual(r["github_job"],"research")
        self.assertFalse(r["all_required_CI_accepted"])

    def test_failed_original_historical_review_never_becomes_green(self):
        for invalid in (
            lambda x:x.update(required_ci_successful=12),
            lambda x:x.update(merge_authorized=True),
            lambda x:x.update(independent_mathematical_review=True),
            lambda x:x.update(historical_source_and_security_review_authenticated=False),
            lambda x:x.update(status="CANDIDATE_ONLY"),
        ):
            value=original()
            invalid(value)
            with self.subTest(invalid=invalid),self.assertRaises(
                    gate.RequiredGateError):
                self.check(source=value)

    def test_main_push_cannot_reuse_draft_only_historical_gate(self):
        ctx=fake_env()
        ctx.update(GITHUB_EVENT_NAME="push",
                   GITHUB_REF="refs/heads/main")
        with self.assertRaises(gate.RequiredGateError):
            gate.verify(payload(),b"T",b"A2",env=ctx,
                        event_data=fake_event(),git=git,
                        historical_gate=lambda *args:original())

    def test_postmerge_uses_real_git_default_instead_of_none(self):
        environ=fake_env()
        environ.update(GITHUB_EVENT_NAME="push",GITHUB_REF="refs/heads/main")
        with mock.patch("pr113_historical_postmerge.verify",
                        return_value={"status":"POSTMERGE_ONLY"}) as actual:
            value=gate.verify(payload(),b"T",b"A2",
                              env=environ,event_data=fake_event())
        self.assertEqual(value["status"],"POSTMERGE_ONLY")
        self.assertNotIn("git",actual.call_args.kwargs)
        self.assertEqual(actual.call_args.kwargs["env"],environ)


    def test_local_environment_cannot_pass_required_gate(self):
        with mock.patch.dict(gate.os.environ,{},clear=True):
            with self.assertRaises(gate.RequiredGateError):
                gate.verify(payload(),b"T",b"A2",
                            event_data=fake_event(),git=git,
                            historical_gate=lambda *a:original())


if __name__=="__main__":
    unittest.main()
