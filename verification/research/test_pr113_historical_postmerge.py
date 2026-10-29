"""Synthetic main-merge source identity tests; never owner approval."""
import copy
import json
import unittest
from unittest import mock

import pr113_historical_postmerge as gate
B=gate.B113
H="a"*40
M="b"*40


def env():
    return {
        "GITHUB_ACTIONS":"true", "GITHUB_EVENT_NAME":"push",
        "GITHUB_REF":"refs/heads/main",
        "GITHUB_REPOSITORY":gate.REPOSITORY,
        "GITHUB_JOB":"archive-reproducibility",
        "GITHUB_WORKFLOW":"Research integrity",
        "GITHUB_SHA":M,"GITHUB_RUN_ID":"31337",
        "GITHUB_RUN_ATTEMPT":"1",
    }


def event():
    return json.dumps({
        "ref":"refs/heads/main","after":M,
        "repository":{"full_name":gate.REPOSITORY},
    }).encode()


def git(*args):
    if args==("rev-parse","HEAD"):return M
    if args in (("cat-file","-t",M),("cat-file","-t",H)):return "commit"
    if args==("show","-s","--format=%P",M):return B+" "+H
    if args in (("rev-parse",M+"^{tree}"),
                ("rev-parse",H+"^{tree}")):return "same_tree"
    if args[0]=="show" and args[1] in (
            H+":"+gate.ACTIVE_WORKFLOW,
            M+":"+gate.ACTIVE_WORKFLOW):
        return ("# Review-pending source-controlled historical verification\n"
                "historical-T-and-H-unreviewed\n"
                "historical-A2-and-H-unreviewed\n")
    if args==("show",H+":lake-manifest.json"):return "{}"
    raise AssertionError("unexpected Git op "+repr(args))


def live(path):
    if path=="/pulls/113":
        return {"number":113,"state":"closed","merged":True,
                "merge_commit_sha":M,
                "head":{"sha":H},"user":{"login":"HMarcusWH"}}
    if path=="/branches/main":
        return {"commit":{"sha":M}}
    raise AssertionError(path)


class MainHistoricalGateTests(unittest.TestCase):
    def test_original_main_binding_has_real_two_parents_and_unreviewed_state(self):
        ctx=gate.exact_main_event(env=env(),event_bytes=event(),
                                  git=git,live=live)
        self.assertEqual(ctx["original_base_sha"],B)
        self.assertEqual(ctx["reviewed_head_sha"],H)
        self.assertEqual(ctx["merged_main_sha"],M)
        self.assertEqual(ctx["github_job"],"archive-reproducibility")

    def test_foreign_main_or_squash_rebase_not_borrowed(self):
        for mutate in (
            lambda e:e.update(GITHUB_SHA="0"*40),
            lambda e:e.update(GITHUB_REF="refs/heads/research/final-mathematical-closure"),
            lambda e:e.update(GITHUB_EVENT_NAME="pull_request"),
            lambda e:e.update(GITHUB_WORKFLOW="Other"),
            lambda e:e.update(GITHUB_RUN_ATTEMPT="0"),
        ):
            e=env()
            mutate(e)
            with self.subTest(mutate=mutate),self.assertRaises(
                    gate.PostmergeError):
                gate.exact_main_event(env=e,event_bytes=event(),
                                      git=git,live=live)
        def squash(*args):
            if args==("show","-s","--format=%P",M):return B
            return git(*args)
        with self.assertRaises(gate.PostmergeError):
            gate.exact_main_event(env=env(),event_bytes=event(),
                                  git=squash,live=live)
        def wrong_tree(*args):
            if args==("rev-parse",M+"^{tree}"):return "wrong"
            return git(*args)
        with self.assertRaises(gate.PostmergeError):
            gate.exact_main_event(env=env(),event_bytes=event(),
                                  git=wrong_tree,live=live)

    def test_false_merge_or_remote_source_mutation_rejected(self):
        def unmerged(path):
            obj=live(path)
            if path=="/pulls/113":return dict(obj,merged=False)
            return obj
        with self.assertRaises(gate.PostmergeError):
            gate.exact_main_event(env=env(),event_bytes=event(),
                                  git=git,live=unmerged)
        def wrongmain(path):
            if path=="/branches/main":return {"commit":{"sha":"0"*40}}
            return live(path)
        with self.assertRaises(gate.PostmergeError):
            gate.exact_main_event(env=env(),event_bytes=event(),
                                  git=git,live=wrongmain)

    def test_checked_main_receipt_is_not_a_mathematical_certificate(self):
        ctx=gate.exact_main_event(env=env(),event_bytes=event(),
                                  git=git,live=live)
        envelope={
            "format":gate.FORMAT,"target":gate.source_target(ctx),
            "historical_T":{},"historical_A2":{},
            "security_review_id":321,"source_bound_ci":[],
        }
        with mock.patch.object(gate,"authenticate_original_zip",
                               side_effect=lambda kind,*args,**kwargs:
                                   {"kind":kind}), \
             mock.patch.object(gate,"inspect_zip",return_value={}), \
             mock.patch.object(gate,"inspect_T",return_value={"T":"PASS"}), \
             mock.patch.object(gate,"inspect_A2",return_value={"A2":"PASS"}), \
             mock.patch.object(gate,"verify_A2_dependency_bridge",
                               return_value="1"*64), \
             mock.patch.object(gate,"authority_policy",
                               return_value={}), \
             mock.patch.object(gate,"approved_security_review",
                               return_value=True):
            report=gate.check_historical_merged(
                envelope,b"old T ZIP",b"old A2 ZIP",
                event_context=ctx,git=git,live=live,paginate=lambda p:[])
        self.assertEqual(report["status"],
            "MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE")
        self.assertEqual(report["required_ci_successful"],0)
        self.assertFalse(report["independent_mathematical_review"])
        self.assertFalse(report["publication_authorized"])
        self.assertFalse(report["owner_merge_authorized"])
        bad=copy.deepcopy(envelope)
        bad["target"]["merged_main_sha"]="f"*40
        with self.assertRaises(gate.PostmergeError):
            gate.check_historical_merged(bad,b"old T",b"old A2",
                                          event_context=ctx,git=git,live=live)


if __name__=="__main__":
    unittest.main()
