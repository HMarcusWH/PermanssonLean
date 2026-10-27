"""Static-route/runtime-event separation: adversarial Python-only tests."""
import copy
import hashlib
import json
import unittest
from unittest import mock

import pr113_legacy20_runtime_resolution as r

H="a"*40


def digest(raw):return hashlib.sha256(raw).hexdigest()


def row(cid):
    return {
        "case_id":cid,"test_path":"verification/research/test_origin.py",
        "test_method":"test_negative","original_provider":
            "PermanssonResearch/Test/Original.lean",
    }


def events():
    return {"C-%02d"%i:[{
        "case_id":"C-%02d"%i,"test_index":0,
        "test_method":"test_negative",
        "original_provider":"PermanssonResearch/Test/Original.lean",
        "observation_id":"event-123-000001",
        "producing_artifact_id":123,
        "observation_sha256":"0"*64,
        "false_input_sha256":"1"*64,
        "unreviewed":True,
    }] for i in range(1,21)}


def selections(options):
    return {"format":r.FORMAT_DECISION,"head_sha":H,
            "status":"DETACHED_EVENT_CHOICES_UNREVIEWED",
            "independent_case_review":False,
            "mathematical_acceptance":False,
            "cases":[{
                "case_id":cid,
                "test_index":options[cid][0]["test_index"],
                "observation_id":options[cid][0]["observation_id"],
                "producing_artifact_id":options[cid][0]["producing_artifact_id"],
            } for cid in sorted(options)]}


class Source:
    def __init__(self):
        self.cases={}
    def blob(self,path):
        return b"import unittest\nclass T(unittest.TestCase):\n    def test_negative(self):\n        pass\n"


def original_case_map(_head):
    cases={}
    for cid in events():
        cases[cid]={
            "case_id":cid,
            "test_method_candidates":[{
                "path":"verification/research/test_origin.py",
                "method":"test_negative","role":"SEMANTIC_NEGATIVE",
            }],
            "historical_proof_declarations":[{
                "path":"PermanssonResearch/Test/Original.lean",
            }],
            "new_claim_source_candidates":[],
        }
    return cases,tuple(cases)


class LegacyEventDecisionTests(unittest.TestCase):
    def test_static_intent_cannot_contain_future_artifact_ids(self):
        intents={"format":r.FORMAT_INTENT,
                 "source_head_binding":"ACTUAL_CI_HEAD_AT_RUN",
                 "review_status":"REQUIRES_INDEPENDENT_MATHEMATICAL_REVIEW",
                 "cases":[row(cid) for cid in sorted(events())]}
        with mock.patch.object(r,"original_case_map",side_effect=original_case_map):
            mapping=r.parse_intent(intents,H,Source())
            self.assertEqual(len(mapping),20)
            self.assertFalse(any("artifact_id" in x for x in mapping.values()))

    def test_unknown_method_provider_or_duplicate_fails_static_intent(self):
        default={"format":r.FORMAT_INTENT,
                 "source_head_binding":"ACTUAL_CI_HEAD_AT_RUN",
                 "review_status":"REQUIRES_INDEPENDENT_MATHEMATICAL_REVIEW",
                 "cases":[row(cid) for cid in sorted(events())]}
        with mock.patch.object(r,"original_case_map",side_effect=original_case_map):
            for mutation in ("badmethod","provider","duplicate","futureid","review"):
                payload=copy.deepcopy(default)
                if mutation=="badmethod":payload["cases"][0]["test_method"]="test_unrelated"
                if mutation=="provider":payload["cases"][0]["original_provider"]="PermanssonResearch/Other/Foreign.lean"
                if mutation=="duplicate":payload["cases"][0]=payload["cases"][1]
                if mutation=="futureid":payload["cases"][0]["artifact_id"]=123
                if mutation=="review":payload["review_status"]="APPROVED"
                with self.subTest(mutation=mutation):
                    with self.assertRaises(r.RuntimeLegacyError):
                        r.parse_intent(payload,H,Source())

    def test_detached_choices_only_select_observed_event_ids(self):
        candidates=events()
        choices=selections(candidates)
        result=r.decision_to_selection(H,candidates,choices)
        self.assertEqual(result["format"],r.FORMAT_SELECTION)
        self.assertEqual(len(result["cases"]),20)
        self.assertEqual(result["cases"][0]["test_method"],"test_negative")
        self.assertTrue(all(set(row)=={
            "case_id","test_index","test_method","original_provider",
            "observation_id","producing_artifact_id",
        } for row in result["cases"]))

    def test_forged_or_stale_detached_choices_do_not_pass(self):
        c=events()
        for name,edit in (
            ("stale-head",lambda v:v.update(head_sha="b"*40)),
            ("approval",lambda v:v.update(mathematical_acceptance=True)),
            ("wrong-id",lambda v:v["cases"][0].update(
                 observation_id="event-999-999999")),
            ("wrong-artifact",lambda v:v["cases"][0].update(
                 producing_artifact_id=7777)),
            ("duplicate-case",lambda v:v["cases"][0].update(
                 case_id=v["cases"][1]["case_id"])),
            ("missing-case",lambda v:v["cases"].pop()),
        ):
            value=selections(c)
            edit(value)
            with self.subTest(name=name),self.assertRaises(r.RuntimeLegacyError):
                r.decision_to_selection(H,c,value)

    def test_exact_original_github_capture_and_semantic_stderr_are_required(self):
        cid="C-01"
        test="verification/research/test_origin.py"
        test_bytes=b"python original method"
        source=mock.Mock()
        source.blob.return_value=test_bytes
        obs=b"error: type mismatch\n"
        original=b"captured false theorem input"
        prefix=cid+"/test-00/raw_compiler/event-1-000001/"
        members={
            cid+"/test-00/unreviewed_test_manifest.json":json.dumps({
                "format":"Permansson.LegacyCaseTestExecutionCandidate.v1",
                "case_id":cid,"test_file":test,
                "selected_methods":["test_negative"],
                "source_test_sha256":digest(test_bytes),
                "status":"EXECUTED_UNREVIEWED_NOT_AUTHENTICATED",
                "test_exit_code":0,
            }).encode(),
            prefix+"observation.json":json.dumps({
                "format":"Permansson.LegacyLeanCompilerObservation.v1",
                "case_id_unverified":cid,
                "selected_method_unverified":"test_negative",
                "status":"RAW_UNREVIEWED",
                "returncode":1,
                "source_sha256":digest(original),
                "stderr_sha256":digest(obs),
            }).encode(),
            prefix+"source.lean":original,
            prefix+"stderr.log":obs,
        }
        authenticated={"producers":{123:{"members":members}}}
        actual=r.enumerate_events(H,{cid:row(cid)},source,authenticated,{123})
        self.assertEqual(len(actual[cid]),1)
        members[prefix+"stderr.log"]=b"error: parser error\n"
        bad=r.enumerate_events(H,{cid:row(cid)},source,authenticated,{123})
        self.assertEqual(bad[cid],[])


    def test_detached_legacy21_directories_reject_path_traversal_and_symlinks(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            original=root/"original"
            original.mkdir()
            self.assertEqual(r.original_detached_directory(original),
                             original.resolve())
            parent=root/"parent"
            parent.mkdir()
            with self.assertRaises(r.RuntimeLegacyError):
                r.original_detached_directory(parent/".."/"original")
            link=root/"alias"
            link.symlink_to(original,target_is_directory=True)
            with self.assertRaises(r.RuntimeLegacyError):
                r.original_detached_directory(link)

    def test_duplicate_selected_legacy21_source_receipt_is_not_authority(self):
        from pr113_boundary_io import strict_json_object, BoundaryError
        with self.assertRaises(BoundaryError):
            strict_json_object(
                b'{"head_sha":"old","head_sha":"forged","cases":[]}')


if __name__=="__main__":
    unittest.main()
