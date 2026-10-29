"""Non-authorizing -O checks of the inherited M113 historical gate.

Every module in the child is a temporary synthetic stub: successful tests
are not evidence of an actual T/A2 producer, GitHub check or human review.
"""
import ast
import copy
import json
import subprocess
import sys
import unittest
import pr113_historical_inheritance_v3 as inheritance

H="b"*40
M="c"*40
NAMES=tuple("mock-required-%02d"%i for i in range(12))
GOOD_STATUS="MERGED_HISTORICAL_T_AND_A2_REVERIFIED_UNDER_REVIEWED_SOURCE"


def case():
    return {
        "checks":{name:{"id":100+i,"head_sha":H,"status":"completed",
                         "conclusion":"success"} for i,name in enumerate(NAMES)},
        "receipt":{"status":GOOD_STATUS,
                   "independent_security_review_authenticated":True,
                   "required_ci_successful":0},
    }


def run_synthetic(record,producer=111,reviewer=333,optimized=True):
    prelude='''import json,sys,types
data=json.loads(__DATA__)
def module(name, **values):
    m=types.ModuleType(name)
    m.__dict__.update(values)
    sys.modules[name]=m
module("pr113_historical_artifact_delivery_v2",
       collect=lambda h,run,**k: (
           {"T":b"PKt","A2":b"PKa"},
           {"T":{"run_id":run},"A2":{"run_id":run}},{}))
module("pr113_historical_postmerge_v2",
       check_historical_merged=lambda *a,**kw:data["receipt"],
       source_target=lambda target:target,
       FORMAT="Permansson.PR113.PostmergeHistoricalEvidence.v2")
module("infrastructure_acceptance_v2",
       exact_committed_lake_blob=lambda h:b"{}")
module("release_target",B113="a"*40)
module("final_closure_authenticate",
       REQUIRED=frozenset(__NAMES__),
       authenticated_checks=lambda h:data["checks"])
'''
    prelude=prelude.replace("__DATA__",repr(json.dumps(record)))
    prelude=prelude.replace("__NAMES__",repr(NAMES))
    argv=[sys.executable]+(["-O"] if optimized else [])+[
        "-B","-c",prelude+inheritance.CHILD,H,M,str(producer),str(reviewer)]
    return subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                          timeout=20,check=False)


class OptimizedHistoricalSourceTests(unittest.TestCase):
    def test_honest_synthetic_controls_under_regular_and_optimized_python(self):
        for optimized in (False,True):
            with self.subTest(optimized=optimized):
                result=run_synthetic(case(),optimized=optimized)
                self.assertEqual(result.returncode,0,result.stderr.decode(errors="replace"))
                receipt=json.loads(result.stdout)
                self.assertEqual(receipt["original_required_context_count"],12)
                self.assertEqual(receipt["historical_status"],GOOD_STATUS)
                self.assertFalse(receipt["new_mathematical_acceptance"])

    def test_invalid_check_identity_or_outcome_is_rejected_under_optimization(self):
        for mutation in ("missing","failed","queued","wrong_head","zero","boolean"):
            record=case()
            first=NAMES[0]
            if mutation=="missing":record["checks"].pop(first)
            elif mutation=="failed":record["checks"][first]["conclusion"]="failure"
            elif mutation=="queued":record["checks"][first]["status"]="queued"
            elif mutation=="wrong_head":record["checks"][first]["head_sha"]="f"*40
            elif mutation=="zero":record["checks"][first]["id"]=0
            elif mutation=="boolean":record["checks"][first]["id"]=True
            with self.subTest(mutation=mutation):
                result=run_synthetic(record)
                self.assertNotEqual(result.returncode,0)
                self.assertEqual(result.stdout,b"")
                self.assertIn(b"ValueError:",result.stderr)

    def test_false_review_status_scope_and_ids_are_rejected_under_optimization(self):
        for mutation in ("review","status","ci","boolean_ci","producer","reviewer"):
            record=case()
            producer=111
            reviewer=333
            if mutation=="review":record["receipt"]["independent_security_review_authenticated"]=False
            elif mutation=="status":record["receipt"]["status"]="FORGED_SUCCESS"
            elif mutation=="ci":record["receipt"]["required_ci_successful"]=12
            elif mutation=="boolean_ci":record["receipt"]["required_ci_successful"]=False
            elif mutation=="producer":producer=0
            elif mutation=="reviewer":reviewer=0
            with self.subTest(mutation=mutation):
                result=run_synthetic(record,producer,reviewer)
                self.assertNotEqual(result.returncode,0)
                self.assertEqual(result.stdout,b"")
                self.assertIn(b"ValueError:",result.stderr)

    def test_child_contains_no_optimization_sensitive_assert_nodes(self):
        self.assertEqual(
            [node for node in ast.walk(ast.parse(inheritance.CHILD))
             if isinstance(node,ast.Assert)],[])
