"""Execute proposed v2 contract against exact 30 virtual Git source blobs.

No source-provided file, hash, or test grants approval. Full activation of
protected source is still separate from this preactivation adversarial QA.
"""
from __future__ import annotations
import ast
import importlib.util
import json
from pathlib import Path
import subprocess
import unittest
from unittest import mock
from pr113_workflow_profile_v2 import PREACTIVATION_HEAD

ROOT=Path(__file__).resolve().parents[2]
STAGE=ROOT/"docs/operations/pr113_required_gate_replacement_unapproved"
TARGET=STAGE/"workflow_contract_v2.py"
TEST_STAGE=STAGE/"test_workflow_v2.py"

def git(*args):
    return subprocess.check_output(
        ["git",*args],cwd=ROOT,stderr=subprocess.DEVNULL,timeout=25)

def virtual_sources():
    H=git("rev-parse","HEAD").decode().strip()
    full=json.loads(git("show",H+":"+
               "docs/operations/pr113_required_gate_replacement_unapproved/full_workflow_manifest.json"))
    proposal=json.loads(git("show",H+":"+
               "docs/operations/pr113_unapproved_workflows/manifest.json"))
    result={}
    historical=git("ls-tree","-r","--name-only",PREACTIVATION_HEAD,
                   "--",".github/workflows").decode().splitlines()
    for path in historical:
        if path.startswith(".github/workflows/") and path.endswith((".yml",".yaml")):
            result[Path(path).name]=git("show",PREACTIVATION_HEAD+":"+path).decode()
    for item in full["full_replacements"]:
        result[Path(item["target"]).name]=git(
            "show",H+":"+item["staged_source"]).decode()
    for item in proposal["proposals"]:
        result[Path(item["workflow_path"]).name]=git(
            "show",H+":"+item["staged_source_path"]).decode()
    return result

def load_staged_contract():
    spec=importlib.util.spec_from_file_location(
        "pr113_staged_contract_under_review",TARGET)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

class CandidateV2ContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.contract=load_staged_contract()
        cls.sources=virtual_sources()

    def test_exact_thirty_virtual_git_blobs_and_required_job_names(self):
        result=self.contract.validate_workflow_set(self.sources)
        self.assertEqual(result["workflows"],30)
        self.assertFalse(result["owner_activation_authorized"])
        self.assertFalse(result["independent_security_review"])
        self.assertFalse(result["all_workflow_actions_commit_pinned"])
        self.assertTrue(result["mutable_action_refs_pending_security_review"])
        self.assertIn("actions/checkout@v4",
                      result["retained_historical_mutable_action_refs"]["a2-smoke.yml"])
        self.assertEqual(set(self.sources),set(
            self.contract.APPROVED_WORKFLOW_BLOBS))
        actual=self.contract.validate_workflow(
            self.sources["research-integrity.yml"],self.sources)
        self.assertEqual(len(actual["contexts"]),3)

    def test_only_exact_retained_history_may_keep_mutable_action_tags(self):
        # Mutable inherited action tags are unresolved security debt,
        # not fully pinned workflow actions or reviewer authorization.
        self.assertEqual(len(self.contract.RETAINED_HISTORICAL_WORKFLOWS),23)
        self.assertEqual(len(self.contract.REPLACEMENT_WORKFLOWS),2)
        self.assertEqual(len(self.contract.ADDITION_WORKFLOWS),5)
        for name in ("research-integrity.yml","pr113-preseal-fullscope.yml"):
            with self.subTest(source=name):
                src=self.sources[name]
                import re
                matcher=re.search(r"(?m)^\s*- uses:\s*actions/checkout@[a-f0-9]{40}",
                                  src)
                self.assertIsNotNone(matcher)
                new_line=matcher.group(0).rsplit("@",1)[0]+"@v4"
                changed=src[:matcher.start()]+new_line+src[matcher.end():]
                modified=dict(self.sources)
                modified[name]=changed
                # Even a source-owned repin must not allow a new mutable tag.
                new_blob=self.contract.git_blob_oid(changed.encode("utf-8"))
                with mock.patch.dict(self.contract.APPROVED_WORKFLOW_BLOBS,
                                     {name:new_blob}):
                    with self.assertRaisesRegex(Exception,
                                                 "must be full-SHA pinned"):
                        self.contract.validate_workflow_set(modified)

    def test_each_canonical_mutation_rejected_by_exact_source_gate(self):
        self.assertEqual(len(self.sources),30)
        for name in self.sources:
            with self.subTest(file=name):
                replaced=dict(self.sources)
                replaced[name]+="\n# unauthorized footer\n"
                with self.assertRaises(Exception):
                    self.contract.validate_workflow_set(replaced)

    def test_absent_colliding_or_privileged_workflow_refused(self):
        one=dict(self.sources)
        one.pop("research-lean.yml")
        with self.assertRaises(Exception):
            self.contract.validate_workflow_set(one)
        two=dict(self.sources)
        two["duplicate-required.yml"]="name: duplicate\n"
        with self.assertRaises(Exception):
            self.contract.validate_workflow_set(two)
        for before,after in (("actions: read","actions: write"),
                             ("contents: read","contents: write"),
                             ("pull_request:","pull_request_target:"),
                             ("pr113_required_dual_gate_v2.py",
                              "echo pr113_required_dual_gate_v2.py")):
            source=dict(self.sources)
            self.assertIn(before,source["research-integrity.yml"])
            source["research-integrity.yml"]=source[
                "research-integrity.yml"].replace(before,after,1)
            with self.assertRaises(Exception):
                self.contract.validate_workflow_set(source)

    def test_v2_suite_preserves_all_ci06_ci07_mappings_before_install(self):
        old_tests=git("show",PREACTIVATION_HEAD+
                      ":verification/integrity/tests/test_workflow.py").decode()
        staged=TEST_STAGE.read_text()
        old_names={n.name for n in ast.walk(ast.parse(old_tests))
                   if isinstance(n,ast.FunctionDef) and n.name.startswith("test_")
                   and n.name!="test_case"}
        new_names={n.name for n in ast.walk(ast.parse(staged))
                   if isinstance(n,ast.FunctionDef) and n.name.startswith("test_")
                   and n.name!="test_case"}
        self.assertEqual(old_names,new_names)
        coverage=json.loads((ROOT/"verification/integrity/test_coverage.json").read_bytes())
        methods=[m for x in coverage["cases"]
                 if x["id"] in ("CI-06","CI-07") for m in x["methods"]]
        names={m.rsplit(".",1)[-1] for m in methods}
        self.assertTrue(names <= new_names)
        status=json.loads((STAGE/"workflow_contract_v2_manifest.json").read_bytes())
        self.assertFalse(status["owner_activation_authorized"])
        self.assertFalse(status["independent_security_review"])
        self.assertFalse(status["installed"])

if __name__=="__main__":
    unittest.main()
