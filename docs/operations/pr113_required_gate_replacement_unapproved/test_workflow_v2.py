"""Versioned T2 successor workflow tests -- NOT INSTALLED OR APPROVED.

The original 25-workflow verifier remains in its immutable T checkout and
continues to verify the historical archive. These current-H tests validate
the reviewed 30-workflow source set, preserving original CI-06/CI-07 method
IDs and fail-closed discovery mapping. Requires independent security review
of the entire atomic upgrade to become an applicable required check.
"""
import io
import json
from pathlib import Path
import unittest

from verification.integrity.reports import HardeningError
from verification.integrity.run_tests import (
    RecordedResult, validate_mapping, _validate_mapping, validate_result,
)
from verification.integrity.workflow_contract import (
    APPROVED_WORKFLOW_BLOBS, load_workflows,
    validate_workflow, validate_workflow_set,
)

class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.root=Path(__file__).resolve().parents[3]
        self.workflows=load_workflows()
        self.integrity=self.workflows["research-integrity.yml"]

    def rejected(self, replacement):
        with self.assertRaises(HardeningError) as caught:
            validate_workflow(replacement.get("research-integrity.yml",""),
                              replacement)
        self.assertEqual(caught.exception.code,"E_WORKFLOW_CONTRACT")

    def altered(self, file, before, after):
        source=self.workflows[file]
        self.assertIn(before,source)
        modified=dict(self.workflows)
        modified[file]=source.replace(before,after,1)
        return modified

    def test_ci_06_filters_and_skip_paths_forbidden(self):
        output=validate_workflow(self.integrity,self.workflows)
        self.assertEqual(output["workflows"],30)
        self.assertEqual(len(output["contexts"]),3)
        for before,after in (
            ("    branches: [main]","    branches: [changed]"),
            ("      - name: Execute archive adversaries",
             "      - name: Execute archive adversaries\n        if: false"),
            ("      - name: Verify genuine reviewed original T/T2 and A2 source",
             "      - name: Verify genuine reviewed original T/T2 and A2 source\n        continue-on-error: true"),
        ):
            with self.subTest(altered=before):
                self.rejected(self.altered(
                    "research-integrity.yml",before,after))

    def test_ci_07_discovery_reports_and_skips_fail_closed(self):
        registry={"cases":[{"id":"CI-07","suite":"workflow",
                            "level":"unit","methods":["x.test"]}]}
        self.assertEqual({"x.test":["CI-07"]},
                         _validate_mapping(registry,"workflow",
                                           ["x.test"],{"CI-07":("workflow","unit")}))
        with self.assertRaises(HardeningError):
            validate_mapping(registry,"workflow",["x.test"])
        with self.assertRaises(HardeningError):
            validate_mapping(registry,"workflow",[])
        class Skipped(unittest.TestCase):
            @unittest.skip("deliberate negative control")
            def test_case(self):pass
        test=Skipped("test_case")
        runner=unittest.TextTestRunner(stream=io.StringIO(),
                                     resultclass=RecordedResult)
        result=runner.run(unittest.TestSuite([test]))
        with self.assertRaises(HardeningError):
            validate_result(result,[test.id()],{test.id():["CI-07"]})

    def test_read_only_credentials_review_control(self):
        for name in ("research-integrity.yml","research-lean.yml"):
            self.rejected(self.altered(name,"contents: read","contents: write"))
            self.rejected(self.altered(name,"actions: read","actions: write"))
            self.rejected(self.altered(name,"pull-requests: read",
                                        "pull-requests: write"))

    def test_disabled_ruleset_is_only_a_proposal(self):
        path=self.root/".github/repository-rules/main.proposed.json"
        proposal=json.loads(path.read_bytes())
        self.assertEqual(proposal["enforcement"],"disabled")
        self.assertEqual(proposal["bypass_actors"],[])

    def test_job_permission_overrides_rejected(self):
        for value in ("    permissions: {contents: write}\n",
                      "    permissions:\n      contents: write\n",
                      "    env:\n      GITHUB_TOKEN: overridden\n",
                      "    runs-on: self-hosted\n"):
            self.rejected(self.altered(
                "research-integrity.yml",
                "  archive-reproducibility:\n",
                "  archive-reproducibility:\n"+value))

    def test_shell_background_and_redirection_rejected(self):
        original="python3 -B verification/research/pr113_historical_runtime_v3.py"
        source=self.integrity
        # Both the producer and --check-existing verifier must be guarded.
        self.assertEqual(source.count(original),2)
        first=source.find(original)
        second=source.find(original,first+len(original))
        self.assertGreater(second,first)
        self.assertIn("--check-existing",source[second:second+400])
        for site,offset in (("produce",first),("check-existing",second)):
            for changed in ("true || "+original,
                            original+" > /dev/null",
                            original+" & true",
                            original+" || true",
                            "echo "+original):
                with self.subTest(site=site,mutation=changed):
                    mutated=dict(self.workflows)
                    mutated["research-integrity.yml"]=(
                        source[:offset]+changed+source[offset+len(original):])
                    self.rejected(mutated)

    def test_execution_overrides_rejected(self):
        for source in ("research-integrity.yml","research-lean.yml"):
            for before,after in (
                ("persist-credentials: false","persist-credentials: true"),
                ("fetch-depth: 0","fetch-depth: 1"),
                ("cancel-in-progress: true","cancel-in-progress: false"),
                ("branches: [main]","branches: [other]"),
            ):
                with self.subTest(source=source,edited=before):
                    self.rejected(self.altered(source,before,after))

    def test_required_workflow_rejects_dispatch(self):
        for path in ("research-lean.yml","research-integrity.yml"):
            self.rejected(self.altered(path,"on:\n",
                                "on:\n  workflow_dispatch:\n"))
            self.rejected(self.altered(path,"GITHUB_TOKEN:",
                                             "IGNORED_TOKEN:"))
        extra=dict(self.workflows)
        extra["duplicate-required.yml"]="name: duplicate\non: push\n"
        self.rejected(extra)
        missing=dict(self.workflows)
        missing.pop("research-lean.yml")
        self.rejected(missing)


if __name__=="__main__":
    unittest.main()
