import io
import json
from pathlib import Path
import unittest

from verification.integrity.reports import HardeningError
from verification.integrity.run_tests import RecordedResult, validate_mapping, _validate_mapping, validate_result
from verification.integrity.workflow_contract import validate_workflow


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(__file__).resolve().parents[3]
        self.text = (self.root / ".github/workflows/research-integrity.yml").read_text()

    def rejected(self, callback, code):
        with self.assertRaises(HardeningError) as raised:
            callback()
        self.assertEqual(code, raised.exception.code)

    def test_ci_06_filters_and_skip_paths_forbidden(self):
        self.assertEqual(3, len(validate_workflow(self.text)["contexts"]))
        for snippet in ("    paths: ['docs/**']\n", "    paths-ignore: ['release/**']\n",
                        "    if: false\n", "    needs: absent\n", "    continue-on-error: true\n"):
            with self.subTest(snippet=snippet):
                self.rejected(lambda: validate_workflow(self.text + snippet), "E_WORKFLOW_CONTRACT")
        for replacement in ("echo python -B -m verification.integrity.preservation", "true || python -B -m verification.integrity.preservation"):
            self.rejected(lambda: validate_workflow(self.text.replace("python -B -m verification.integrity.preservation", replacement)), "E_WORKFLOW_CONTRACT")

    def test_ci_07_discovery_reports_and_skips_fail_closed(self):
        registry = {"cases": [{"id": "CI-07", "suite": "workflow", "level": "unit", "methods": ["x.test"]}]}
        self.assertEqual({"x.test": ["CI-07"]}, _validate_mapping(registry, "workflow", ["x.test"], {"CI-07": ("workflow", "unit")}))
        self.rejected(lambda: validate_mapping(registry, "workflow", ["x.test"]), "E_REPORT")
        self.rejected(lambda: validate_mapping(registry, "workflow", []), "E_REPORT")
        self.rejected(lambda: validate_mapping({"cases": []}, "workflow", ["x.test"]), "E_REPORT")
        self.rejected(lambda: validate_mapping(registry, "workflow", ["unittest.loader._FailedTest.bad"]), "E_REPORT")
        self.rejected(lambda: validate_mapping(registry, "workflow", ["other.test"]), "E_REPORT")
        class Skipped(unittest.TestCase):
            @unittest.skip("deliberate runner control")
            def test_case(self):
                pass
        test = Skipped("test_case")
        result = unittest.TextTestRunner(stream=io.StringIO(), resultclass=RecordedResult).run(unittest.TestSuite([test]))
        self.rejected(lambda: validate_result(result, [test.id()], {test.id(): ["CI-07"]}), "E_REPORT")

    def test_read_only_credentials_review_control(self):
        validate_workflow(self.text)
        self.rejected(lambda: validate_workflow(self.text.replace("contents: read", "contents: write")), "E_WORKFLOW_CONTRACT")
        self.rejected(lambda: validate_workflow(self.text.replace("persist-credentials: false", "persist-credentials: true", 1)), "E_WORKFLOW_CONTRACT")

    def test_disabled_ruleset_is_only_a_proposal(self):
        proposal = json.loads((self.root / ".github/repository-rules/main.proposed.json").read_text())
        self.assertEqual("disabled", proposal["enforcement"])
        self.assertEqual([], proposal["bypass_actors"])
        checks = next(rule for rule in proposal["rules"] if rule["type"] == "required_status_checks")
        self.assertEqual(8, len(checks["parameters"]["required_status_checks"]))
        self.assertTrue(all(row["integration_id"] == 15368 for row in checks["parameters"]["required_status_checks"]))
