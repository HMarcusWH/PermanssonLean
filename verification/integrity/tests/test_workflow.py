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
        for restricted_types in ("closed", "labeled"):
            with self.subTest(restricted_types=restricted_types):
                candidate = self.text.replace("    branches: [main]\n",
                                              "    branches: [main]\n    types: [" + restricted_types + "]\n", 1)
                with self.assertRaises(HardeningError) as raised:
                    validate_workflow(candidate)
                self.assertEqual("E_WORKFLOW_CONTRACT", raised.exception.code)
                self.assertIn("complete reviewed workflow digest", str(raised.exception))

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

    def test_job_permission_overrides_rejected(self):
        validate_workflow(self.text)
        overrides = (
            "    permissions: {contents: write}\n",
            "    permissions:\n      contents: write\n",
            "    permissions:\n      contents: read\n",
            '    "permissions": {contents: write}\n',
            "    'permissions':\n      contents: write\n",
            '    "permis\\u0073ions":\n      contents: write\n',
            "    !!str permissions:\n      contents: write\n",
            "    !<tag:yaml.org,2002:str> permissions:\n      contents: write\n",
            "    &override !!str permissions:\n      contents: write\n",
        )
        for override in overrides:
            with self.subTest(override=override):
                candidate = self.text.replace("  frozen-source-preservation:\n",
                                              "  frozen-source-preservation:\n" + override, 1)
                self.rejected(lambda: validate_workflow(candidate), "E_WORKFLOW_CONTRACT")
        for grant in ("  issues: write\n", "# mapping continues across this comment\n  id-token: write\n"):
            with self.subTest(grant=grant):
                candidate = self.text.replace("permissions:\n  contents: read\n",
                                              "permissions:\n  contents: read\n" + grant, 1)
                self.rejected(lambda: validate_workflow(candidate), "E_WORKFLOW_CONTRACT")

    def test_shell_background_and_redirection_rejected(self):
        validate_workflow(self.text)
        line = next(line for line in self.text.splitlines()
                    if line.startswith("        run: python -B -m verification.integrity.preservation "))
        for suffix in (" & true", "&true", " | true", "|true", " > ignored", ">ignored",
                       " < /dev/null", " || true", " && true", " ; true",
                       ' --report "$RUNNER_TEMP/other-report.json"'):
            with self.subTest(suffix=suffix):
                self.rejected(lambda: validate_workflow(self.text.replace(line, line + suffix, 1)),
                              "E_WORKFLOW_CONTRACT")

    def test_execution_overrides_rejected(self):
        validate_workflow(self.text)
        for override in ("    env:\n      PATH: /tmp/shadow\n",
                         "    defaults:\n      run:\n        shell: bash -c 'true'\n",
                         "    shell: bash -c 'true'\n",
                         "    working-directory: /tmp/shadow\n",
                         "    container: ubuntu:latest\n", "    services: {}\n",
                         "    strategy: {}\n", "    name: misleading-check-context\n"):
            with self.subTest(override=override):
                candidate = self.text.replace("  frozen-source-preservation:\n",
                                              "  frozen-source-preservation:\n" + override, 1)
                self.rejected(lambda: validate_workflow(candidate), "E_WORKFLOW_CONTRACT")
        self.rejected(lambda: validate_workflow(self.text.replace("permissions:\n", "env:\n  PATH: /tmp/shadow\npermissions:\n", 1)),
                      "E_WORKFLOW_CONTRACT")
        self.rejected(lambda: validate_workflow(self.text.replace("persist-credentials: false", "persist-credentials: false\n          persist-credentials: true", 1)),
                      "E_WORKFLOW_CONTRACT")
        for candidate in ("%YAML 1.2\n" + self.text, "---\n" + self.text,
                          self.text + "\n...\n", self.text + "\n---\n# second document\n"):
            with self.subTest(structural_form=candidate[:30] + candidate[-30:]):
                self.rejected(lambda: validate_workflow(candidate), "E_WORKFLOW_CONTRACT")
        extra_steps = (
            "      - run: echo injected\n",
            "      - {run: echo injected}\n",
            "      - run: >\n          echo injected\n",
            "      - uses: ./candidate-action\n",
            "      - uses: actions/checkout\n",
            "      - uses: docker://alpine:latest\n",
        )
        drifted_profiles = [self.text.replace("    steps:\n", "    steps:\n" + step, 1)
                            for step in extra_steps]
        drifted_profiles.extend((self.text.replace("python-version: '3.13'", "python-version: '3.12'", 1),
                                 self.text.replace("          fetch-depth: 0\n",
                                                   "          fetch-depth: 0\n          ref: main\n", 1)))
        for candidate in drifted_profiles:
            with self.subTest(profile_drift=candidate):
                with self.assertRaises(HardeningError) as raised:
                    validate_workflow(candidate)
                self.assertEqual("E_WORKFLOW_CONTRACT", raised.exception.code)
                self.assertIn("complete reviewed workflow digest", str(raised.exception))

    def test_required_workflow_rejects_dispatch(self):
        validate_workflow(self.text)
        candidate = self.text.replace("on:\n", "on:\n  workflow_dispatch:\n", 1)
        self.rejected(lambda: validate_workflow(candidate), "E_WORKFLOW_CONTRACT")
