import io
import json
from pathlib import Path
import unittest

from verification.integrity.reports import HardeningError
from verification.integrity.run_tests import RecordedResult, validate_mapping, _validate_mapping, validate_result
from verification.integrity.tests._fixtures import GitFixture
from verification.integrity.workflow_contract import (LEGACY_COMMAND, LEGACY_FIRST_WORK, RELEASE_WORKFLOW,
                                                     load_workflows, validate_release_workflow,
                                                     validate_workflow)


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(__file__).resolve().parents[3]
        self.text = (self.root / ".github/workflows/research-integrity.yml").read_text()
        # Explicit fixture inputs let local source review precede a commit. The
        # production loader is independently exercised against real Git below.
        self.workflows = {path.name: path.read_text(encoding="utf-8")
                          for path in (self.root / ".github/workflows").iterdir()
                          if path.suffix in {".yml", ".yaml"}}

    def checked(self, text=None, workflows=None):
        return validate_workflow(self.text if text is None else text,
                                 self.workflows if workflows is None else workflows)

    def rejected(self, callback, code):
        with self.assertRaises(HardeningError) as raised:
            callback()
        self.assertEqual(code, raised.exception.code)

    def test_ci_06_filters_and_skip_paths_forbidden(self):
        # This is the production gate, bound to canonical HEAD. A changed
        # profile must be committed before a full suite can certify it.
        self.assertEqual(26, validate_workflow(self.text)["workflows"])
        self.assertEqual(3, len(self.checked(self.text)["contexts"]))
        for snippet in ("    paths: ['docs/**']\n", "    paths-ignore: ['release/**']\n",
                        "    if: false\n", "    needs: absent\n", "    continue-on-error: true\n"):
            with self.subTest(snippet=snippet):
                self.rejected(lambda: self.checked(self.text + snippet), "E_WORKFLOW_CONTRACT")
        for replacement in ("echo python -B -m verification.integrity.preservation", "true || python -B -m verification.integrity.preservation"):
            self.rejected(lambda: self.checked(self.text.replace("python -B -m verification.integrity.preservation", replacement)), "E_WORKFLOW_CONTRACT")
        for restricted_types in ("closed", "labeled"):
            with self.subTest(restricted_types=restricted_types):
                candidate = self.text.replace("    branches: [main]\n",
                                              "    branches: [main]\n    types: [" + restricted_types + "]\n", 1)
                with self.assertRaises(HardeningError) as raised:
                    self.checked(candidate)
                self.assertEqual("E_WORKFLOW_CONTRACT", raised.exception.code)
                self.assertIn("complete reviewed workflow digest", str(raised.exception))

    def check_release_workflow_is_dispatch_only_with_one_writer(self):
        # The added application release workflow can never produce a required
        # context, and only its publish job may write repository contents.
        # Called from the registered permission control below, so the
        # archived test-coverage registry stays unchanged.
        text = self.workflows[RELEASE_WORKFLOW]
        def reject(message):
            raise HardeningError("E_WORKFLOW_CONTRACT", message)
        self.assertEqual(5, len(validate_release_workflow(text, reject)["release_jobs"]))
        dispatch = "on:\n  workflow_dispatch:\n"
        mutations = {
            "push trigger": text.replace(dispatch, "on:\n  push:\n    branches: [main]\n  workflow_dispatch:\n"),
            "required job id": text.replace("  release-build:\n", "  build:\n"),
            "required job name": text.replace("name: release gate", "name: research"),
            "second writer": text.replace("    permissions:\n      contents: read\n      actions: read\n",
                                          "    permissions:\n      contents: write\n      actions: read\n", 1),
            "repository secret": text.replace("${{ github.token }}", "${{ secrets.TOKEN }}", 1),
            "mutable action": text.replace("actions/checkout@11d5960a326750d5838078e36cf38b85af677262",
                                           "actions/checkout@v4", 1),
            "writable default token": text.replace("permissions:\n  contents: read\n\njobs:",
                                                   "permissions:\n  contents: write\n\njobs:"),
        }
        for name, mutated in mutations.items():
            with self.subTest(name):
                self.assertNotEqual(text, mutated)
                self.rejected(lambda: validate_release_workflow(mutated, reject), "E_WORKFLOW_CONTRACT")
                changed = dict(self.workflows, **{RELEASE_WORKFLOW: mutated})
                self.rejected(lambda: self.checked(self.text, changed), "E_WORKFLOW_CONTRACT")

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
        self.checked(self.text)
        self.rejected(lambda: self.checked(self.text.replace("contents: read", "contents: write")), "E_WORKFLOW_CONTRACT")
        self.rejected(lambda: self.checked(self.text.replace("persist-credentials: false", "persist-credentials: true", 1)), "E_WORKFLOW_CONTRACT")
        for name in LEGACY_FIRST_WORK:
            for before, after in (("contents: read", "contents: write"),
                                  ("persist-credentials: false", "persist-credentials: true"),
                                  ("fetch-depth: 0", "fetch-depth: 1")):
                with self.subTest(legacy=name, altered=before):
                    candidate = dict(self.workflows)
                    candidate[name] = candidate[name].replace(before, after, 1)
                    self.rejected(lambda: self.checked(self.text, candidate), "E_WORKFLOW_CONTRACT")

    def test_disabled_ruleset_is_only_a_proposal(self):
        proposal = json.loads((self.root / ".github/repository-rules/main.proposed.json").read_text())
        self.assertEqual("disabled", proposal["enforcement"])
        self.assertEqual([], proposal["bypass_actors"])
        checks = next(rule for rule in proposal["rules"] if rule["type"] == "required_status_checks")
        self.assertEqual(8, len(checks["parameters"]["required_status_checks"]))
        self.assertTrue(all(row["integration_id"] == 15368 for row in checks["parameters"]["required_status_checks"]))

    def test_job_permission_overrides_rejected(self):
        self.checked(self.text)
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
                self.rejected(lambda: self.checked(candidate), "E_WORKFLOW_CONTRACT")
        for grant in ("  issues: write\n", "# mapping continues across this comment\n  id-token: write\n"):
            with self.subTest(grant=grant):
                candidate = self.text.replace("permissions:\n  contents: read\n",
                                              "permissions:\n  contents: read\n" + grant, 1)
                self.rejected(lambda: self.checked(candidate), "E_WORKFLOW_CONTRACT")
        self.check_release_workflow_is_dispatch_only_with_one_writer()

    def test_shell_background_and_redirection_rejected(self):
        self.checked(self.text)
        line = next(line for line in self.text.splitlines()
                    if line.startswith("        run: python -B -m verification.integrity.preservation "))
        for suffix in (" & true", "&true", " | true", "|true", " > ignored", ">ignored",
                       " < /dev/null", " || true", " && true", " ; true",
                       ' --report "$RUNNER_TEMP/other-report.json"'):
            with self.subTest(suffix=suffix):
                self.rejected(lambda: self.checked(self.text.replace(line, line + suffix, 1)),
                              "E_WORKFLOW_CONTRACT")

    def test_execution_overrides_rejected(self):
        self.checked(self.text)
        # A profile change must not cancel checks on a different ref,
        # silently disable superseded-run cleanup, or override its scope.
        concurrency = ("concurrency:\n"
                       "  group: ${{ github.workflow }}-${{ github.ref }}\n"
                       "  cancel-in-progress: true\n")
        self.assertIn(concurrency, self.text)
        for drift in (
            concurrency.replace("cancel-in-progress: true", "cancel-in-progress: false"),
            concurrency.replace("github.ref", "github.repository"),
            concurrency.replace("github.workflow", "github.repository"),
            concurrency + "  max-parallel: 1\n",
        ):
            self.rejected(lambda: self.checked(self.text.replace(
                concurrency, drift, 1)), "E_WORKFLOW_CONTRACT")
        for override in ("    env:\n      PATH: /tmp/shadow\n",
                         "    defaults:\n      run:\n        shell: bash -c 'true'\n",
                         "    shell: bash -c 'true'\n",
                         "    working-directory: /tmp/shadow\n",
                         "    container: ubuntu:latest\n", "    services: {}\n",
                         "    strategy: {}\n", "    name: misleading-check-context\n"):
            with self.subTest(override=override):
                candidate = self.text.replace("  frozen-source-preservation:\n",
                                              "  frozen-source-preservation:\n" + override, 1)
                self.rejected(lambda: self.checked(candidate), "E_WORKFLOW_CONTRACT")
        self.rejected(lambda: self.checked(self.text.replace("permissions:\n", "env:\n  PATH: /tmp/shadow\npermissions:\n", 1)),
                      "E_WORKFLOW_CONTRACT")
        self.rejected(lambda: self.checked(self.text.replace("persist-credentials: false", "persist-credentials: false\n          persist-credentials: true", 1)),
                      "E_WORKFLOW_CONTRACT")
        for candidate in ("%YAML 1.2\n" + self.text, "---\n" + self.text,
                          self.text + "\n...\n", self.text + "\n---\n# second document\n"):
            with self.subTest(structural_form=candidate[:30] + candidate[-30:]):
                self.rejected(lambda: self.checked(candidate), "E_WORKFLOW_CONTRACT")
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
                    self.checked(candidate)
                self.assertEqual("E_WORKFLOW_CONTRACT", raised.exception.code)
                self.assertIn("complete reviewed workflow digest", str(raised.exception))

    def test_required_workflow_rejects_dispatch(self):
        checked = self.checked(self.text)
        self.assertEqual(26, checked["workflows"])
        self.assertEqual(5, len(checked["legacy_contexts"]))
        candidate = self.text.replace("on:\n", "on:\n  workflow_dispatch:\n", 1)
        self.rejected(lambda: self.checked(candidate), "E_WORKFLOW_CONTRACT")
        guard = "      - name: Bind genuine required-check source\n        shell: bash\n        run: " + LEGACY_COMMAND + "\n"
        for name, first_work in LEGACY_FIRST_WORK.items():
            source = self.workflows[name]
            # All five legacy runtime contexts use this direct checked prelude;
            # the application matrix executes it on both supported OS runners.
            self.assertLess(source.index(guard), source.index(first_work))
            mutations = {
                "dispatch": source.replace("on:\n", "on:\n  workflow_dispatch:\n", 1),
                "removed_guard": source.replace(guard, "", 1),
                "background_guard": source.replace(LEGACY_COMMAND + "\n", LEGACY_COMMAND + " & true\n", 1),
                "conditional_guard": source.replace("        shell: bash\n        run: " + LEGACY_COMMAND,
                    "        if: false\n        shell: bash\n        run: " + LEGACY_COMMAND, 1),
                "proof_before_guard": source.replace(guard, "", 1) + guard,
                "head_checkout": source.replace("          fetch-depth: 0\n",
                    "          fetch-depth: 0\n          ref: ${{ github.event.pull_request.head.sha }}\n", 1),
            }
            for attack, altered in mutations.items():
                with self.subTest(legacy=name, attack=attack):
                    candidate = dict(self.workflows, **{name: altered})
                    self.rejected(lambda: self.checked(self.text, candidate), "E_WORKFLOW_CONTRACT")
        # File-set/payload pinning rejects all alternate YAML name spellings
        # without claiming to parse arbitrary YAML or resolve its expressions.
        for duplicate in (
            "jobs:\n  build:\n    runs-on: ubuntu-latest\n    steps: [{run: true}]\n",
            'jobs: {other: {name: "build", runs-on: ubuntu-latest, steps: [{run: true}]}}\n',
            'jobs:\n  other:\n    name: "\\u0062uild"\n    runs-on: ubuntu-latest\n',
            "jobs:\n  other:\n    name: !!str research\n    runs-on: ubuntu-latest\n",
            "jobs:\n  other:\n    name: ${{ inputs.context }}\n    runs-on: ubuntu-latest\n",
        ):
            with self.subTest(extra_workflow=duplicate):
                candidate = dict(self.workflows)
                candidate["duplicate-required.yml"] = "name: Duplicate\non:\n  workflow_dispatch:\n" + duplicate
                self.rejected(lambda: self.checked(self.text, candidate), "E_WORKFLOW_CONTRACT")
                candidate = dict(self.workflows)
                candidate["a2-smoke.yml"] += "\n" + duplicate
                self.rejected(lambda: self.checked(self.text, candidate), "E_WORKFLOW_CONTRACT")
        missing = dict(self.workflows)
        missing.pop("lean.yml")
        self.rejected(lambda: self.checked(self.text, missing), "E_WORKFLOW_CONTRACT")
        # Canonical Git authority: a checkout conversion/untracked file cannot
        # alter accepted payloads, but a committed CRLF/mode/name edit can.
        fixture = GitFixture()
        self.addCleanup(fixture.close)
        changes = {(b".github/workflows/" + name.encode()): ("100644", text.encode())
                   for name, text in self.workflows.items()}
        good = fixture.commit(changes)
        fixture.repo.run("update-ref", "refs/heads/main", good)
        checkout = fixture.root / ".github/workflows"
        checkout.mkdir(parents=True)
        (checkout / "lean.yml").write_bytes(b"untracked checkout shadow\r\n")
        (checkout / "duplicate-required.yaml").write_bytes(b"jobs: {build: {}}\n")
        canonical = load_workflows(fixture.root)
        self.assertEqual(self.workflows, canonical)
        self.assertEqual(26, self.checked(self.text, canonical)["workflows"])
        path = b".github/workflows/lean.yml"
        variants = (
            {path: ("100644", self.workflows["lean.yml"].replace("\n", "\r\n").encode())},
            {path: ("100755", self.workflows["lean.yml"].encode())},
            {path: ("120000", b"outside.yml")},
            {b".github/workflows/duplicate-required.yaml": ("100644", b"jobs: {build: {}}\n")},
        )
        for changes in variants:
            altered = fixture.commit(changes, parent=good)
            fixture.repo.run("update-ref", "refs/heads/main", altered)
            with self.subTest(committed_workflow_changes=list(changes)):
                self.rejected(lambda: self.checked(self.text, load_workflows(fixture.root)),
                              "E_WORKFLOW_CONTRACT")
        fixture.repo.run("update-ref", "refs/heads/main", good)
        self.assertEqual(self.workflows, load_workflows(fixture.root))
