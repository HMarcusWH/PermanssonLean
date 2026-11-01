"""Owner-engineering archive successor contract v1: every boundary fails closed.

The gate reads policy v2 (the 25-workflow contract plus the owner-approved
application release workflow); the v1 record stays as history and still parses.

Real-repository tests audit the committed T/B/C objects, the policy and the
installed research-integrity workflow. Report, policy and orchestration tests
use SYNTHETIC reports shaped like the original verifier's output (see the
B run 39513915824 artifact); they never count as a historical replay. The
genuine isolated T replay runs only in the `archive-reproducibility` job.
"""
from __future__ import annotations

from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import archive_successor_gate_v1 as gate  # noqa: E402
import pr113_tooling_migration as tooling  # noqa: E402
from verification.integrity.reports import HardeningError  # noqa: E402

ROOT = gate.ROOT
COMMAND = ('python -B verification/research/archive_successor_gate_v1.py --repo . --candidate "$GITHUB_SHA" '
           '--supplement archival/v0.2.0/supplement-1 --scratch "$RUNNER_TEMP/archive-clean" '
           '--evidence "$RUNNER_TEMP/archive-evidence" --report "$RUNNER_TEMP/archive-replay.json"')


def _has_history() -> bool:
    try:
        gate.git(ROOT, "cat-file", "-e", tooling.T + "^{commit}")
        gate.git(ROOT, "cat-file", "-e", tooling.B + "^{commit}")
        return True
    except HardeningError:
        return False


def standalone_report(**changes) -> dict:
    """SYNTHETIC: the original standalone report shape, not a replay."""
    details = {
        "acceptance_scope": "accepted_artifact_replay_only", "artifact_replay": "PASS",
        "completed_stages": list(gate.STANDALONE_STAGES), "isolation": {"network_isolation": "ENFORCED"},
        "publication": {"status": "NOT_APPLICABLE"}, "replay_target": gate.ACCEPTED,
        "replay_tree": gate.ACCEPTED_TREE, "source_restore": "PASS",
        "tooling": {"binding": "standalone_content_hashes_only", "files": 35,
                    "reproduction_instructions_match": True, "source_commit": tooling.T}}
    report = {"format": "Permansson.Hardening.Check.v1", "check": "archive-reproducibility", "status": "PASS",
              "error_code": None, "message": None, "completed_stages": list(gate.STANDALONE_STAGES),
              "details": details}
    for path, value in changes.items():
        target = report
        keys = path.split("__")
        for key in keys[:-1]:
            target = target[key]
        if value is KeyError:
            target.pop(keys[-1])
        else:
            target[keys[-1]] = value
    return report


def suite_report(**changes) -> dict:
    report = {"status": "PASS", "suite": "workflow", "methods_run": 9, "skips": 0, "failures": 0, "errors": 0}
    report.update(changes)
    return report


def raw(value) -> bytes:
    return json.dumps(value).encode()


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.policy, _ = gate.load_policy()

    def test_committed_policy_is_an_owner_engineering_record(self):
        approved = gate.check_policy(self.policy)
        self.assertEqual(set(approved), set(tooling.EXPECTED_CHANGES))
        self.assertIs(self.policy["independent_security_review"], False)
        self.assertEqual(self.policy["authority"], "OWNER_ENGINEERING_POLICY")
        self.assertIn("not an independent security review", self.policy["statement"])
        self.assertEqual(self.policy["historical_record"]["pr113_final_archive_reproducibility_conclusion"], "failure")

    def test_policy_mutations_are_rejected(self):
        mutations = {
            "independent review claimed": lambda p: p.update(independent_security_review=True),
            "other authority": lambda p: p.update(authority="INDEPENDENT_SECURITY_REVIEW"),
            "other owner": lambda p: p.update(owner="someone-else"),
            "wrong T": lambda p: p.update(historical_T="0" * 40),
            "wrong B": lambda p: p.update(accepted_base_B="0" * 40),
            "25 workflows": lambda p: p.update(workflow_count=25),
            "27 workflows": lambda p: p.update(workflow_count=27),
            "no additions": lambda p: p.update(approved_added_workflows=[]),
            "addition is the archive workflow": lambda p: p["approved_added_workflows"][0].update(
                path=".github/workflows/research-integrity.yml"),
            "addition outside workflows": lambda p: p["approved_added_workflows"][0].update(path="release.yml"),
            "duplicate addition": lambda p: p["approved_added_workflows"].append(dict(p["approved_added_workflows"][0])),
            "short addition blob": lambda p: p["approved_added_workflows"][0].update(approved_blob="abc"),
            "v1 format with additions": lambda p: p.update(format=gate.POLICY_FORMAT),
            "extra field": lambda p: p.update(approved_by_reviewer="x"),
            "missing field": lambda p: p.pop("effective_by"),
            "third change": lambda p: p["approved_tooling_changes"].append(
                {"path": "verification/archive/verify_bundle.py", "T_blob": "1" * 40, "approved_blob": "2" * 40}),
            "dropped change": lambda p: p["approved_tooling_changes"].pop(),
            "duplicate path": lambda p: p["approved_tooling_changes"].append(dict(p["approved_tooling_changes"][0])),
            "short blob": lambda p: p["approved_tooling_changes"][0].update(approved_blob="abc"),
            "unchanged blob": lambda p: p["approved_tooling_changes"][0].update(
                approved_blob=p["approved_tooling_changes"][0]["T_blob"]),
            "boolean record": lambda p: p["historical_record"].update(pr113_approved=True),
            "second workflow": lambda p: p["approved_workflow_changes"].append(
                {"path": ".github/workflows/lean.yml", "preactivation_blob": "1" * 40, "approved_blob": "2" * 40}),
            "other workflow": lambda p: p["approved_workflow_changes"][0].update(path=".github/workflows/lean.yml"),
            "other preactivation head": lambda p: p.update(preactivation_25_head="0" * 40),
            "workflow unchanged": lambda p: p["approved_workflow_changes"][0].update(
                approved_blob=p["approved_workflow_changes"][0]["preactivation_blob"]),
        }
        for name, mutate in mutations.items():
            policy = deepcopy(self.policy)
            mutate(policy)
            with self.subTest(name), self.assertRaises(HardeningError) as raised:
                gate.check_policy(policy)
            self.assertEqual(raised.exception.code, "E_SUCCESSOR_POLICY")

    def test_the_v1_record_stays_a_valid_history(self):
        policy, _ = gate.load_policy(gate.POLICY.with_name("archive_successor_policy_v1.json"))
        self.assertEqual((policy["format"], policy["workflow_count"]), (gate.POLICY_FORMAT, 25))
        self.assertEqual(gate.added_workflows(policy), {})
        self.assertEqual(self.policy["format"], gate.POLICY_FORMAT_V2)
        self.assertEqual(self.policy["approved_workflow_changes"], policy["approved_workflow_changes"])
        self.assertEqual(self.policy["historical_record"], policy["historical_record"])
        self.assertEqual(set(gate.added_workflows(self.policy)), {".github/workflows/application-release.yml"})

    def test_duplicate_keys_are_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "policy.json"
            text = gate.POLICY.read_text()
            path.write_text(text.replace('"owner": "HMarcusWH",', '"owner": "HMarcusWH", "owner": "HMarcusWH",', 1))
            with self.assertRaises(HardeningError):
                gate.load_policy(path)


@unittest.skipUnless(_has_history(), "needs the Git history that contains T and B")
class RealSourceTests(unittest.TestCase):
    def setUp(self):
        self.policy, _ = gate.load_policy()
        self.head = gate.git(ROOT, "rev-parse", "HEAD")

    def require_committed(self):
        if gate.git(ROOT, "status", "--porcelain", "--untracked-files=no"):
            self.skipTest("uncommitted tracked changes; the audit binds the committed candidate")

    def test_committed_head_satisfies_the_source_audit(self):
        self.require_committed()
        source = gate.source_audit(ROOT, self.head, self.policy)
        self.assertEqual(source["workflow_count"], 26)
        self.assertEqual([row["path"] for row in source["approved_added_workflows"]],
                         [".github/workflows/application-release.yml"])
        self.assertEqual(source["historical_packaged_tooling_files_verified"], 35)
        self.assertEqual(source["archival_tree"], self.policy["archival_tree_at_B"])
        self.assertEqual({row["path"] for row in source["approved_closure_delta"]}, set(tooling.EXPECTED_CHANGES))

    def test_stale_or_foreign_approval_is_rejected(self):
        self.require_committed()
        for index, field in ((0, "approved_blob"), (1, "approved_blob"), (0, "T_blob")):
            policy = deepcopy(self.policy)
            policy["approved_tooling_changes"][index][field] = "f" * 40
            with self.subTest(index=index, field=field), self.assertRaises(HardeningError) as raised:
                gate.source_audit(ROOT, self.head, policy)
            self.assertEqual(raised.exception.code, "E_SUCCESSOR_DELTA")
        for field in ("preactivation_blob", "approved_blob"):
            policy = deepcopy(self.policy)
            policy["approved_workflow_changes"][0][field] = "e" * 40
            with self.subTest(workflow_field=field), self.assertRaises(HardeningError) as raised:
                gate.source_audit(ROOT, self.head, policy)
            self.assertEqual(raised.exception.code, "E_SUCCESSOR_DELTA")
        policy = deepcopy(self.policy)
        policy["approved_added_workflows"][0]["approved_blob"] = "d" * 40
        with self.subTest("added workflow blob"), self.assertRaises(HardeningError) as raised:
            gate.source_audit(ROOT, self.head, policy)
        self.assertEqual(raised.exception.code, "E_SUCCESSOR_DELTA")
        # The superseded v1 record cannot approve the current source.
        v1, _ = gate.load_policy(gate.POLICY.with_name("archive_successor_policy_v1.json"))
        with self.subTest("v1 record"), self.assertRaises(HardeningError):
            gate.source_audit(ROOT, self.head, v1)

    def test_wrong_candidate_or_archival_tree_is_rejected(self):
        with self.assertRaises(HardeningError) as raised:
            gate.source_audit(ROOT, "0" * 40, self.policy)
        self.assertEqual(raised.exception.code, "E_SUCCESSOR_SOURCE")
        self.require_committed()
        policy = deepcopy(self.policy)
        policy["archival_tree_at_B"] = "0" * 40
        with self.assertRaises(HardeningError) as raised:
            gate.source_audit(ROOT, self.head, policy)
        self.assertIn("archival tree", str(raised.exception))

    def test_source_audit_rejections_are_failures(self):
        self.require_committed()
        with mock.patch.object(tooling, "audit", side_effect=tooling.ToolingMigrationError("third change")):
            with self.assertRaises(HardeningError) as raised:
                gate.source_audit(ROOT, self.head, self.policy)
        self.assertEqual(raised.exception.code, "E_SUCCESSOR_SOURCE")
        self.assertIn("third change", str(raised.exception))

    def test_installed_workflow_runs_the_successor_gate(self):
        from verification.integrity.workflow_contract import validate_workflow
        text = (ROOT / ".github/workflows/research-integrity.yml").read_text(encoding="utf-8")
        workflows = {p.name: p.read_text(encoding="utf-8") for p in (ROOT / ".github/workflows").iterdir()
                     if p.suffix in {".yml", ".yaml"}}
        self.assertEqual(text.count("        run: " + COMMAND + "\n"), 1)
        self.assertEqual(validate_workflow(text, workflows)["workflows"], 26)
        old = ('python -B -m verification.archive.offline_smoke --repo . --candidate "$GITHUB_SHA" '
               '--supplement archival/v0.2.0/supplement-1 --scratch "$RUNNER_TEMP/archive-clean" '
               '--report "$RUNNER_TEMP/archive-replay.json"')
        for name, altered in {
            "original equality check": text.replace(COMMAND, old),
            "gate removed": text.replace("      - name: Replay the historical bundle", "      - name: x", 1)
                                .replace("        run: " + COMMAND + "\n", "        run: true\n"),
            "failure masked": text.replace(COMMAND, COMMAND + " || true"),
            "other policy": text.replace("archive_successor_gate_v1.py", "archive_successor_gate_v2.py"),
        }.items():
            with self.subTest(name), self.assertRaises(HardeningError):
                validate_workflow(altered, dict(workflows, **{"research-integrity.yml": altered}))



class ReportTests(unittest.TestCase):
    def test_standalone_isolated_T_report_is_accepted(self):
        result = gate.validate_historical_report(raw(standalone_report()), 0)
        self.assertEqual(result["binding"], "standalone_content_hashes_only")
        self.assertEqual(result["source_commit"], tooling.T)

    def test_historical_report_rejections(self):
        stages = list(gate.STANDALONE_STAGES)
        cases = {
            "failed": standalone_report(status="FAIL", error_code="E_TOOLING_CLOSURE"),
            "isolation missing": standalone_report(details__isolation={}),
            "isolation not enforced": standalone_report(details__isolation={"network_isolation": "NONE"}),
            "C-bound binding": standalone_report(details__tooling__binding="canonical_T_C_and_executing_code"),
            "foreign source": standalone_report(details__tooling__source_commit="0" * 40),
            "partial closure": standalone_report(details__tooling__files=34),
            "guide mismatch": standalone_report(details__tooling__reproduction_instructions_match=False),
            "wrong replay target": standalone_report(details__replay_target="0" * 40),
            "wrong replay tree": standalone_report(details__replay_tree="0" * 40),
            "restore not run": standalone_report(details__source_restore="NOT_RUN"),
            "replay not run": standalone_report(details__artifact_replay=KeyError),
            "stage skipped": standalone_report(completed_stages=stages[:-1], details__completed_stages=stages[:-1]),
            "stage added": standalone_report(completed_stages=stages + ["candidate_acceptance"]),
            "stages disagree": standalone_report(details__completed_stages=stages[1:]),
            "no scope": standalone_report(details__acceptance_scope=KeyError),
            "claims candidate CI": standalone_report(details__acceptance_scope="candidate_ci"),
            "publication claimed": standalone_report(details__publication={"status": "PASS"}),
            "wrong check": standalone_report(check="frozen-source-preservation"),
            "wrong format": standalone_report(format="Permansson.Other.v1"),
        }
        for name, report in cases.items():
            with self.subTest(name), self.assertRaises(HardeningError) as raised:
                gate.validate_historical_report(raw(report), 0)
            self.assertNotEqual(raised.exception.exit_code, 0)
        for name, data, code in (("nonzero exit", raw(standalone_report()), 1),
                                 ("not JSON", b"PASS", 0),
                                 ("duplicate key", b'{"status": "PASS", "status": "PASS"}', 0)):
            with self.subTest(name), self.assertRaises(HardeningError):
                gate.validate_historical_report(data, code)

    def test_blocked_T_replay_stays_blocked(self):
        with self.assertRaises(HardeningError) as raised:
            gate.validate_historical_report(raw(standalone_report(status="BLOCKED", error_code="E_OFFLINE_UNAVAILABLE",
                                                                  message="no namespace")), 3)
        self.assertEqual((raised.exception.code, raised.exception.exit_code), ("E_OFFLINE_UNAVAILABLE", 3))

    def test_current_suite_rejections(self):
        self.assertEqual(gate.validate_current_report(raw(suite_report()), 0)["methods_run"], 9)
        for name, report, code in (("failed", suite_report(status="FAIL"), 1), ("skipped", suite_report(skips=1), 0),
                                   ("error", suite_report(errors=1), 0), ("nothing ran", suite_report(methods_run=0), 0),
                                   ("other suite", suite_report(suite="archive"), 0),
                                   ("nonzero exit", suite_report(), 1)):
            with self.subTest(name), self.assertRaises(HardeningError):
                gate.validate_current_report(raw(report), code)


class EnvironmentAndProcessTests(unittest.TestCase):
    def test_historical_environment_drops_ci_git_token_and_import_redirection(self):
        base = {"PATH": "/usr/bin", "HOME": "/home/runner", "GITHUB_ACTIONS": "true", "GITHUB_TOKEN": "x",
                "GIT_DIR": "/elsewhere", "GIT_CONFIG_COUNT": "1", "GH_TOKEN": "x", "ACTIONS_RUNTIME_TOKEN": "x",
                "RUNNER_TEMP": "/tmp", "PYTHONPATH": "/candidate", "PYTHONHOME": "/x", "PERMANSSON_PARENT_NETNS": "n",
                "AWS_SECRET_ACCESS_KEY": "x", "MY_PASSWORD": "x", "CI": "true", "LANG": "C.UTF-8"}
        env = gate.historical_environment(base)
        self.assertEqual(env, {"PATH": "/usr/bin", "HOME": "/home/runner", "LANG": "C.UTF-8",
                               "PYTHONDONTWRITEBYTECODE": "1"})

    @unittest.skipUnless(sys.platform.startswith("linux"), "process-group semantics checked on Linux")
    def test_timeout_kills_the_whole_process_group(self):
        with tempfile.TemporaryDirectory() as td:
            marker = Path(td) / "child.pid"
            with self.assertRaises(HardeningError) as raised:
                gate.run_bounded(["sh", "-c", f"sleep 60 & echo $! > {marker}; wait"], Path(td), dict(os.environ), 1)
            self.assertEqual(raised.exception.code, "E_SUCCESSOR_TIMEOUT")
            child = int(marker.read_text().strip())
            for _ in range(50):
                if not Path(f"/proc/{child}").exists():
                    break
                time.sleep(0.1)
            self.assertFalse(Path(f"/proc/{child}").exists())


class OrchestrationTests(unittest.TestCase):
    """run_gate with injected source audit, checkout and runner (SYNTHETIC legs)."""

    def setUp(self):
        self.td = Path(tempfile.mkdtemp())
        self.addCleanup(lambda: subprocess.run(["rm", "-rf", str(self.td)]))
        self.repo = self.td / "repo"
        (self.repo / gate.ARCHIVAL / "supplement-1").mkdir(parents=True)
        self.audits = 0
        self.historical = standalone_report()
        self.current = suite_report()

    def audit(self, repo, candidate, policy):
        self.audits += 1
        return {"candidate": candidate, "approved_closure_delta": []}

    def checkout(self, repo, destination):
        destination.mkdir()
        return destination

    def runner(self, command, cwd, env, timeout):
        report = Path(command[command.index("--report") + 1])
        if "verification.archive.offline_smoke" in command:
            self.assertNotIn("GITHUB_ACTIONS", env)
            self.assertNotIn("PYTHONPATH", env)
            self.assertEqual(cwd.name, "historical-T")
            if self.historical is not None:
                report.write_bytes(raw(self.historical))
            return (0 if self.historical and self.historical["status"] == "PASS" else 3), b"T out", b""
        self.assertEqual(cwd, self.repo.resolve())
        report.write_bytes(raw(self.current))
        return (0 if self.current["status"] == "PASS" else 1), b"", b""

    def run_gate(self, **overrides):
        kwargs = dict(runner=self.runner, audit=self.audit, checkout=self.checkout, recheck=lambda path: None)
        kwargs.update(overrides)
        return gate.run_gate(self.repo, "a" * 40, self.repo / gate.ARCHIVAL / "supplement-1",
                             self.td / "scratch", self.td / "evidence", **kwargs)

    def test_both_legs_pass(self):
        result = self.run_gate()
        self.assertEqual(result["historical_T"]["status"], "PASS")
        self.assertEqual(result["current_C"]["status"], "PASS")
        self.assertIs(result["approval"]["independent_security_review"], False)
        self.assertEqual(result["approval"]["authority"], "OWNER_ENGINEERING_POLICY")
        self.assertEqual(self.audits, 2)
        self.assertTrue((self.td / "evidence/historical_T_report.json").is_file())

    def test_failing_or_missing_legs_fail_closed(self):
        cases = {
            "T failed": lambda: setattr(self, "historical", standalone_report(status="FAIL", error_code="E_X")),
            "T wrote nothing": lambda: setattr(self, "historical", None),
            "C failed": lambda: setattr(self, "current", suite_report(status="FAIL")),
        }
        for name, arrange in cases.items():
            self.setUp()
            arrange()
            with self.subTest(name), self.assertRaises(HardeningError):
                self.run_gate()

    def test_source_change_during_run_fails(self):
        def drifting(repo, candidate, policy):
            self.audits += 1
            return {"candidate": candidate, "round": self.audits}
        with self.assertRaises(HardeningError) as raised:
            self.run_gate(audit=drifting)
        self.assertIn("changed during verification", str(raised.exception))

    def test_mutated_T_checkout_fails(self):
        def recheck(path):
            raise HardeningError("E_SUCCESSOR_HISTORICAL", "historical T checkout is not the clean T commit")
        with self.assertRaises(HardeningError) as raised:
            self.run_gate(recheck=recheck)
        self.assertEqual(raised.exception.code, "E_SUCCESSOR_HISTORICAL")

    def test_output_paths_must_be_fresh_and_separate(self):
        (self.td / "scratch").mkdir()
        (self.td / "scratch" / "old").write_text("x")
        with self.assertRaises(HardeningError) as raised:
            self.run_gate()
        self.assertEqual(raised.exception.code, "E_SUCCESSOR_PATHS")
        with self.assertRaises(HardeningError):
            gate.run_gate(self.repo, "a" * 40, self.repo / gate.ARCHIVAL / "supplement-1", self.repo / "inside",
                          self.td / "evidence2", runner=self.runner, audit=self.audit, checkout=self.checkout)
        with self.assertRaises(HardeningError):
            gate.run_gate(self.repo, "a" * 40, self.td, self.td / "s3", self.td / "e3",
                          runner=self.runner, audit=self.audit, checkout=self.checkout)


if __name__ == "__main__":
    unittest.main()
