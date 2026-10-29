"""The dual A2 harness must execute both checks, never autoapprove either."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import pr113_dual_a2_compiler as dual


def fake_result(status, gate):
    command_names = ["compiler_version","research_build","signatures_axioms",
                     "positive_fixture","source_1","source_2","source_3","source_4",
                     *gate.MUTATIONS]
    return {
        "status":status,
        "mode":"focused",
        "source_unchanged":True,
        "declarations":{name:[] for name in gate.DECLS},
        "mutations":{name:{"status":"SEMANTICALLY_REJECTED",
                           "positive_source_sha256":"b"*64,
                           "mutant_source_sha256":"c"*64}
                     for name in gate.MUTATIONS},
        "commands":[{"label":name,
                     "returncode":1 if name in gate.MUTATIONS else 0,
                     "log_sha256":"a"*64} for name in command_names],
        "independent_security_review":False,
        "historical_a2_verifier_replaced":False,
        "mathematical_acceptance":False,
        "historical_runtime_provenance":{
            "historical_checkout_sha":"a"*40,
            "introduced_executable_sha":dual.HISTORICAL_INTRODUCER,
            "imported_current_A2_gate":False,
            "independent_security_review":False,
        },
    }


class DualA2Tests(unittest.TestCase):
    def test_both_real_runs_retained_unapproved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            old,now=root/"old",root/"current"
            old.mkdir();now.mkdir()
            dest=root/"output"
            original=fake_result("LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
                                 dual.historical_gate)
            new=fake_result("SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                            dual.successor_gate)
            with mock.patch.object(dual,"real_source",side_effect=[old,now]), \
                 mock.patch.object(dual,"run_historical_verified",
                                   return_value=original) as h, \
                 mock.patch.object(dual.successor_gate,"verify",
                                   return_value=new) as s:
                result=dual.execute(old,"a"*40,now,"b"*40,dest)
            h.assert_called_once()
            s.assert_called_once()
            self.assertEqual(result["historical_semantic_mutants"],4)
            self.assertEqual(result["successor_semantic_mutants"],4)
            self.assertFalse(result["independent_security_approval"])
            self.assertFalse(result["required_research_CI_accepted"])
            self.assertFalse(result["full_release_approved"])
            self.assertTrue((dest/"unreviewed_dual_A2_candidate.json").exists())

    def test_any_incomplete_original_leg_blocks_successor(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); old=root/"old";now=root/"current"
            old.mkdir();now.mkdir()
            h=fake_result("LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
                          dual.historical_gate)
            h["mutations"].pop(next(iter(h["mutations"])))
            with mock.patch.object(dual,"real_source",side_effect=[old,now]), \
                 mock.patch.object(dual,"run_historical_verified",return_value=h), \
                 mock.patch.object(dual.successor_gate,"verify") as s:
                with self.assertRaises(dual.DualA2Error):
                    dual.execute(old,"a"*40,now,"b"*40,root/"out")
                s.assert_not_called()

    def test_historical_exec_invokes_its_own_checkout_not_current_module(self):
        with tempfile.TemporaryDirectory() as td:
            old=Path(td)/"historical"
            (old/"verification/research").mkdir(parents=True)
            gate=old/dual.HISTORICAL_GATE
            gate.write_text("original")
            path=Path(td)/"candidate"
            invocation=dual.historical_command(old,path,"focused")
            self.assertEqual(invocation[:2],[dual.sys.executable,"-B"])
            self.assertEqual(Path(invocation[2]),gate)
            self.assertEqual(invocation[3:],[
                "--repo",str(old),"--output",str(path),"--mode","focused"])
            self.assertNotEqual(Path(dual.historical_gate.__file__).resolve(),
                                gate.resolve())
            gate.unlink()
            with self.assertRaises(dual.DualA2Error):
                dual.historical_command(old,path,"focused")

    def test_missing_historical_runtime_provenance_must_fail_closed(self):
        with tempfile.TemporaryDirectory() as td:
            old,now=Path(td)/"old",Path(td)/"now"
            old.mkdir();now.mkdir()
            receipt=fake_result("LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
                                dual.historical_gate)
            receipt.pop("historical_runtime_provenance")
            with mock.patch.object(dual,"real_source",side_effect=[old,now]), \
                 mock.patch.object(dual,"run_historical_verified",
                                   return_value=receipt), \
                 mock.patch.object(dual.successor_gate,"verify",
                                   return_value=fake_result(
                                       "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                                       dual.successor_gate)):
                with self.assertRaises(dual.DualA2Error):
                    dual.execute(old,"a"*40,now,"b"*40,Path(td)/"result")

    def test_staged_historical_dependency_bridge_uses_identical_pins_only(self):
        """The historical T/A2 migration candidate does not borrow H proofs."""
        proposed = (Path(__file__).resolve().parents[2] /
                    "docs/operations/pr113_unapproved_workflows/"
                    "pr113-historical-migration-candidates.yml").read_text()
        begin = proposed.index("      - name: Bind historical A2 to the exact pinned dependency source")
        end = proposed.index("      - name: Execute both genuine compiler gates", begin)
        stage = proposed[begin:end]
        from pr113_a2_dependency_bridge_v2 import FORMAT
        from pr113_historical_a2_baseline_v1 import REPLAY_HEAD, INTRODUCER
        self.assertIn("pr113_a2_dependency_bridge_v2.py", stage)
        for option in ("--historical-source", "--current-source",
                       "--current-head", "--out"):
            self.assertIn(option, stage)
        self.assertIn("--historical-head " + REPLAY_HEAD, proposed)
        self.assertNotIn("--historical-head " + INTRODUCER, proposed)
        self.assertEqual(FORMAT, "Permansson.PR113.HistoricalA2DependencyBridge.v2")
        root = Path(__file__).resolve().parents[2]
        bridge = (root / "verification/research/pr113_a2_dependency_bridge_v2.py").read_text()
        replay = (root / "verification/research/pr113_historical_a2_replay_v1.py").read_text()
        # Check the executable helper and the original package-only bridge,
        # not obsolete inline shell text. Runtime tests separately reject
        # wrong pins, source edits, injected project builds and fake receipts.
        for guard in ("baseline.verify_positive_source(historical)",
                      "packages = dependency_bridge(now, old)",
                      "packages == manifest_packages(raw)",
                      "unchanged(old, baseline.REPLAY_HEAD)",
                      '"historical_project_proofs_reused": False',
                      '"independent_security_review": False',
                      '"mathematical_acceptance": False'):
            self.assertIn(guard, bridge)
        for guard in ('"lean-toolchain", "lake-manifest.json", "lakefile.toml"',
                      'not (old / ".lake/build").exists()',
                      "link.symlink_to(packages.resolve()",
                      "check_dependencies(old) == before"):
            self.assertIn(guard, replay)
        actual_commands = "\n".join(
            line for line in stage.splitlines()
            if not line.lstrip().startswith("#"))
        self.assertNotIn("lake update", actual_commands)
        self.assertIn("historical_dependency_bridge.json", proposed)
        self.assertIn("cp --", proposed)
        self.assertIn("test -s", proposed)
        self.assertTrue(proposed.startswith("# Review-pending"))

    def test_wrong_successor_semantic_result_rejects(self):
        h=fake_result("SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                      dual.successor_gate)
        h["mutations"]["omit_baseline_reporting_error"]["status"]="SKIPPED"
        with self.assertRaises(dual.DualA2Error):
            dual.validate_run(h,"SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                              dual.successor_gate.MUTATIONS,
                              dual.successor_gate.DECLS)


    def test_real_a2_both_legs_refuse_fake_green_status(self):
        """A mock receipt cannot hide failed positives or accepted mutants."""
        for gate,status in ((dual.historical_gate,
                            "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING"),
                           (dual.successor_gate,
                            "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING")):
            original=fake_result(status,gate)
            self.assertTrue(dual.validate_run(original,status,gate.MUTATIONS,
                                              gate.DECLS))
            mutate = next(iter(gate.MUTATIONS))
            broken = [
                lambda x: x["commands"][0].update(returncode=1),
                lambda x: next(q for q in x["commands"] if
                               q["label"]==mutate).update(returncode=0),
                lambda x: x["commands"].append(dict(x["commands"][0])),
                lambda x: x["commands"][0].update(log_sha256="x"*64),
                lambda x: x["commands"].pop(4),
                lambda x: x["mutations"][mutate].update(
                    mutant_source_sha256="b"*64),
                lambda x: x["mutations"][mutate].update(
                    positive_source_sha256="not-an-authentic-digest"),
            ]
            for edit in broken:
                with self.subTest(status=status,edit=edit):
                    candidate=json.loads(json.dumps(original))
                    edit(candidate)
                    with self.assertRaises(dual.DualA2Error):
                        dual.validate_run(candidate,status,gate.MUTATIONS,
                                          gate.DECLS)

