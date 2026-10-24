"""The dual A2 harness must execute both checks, never autoapprove either."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import pr113_dual_a2_compiler as dual


def fake_result(status, gate):
    command_names = ["compiler_version","research_build","signatures_axioms",
                     "positive_fixture",*gate.MUTATIONS]
    return {
        "status":status,
        "source_unchanged":True,
        "declarations":{name:[] for name in gate.DECLS},
        "mutations":{name:{"status":"SEMANTICALLY_REJECTED"}
                     for name in gate.MUTATIONS},
        "commands":[{"label":name,"returncode":0,
                     "log_sha256":"a"*64} for name in command_names],
        "independent_security_review":False,
        "historical_a2_verifier_replaced":False,
        "mathematical_acceptance":False,
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
                 mock.patch.object(dual.historical_gate,"verify",
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
                 mock.patch.object(dual.historical_gate,"verify",return_value=h), \
                 mock.patch.object(dual.successor_gate,"verify") as s:
                with self.assertRaises(dual.DualA2Error):
                    dual.execute(old,"a"*40,now,"b"*40,root/"out")
                s.assert_not_called()

    def test_wrong_successor_semantic_result_rejects(self):
        h=fake_result("SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                      dual.successor_gate)
        h["mutations"]["omit_baseline_reporting_error"]["status"]="SKIPPED"
        with self.assertRaises(dual.DualA2Error):
            dual.validate_run(h,"SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                              dual.successor_gate.MUTATIONS,
                              dual.successor_gate.DECLS)
