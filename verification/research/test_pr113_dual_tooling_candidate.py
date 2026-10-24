"""Dual T/H report regression tests; mocks NEVER simulate real archive approval."""
import copy
import unittest
import pr113_dual_tooling_candidate as dual

T=dual.T
H="a"*40

def fixture():
    historical={
        "check":"archive-reproducibility",
        "status":"PASS",
        "details":{
            "acceptance_scope":"accepted_artifact_replay_only",
            "isolation":{"network_isolation":"ENFORCED",
                         "capabilities":"all_zero"},
        },
    }
    current={
        "status":"PASS","suite":"workflow",
        "execution_tracked_clean":True,
        "methods_run":9,
    }
    return historical,current

class DualToolingTests(unittest.TestCase):
    def test_historical_and_new_provenance_stays_unapproved(self):
        old,now=fixture()
        result=dual.validate_dual_reports(old,now,T_source=T,H_source=H)
        self.assertEqual(result["status"],"DUAL_T_AND_H_EXECUTED_UNREVIEWED")
        self.assertTrue(result["original_T_archive_offline_restoration_passed"])
        self.assertFalse(result["independent_security_review"])
        self.assertFalse(result["required_current_archive_CI_green"])
        self.assertFalse(result["mathematical_release_approved"])

    def test_missing_isolation_or_bypassed_historical_T_fails(self):
        for key,value in [("status","FAIL"),("details",{}),
                          ("check","wrong context")]:
            old,now=fixture()
            old[key]=value
            with self.subTest(key=key), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)
        for fault in ("network_isolation","capabilities"):
            old,now=fixture()
            old["details"]["isolation"][fault]="NOT_ENFORCED"
            with self.subTest(fault=fault), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)

    def test_unexecuted_current_workflow_or_dirty_source_rejected(self):
        for key,value in [("status","FAIL"),
                          ("suite","reference"),
                          ("execution_tracked_clean",False),
                          ("methods_run",0)]:
            old,now=fixture()
            now[key]=value
            with self.subTest(key=key), self.assertRaises(dual.DualToolingError):
                dual.validate_dual_reports(old,now,T_source=T,H_source=H)
