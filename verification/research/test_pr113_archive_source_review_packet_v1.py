"""Review packet is read-only real Git inventory, not external approval."""
import unittest
from unittest import mock

import pr113_archive_source_review_packet_v1 as packet
from pr113_tooling_migration import ROOT, git, ToolingMigrationError


class SourcePacketTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.head=git(ROOT,"rev-parse","HEAD").decode().strip()

    def test_exact_real_T_B_H_35_and_virtual_30_unapproved(self):
        actual=packet.produce(self.head)
        self.assertEqual(actual["tooling_file_count"],35)
        self.assertEqual(len(actual["historical_tooling"]),35)
        self.assertEqual(sum(x["changed"] for x in actual["historical_tooling"]),2)
        self.assertEqual(len(actual["virtual_workflow_git_blobs"]),30)
        self.assertEqual(actual["actual_active_workflows"],25)
        self.assertFalse(actual["independent_security_review"])
        self.assertFalse(actual["current_required_archive_check_passed"])
        self.assertFalse(actual["owner_activation_authorized"])
        self.assertFalse(actual["publication_authorized"])

    def test_packet_refuses_forged_successor_workflow_count(self):
        actual=packet.workflow_audit
        def forged(*args,**kwargs):
            result=actual(*args,**kwargs)
            return {**result,"current_reviewed_workflow_count":31}
        with mock.patch.object(packet,"workflow_audit",side_effect=forged):
            with self.assertRaises(packet.PacketError):
                packet.produce(self.head)

    def test_packet_refuses_extra_canonical_blob_even_if_two_known_differ(self):
        original=packet.exact_tree
        def altered(root,rev,*prefixes):
            rows=original(root,rev,*prefixes)
            if rev==self.head and "verification/archive/verify_bundle.py" in rows:
                rows=dict(rows)
                rows["verification/archive/verify_bundle.py"]=(
                    rows["verification/archive/verify_bundle.py"][0], "f"*40)
            return rows
        with mock.patch.object(packet,"exact_tree",side_effect=altered):
            with self.assertRaises(packet.PacketError):
                packet.produce(self.head)


if __name__=="__main__":
    unittest.main()
