"""Synthetic negative adversaries for the PR115/PR113 trust-boundary adapter."""
from __future__ import annotations

from pathlib import Path
import subprocess
import tempfile
import unittest
import json
import hashlib

import pr113_tooling_migration as migration
from pr115_archive_transition_guard_v1 import diagnose, FORMAT


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(['git', *args], cwd=root, text=True).strip()


def commit(root: Path, message: str) -> str:
    subprocess.run(['git', 'add', '-A'], cwd=root, check=True)
    subprocess.run(['git', '-c', 'user.name=Fixture', '-c',
                    'user.email=fixture@example.invalid', 'commit', '-qm', message],
                   cwd=root, check=True)
    return git(root, 'rev-parse', 'HEAD')


class ArchiveTransitionGuardTests(unittest.TestCase):
    def fixture(self, root):
        subprocess.run(['git', 'init', '-q'], cwd=root, check=True)
        original = {
            'verification/integrity/workflow_contract.py': b'historical contract\n',
            'verification/integrity/tests/test_workflow.py': b'historical tests\n',
            'verification/archive/verify_bundle.py': b'historical verifier\n',
            'archival/v0.2.0/README.md': b'historical guide\n',
        }
        for name, data in original.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        t=commit(root, 'synthetic historical tooling T')
        supplement=root / migration.SUPPLEMENT
        rows=[]
        for name,data in sorted(original.items()):
            path=supplement / 'tooling' / name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(data)
            rows.append({'path':name, 'blob':git(root,'rev-parse',f'{t}:{name}'),
                         'sha256':hashlib.sha256(data).hexdigest()})
        (supplement/'archive-manifest.json').write_text(json.dumps({
            'tooling':{'source_commit':t,'files':rows}}))
        for n in range(25):
            path=root/'.github/workflows'/f'historical-{n:02d}.yml'
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text('name: fixture\n')
        b=commit(root,'synthetic packaged release B')
        for name in migration.EXPECTED_CHANGES:
            (root/name).write_text('changed reviewed workflow profile\n')
        h=commit(root,'synthetic candidate H')
        return t,b,h

    def test_reuses_original_t_exact_source_and_never_grants_review(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);t,b,h=self.fixture(root)
            result=diagnose(root,h,include_staged=False,original_t=t,original_b=b)
            self.assertEqual(result['format'],FORMAT)
            self.assertEqual(result['status'],'CLOSURE_DRIFT_IDENTIFIED_REVIEW_REQUIRED')
            self.assertEqual(result['current_workflow_count'],25)
            self.assertEqual(result['historical_tooling_file_count'],4)
            self.assertEqual({v['path'] for v in result['changed_tooling_blobs']},migration.EXPECTED_CHANGES)
            for blocked in ('original_archive_current_candidate_gate_passed',
                            'historical_archive_repair_accepted','mathematical_acceptance',
                            'publication_authorized'):
                self.assertIs(result[blocked],False)
            self.assertTrue(result['requires_independent_security_review'])
            self.assertTrue(result['requires_distinct_original_T_offline_execution'])
            self.assertTrue(result['requires_current_H_integrity_execution'])

    def test_current_source_mutation_outside_exact_two_files_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);t,b,h=self.fixture(root)
            (root/'verification/archive/verify_bundle.py').write_text('unauthorized verifier modification')
            h2=commit(root,'mutated historical verifier')
            with self.assertRaises(migration.ToolingMigrationError):
                diagnose(root,h2,include_staged=False,original_t=t,original_b=b)

    def test_archive_repackaging_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);t,b,h=self.fixture(root)
            archive=root/migration.SUPPLEMENT/'tooling/verification/archive/verify_bundle.py'
            archive.write_text('not original T tooling')
            h2=commit(root,'forged T snapshot')
            with self.assertRaises(migration.ToolingMigrationError):
                diagnose(root,h2,include_staged=False,original_t=t,original_b=b)

    def test_dirty_or_stale_source_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);t,b,h=self.fixture(root)
            with self.assertRaises(migration.ToolingMigrationError):
                diagnose(root,b,include_staged=False,original_t=t,original_b=b)
            (root/'some-extra.txt').write_text('untracked')
            with self.assertRaises(migration.ToolingMigrationError):
                diagnose(root,h,include_staged=False,original_t=t,original_b=b)

    def test_missing_workflow_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);t,b,h=self.fixture(root)
            (root/'.github/workflows/historical-00.yml').unlink()
            h2=commit(root,'removed one active workflow')
            with self.assertRaises(migration.ToolingMigrationError):
                diagnose(root,h2,include_staged=False,original_t=t,original_b=b)

    def test_no_stage_cannot_invent_thirty_active_workflows(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);t,b,h=self.fixture(root)
            result=diagnose(root,h,include_staged=False,original_t=t,original_b=b)
            self.assertIsNone(result['proposed_staged_workflow_count'])
            self.assertFalse(result['original_archive_current_candidate_gate_passed'])
            self.assertFalse(result['historical_archive_repair_accepted'])

    def test_real_repository_cannot_launder_historical_status(self):
        root=Path(__file__).resolve().parents[2]
        if not (root/'.git').exists():
            self.skipTest('standalone source snapshot lacks genuine Git object history')
        head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
        result=diagnose(root,head,include_staged=True)
        self.assertEqual(result['historical_tooling_file_count'],35)
        self.assertEqual(result['proposed_staged_workflow_count'],30)
        self.assertFalse(result['historical_archive_repair_accepted'])
        self.assertFalse(result['original_archive_current_candidate_gate_passed'])


if __name__ == '__main__':unittest.main()
