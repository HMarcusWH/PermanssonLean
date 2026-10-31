"""IMPLEMENTATION_MANIFEST.json stays a truthful inventory of the tracked tree.

`scripts/inventory.py --check` must pass, and each invariant it promises must
catch the corresponding stale or malformed state: numeric-key spread records,
historical facts overwritten, tracked files without a row, untracked rows
without a disposition, dangling supersessions or related files, stale current
counts, historical records not marked as non-evidence, and rows that claim
CI results the tracked tree cannot hold.
"""
from __future__ import annotations
from copy import deepcopy
from pathlib import Path
import subprocess
import sys
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'scripts'))
import inventory
sys.path.pop(0)


def _repo():
    try:
        return inventory.repository()
    except inventory.InventoryError:
        return None


REPO=_repo()


@unittest.skipUnless(REPO and (REPO/inventory.APP_PREFIX).is_dir(),'needs the Git checkout that contains the application')
class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.manifest=inventory.load()

    def problems(self,manifest):
        return inventory.check(REPO,manifest)

    def test_manifest_passes_its_inventory_check(self):
        self.assertEqual(self.problems(self.manifest),[])
        current=self.manifest['current_inventory']
        self.assertEqual(current['application_tracked_files_without_row'],0)
        self.assertEqual(current['absent_rows'],sum(current['absent_rows_by_disposition'].values()))
        self.assertNotIn('MISSING',current['absent_rows_by_disposition'])

    def test_numeric_key_spread_record_rejected(self):
        bad=deepcopy(self.manifest)
        bad['historical']['round_records']['v15_candidate_summary']['text']={str(i):c for i,c in enumerate('PASS')}
        self.assertTrue(any('numeric-key' in p for p in self.problems(bad)))

    def test_historical_planning_counts_are_frozen(self):
        bad=deepcopy(self.manifest)
        bad['historical']['planning_counts']['v2']=345
        self.assertTrue(any('historical planning counts' in p for p in self.problems(bad)))

    def test_historical_record_cannot_become_evidence(self):
        name=next(iter(self.manifest['historical']['round_records']))
        for forged in ({'evidence_status':'PASS'},{'evidence_status':'EXACT_HEAD_CI_SUCCESS'},
                       {'evidence_status':'EXACT_HEAD_CI_SUCCESS','github_run_id':41166380739}):
            bad=deepcopy(self.manifest)
            bad['historical']['round_records'][name].update(forged)
            with self.subTest(forged=forged):
                self.assertTrue(any('non-evidence' in p for p in self.problems(bad)))

    def test_tracked_row_cannot_claim_ci_evidence(self):
        """INV-02/INV-05: CI results live outside the tracked manifest, with or without a run identity."""
        for state in ('EXACT_HEAD_CI_PASSED','LOCAL_TESTED_GITHUB_LEAN_PASSED','CI_GREEN_RUN_41166380739'):
            bad=deepcopy(self.manifest)
            row=next(e for e in bad['entries'] if e.get('candidate'))
            row['candidate']['state']=state
            with self.subTest(state=state):
                self.assertTrue(any('claims CI evidence' in p for p in self.problems(bad)))

    def test_tracked_file_without_row_detected(self):
        bad=deepcopy(self.manifest)
        bad['entries']=[e for e in bad['entries'] if not e['path'].endswith('/scripts/inventory.py')]
        self.assertTrue(any('without a manifest row' in p for p in self.problems(bad)))

    def test_absent_row_needs_a_valid_disposition(self):
        for value in (None,'IMPLEMENTED','PLANNED'):
            bad=deepcopy(self.manifest)
            entry=next(e for e in bad['entries'] if e.get('disposition_current')=='DEFERRED_CONTRACT_LAYER')
            if value is None:
                entry.pop('disposition_current')
            else:
                entry['disposition_current']=value
            with self.subTest(value=value):
                self.assertTrue(any('valid disposition' in p for p in self.problems(bad)))

    def test_tracked_row_cannot_claim_an_absent_disposition(self):
        bad=deepcopy(self.manifest)
        entry=next(e for e in bad['entries'] if e['path'].endswith('/scripts/inventory.py'))
        entry['disposition_current']='DEFERRED_SCOPE'
        self.assertTrue(any('tracked but carries' in p for p in self.problems(bad)))

    def test_dangling_supersession_and_related_files_rejected(self):
        bad=deepcopy(self.manifest)
        entry=next(e for e in bad['entries'] if e.get('disposition_current')=='SUPERSEDED_BY_IMPLEMENTED_EQUIVALENT')
        entry['candidate']['superseded_by']=['apps/permansson/application-successor/no/such/file.py']
        self.assertTrue(any('superseded_by' in p for p in self.problems(bad)))
        bad=deepcopy(self.manifest)
        entry=next(e for e in bad['entries'] if e.get('disposition_current')=='DEFERRED_ALTERNATE_LAYOUT')
        entry['related_implemented']=[]
        self.assertTrue(any('related_implemented' in p for p in self.problems(bad)))

    def test_only_build_products_may_be_excluded_as_generated(self):
        bad=deepcopy(self.manifest)
        entry=next(e for e in bad['entries'] if e.get('disposition_current')=='DEFERRED_CONTRACT_LAYER')
        entry['disposition_current']='EXCLUDED_GENERATED_BUILD_PRODUCT'
        self.assertTrue(any('only build/lib' in p for p in self.problems(bad)))

    def test_stale_current_inventory_detected(self):
        bad=deepcopy(self.manifest)
        bad['current_inventory']['research_bridge_modules']=2
        self.assertTrue(any('stale' in p for p in self.problems(bad)))

    def test_vendored_fixtures_keep_their_upstream_digests(self):
        rows=[e for e in self.manifest['entries'] if e['candidate']['state']=='VENDORED_THIRD_PARTY_TEST_FIXTURE']
        self.assertEqual(len(rows),12)
        for row in rows:
            self.assertEqual(row['provenance']['commit'],'32a48195b9b20fe67b1795e39e4509f14d860b45')
            self.assertEqual(row['provenance']['license'],'Apache-2.0')

    def test_command_line_check(self):
        p=subprocess.run([sys.executable,'-B',str(APP/'scripts/inventory.py'),'--check'],cwd=APP,text=True,
                         capture_output=True,timeout=120)
        self.assertEqual(p.returncode,0,p.stdout[-2000:]+p.stderr[-2000:])


if __name__=='__main__':
    unittest.main()
