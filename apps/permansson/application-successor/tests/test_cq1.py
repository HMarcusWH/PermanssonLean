"""Exact CQ-1 finite certificate: region-wide persistence, margin and adversaries."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.cq1 import propose_cq1
from permansson_app.receipts.cq1 import check_cq1

EXAMPLE=Path(__file__).resolve().parents[1]/'src/permansson_app/data/examples/cq1.v1.json'


def request(**changes):
    return dict(json.loads(EXAMPLE.read_text()),**changes)


class CQ1Tests(unittest.TestCase):
    def test_example_certificate_is_exact(self):
        raw=request();receipt=propose_cq1(raw)
        self.assertEqual(check_cq1(raw,receipt)['status'],'PASS')
        self.assertEqual([r['survival'] for r in receipt['region_survival']],['81/100','16/25'])
        self.assertEqual(receipt['min_region_survival'],'16/25')
        self.assertEqual([e['effect'] for e in receipt['comparison_effects']],['8/25','39/100'])
        self.assertEqual(receipt['uniform_margin'],'8/25')
        self.assertEqual(receipt['margin_attained_at'],[['calm','ok']])
        self.assertEqual(receipt['certificate_status'],'FINITE_CONSTITUTIVE_CERTIFICATE')
        self.assertIs(receipt['exact_GR_or_PR_certified'],False)
        self.assertEqual(receipt['lean_status'],'NOT_EXECUTED')

    def test_zero_horizon_has_no_path_effect(self):
        raw=request(horizon=0);receipt=propose_cq1(raw)
        self.assertEqual(check_cq1(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['uniform_margin'],'0')
        self.assertEqual(receipt['failed_conditions'],['ZERO_UNIFORM_MARGIN'])
        self.assertEqual(receipt['certificate_status'],'NOT_CERTIFIED')

    def test_persistence_is_checked_on_the_whole_region(self):
        # Adding (calm, bad) to the region leaves the comparison set and its
        # effects unchanged, but that region-only state survives with 1/4.
        raw=request(region=[['calm','ok'],['alert','ok'],['calm','bad']])
        receipt=propose_cq1(raw)
        survival={tuple(r['state']):r['survival'] for r in receipt['region_survival']}
        self.assertEqual(survival,{('calm','ok'):'19/20',('alert','ok'):'16/25',('calm','bad'):'1/4'})
        self.assertEqual(receipt['uniform_margin'],'8/25')
        self.assertEqual(receipt['failed_conditions'],['REGION_PERSISTENCE_BELOW_1_MINUS_ETA'])
        self.assertEqual(check_cq1(raw,receipt)['certificate_status'],'NOT_CERTIFIED')

    def test_comparison_needs_two_states_inside_basin(self):
        for change in ({'comparison':[['calm','ok']]},
                       {'comparison':[['calm','ok'],['calm','bad']]},
                       {'basin':[['calm','ok'],['calm','bad']],'comparison':[['calm','ok'],['calm','bad']]}):
            with self.subTest(change=change),self.assertRaises(AppError):
                propose_cq1(request(**change))

    def test_undeclared_or_structural_changes_rejected(self):
        raw=request();raw['intervention']['target']='U'
        with self.assertRaises(AppError):propose_cq1(raw)
        raw=request();raw['intervention']['treated']['P'][0]['weights']={'ok':'1/2','bad':'1/2'}
        with self.assertRaises(AppError):propose_cq1(raw)

    def test_tampered_receipts_rejected(self):
        raw=request();receipt=propose_cq1(raw)
        mutations=[]
        bad=copy.deepcopy(receipt);bad['uniform_margin']='39/100';mutations.append(bad)
        bad=copy.deepcopy(receipt);bad['region_survival'][1]['survival']='81/100';mutations.append(bad)
        bad=copy.deepcopy(receipt);bad['margin_attained_at']=[['alert','ok']];mutations.append(bad)
        bad=copy.deepcopy(receipt);bad['exact_GR_or_PR_certified']=True;mutations.append(bad)
        bad=copy.deepcopy(receipt);bad['region_survival']=bad['region_survival'][:1];mutations.append(bad)
        for item in mutations:
            with self.subTest(),self.assertRaises(AppError):
                check_cq1(raw,item)
        failing=request(eta='1/4');bad=propose_cq1(failing)
        bad['certificate_status']='FINITE_CONSTITUTIVE_CERTIFICATE';bad['failed_conditions']=[]
        with self.assertRaises(AppError):check_cq1(failing,bad)


if __name__=='__main__':
    unittest.main()
