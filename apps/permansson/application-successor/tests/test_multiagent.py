"""Exact finite two-player protocols: kernels, protocols and adversaries."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.multiagent import propose_multiagent
from permansson_app.receipts.multiagent import check_multiagent

EXAMPLE=Path(__file__).resolve().parents[1]/'src/permansson_app/data/examples/multiagent.v1.json'


def request():
    return json.loads(EXAMPLE.read_text())


class MultiAgentTests(unittest.TestCase):
    def test_example_kernels(self):
        raw=request();receipt=propose_multiagent(raw)
        self.assertEqual(check_multiagent(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['baseline_kernel'][0],['27/64','1/64','9/64','3/64','9/64','3/64','3/64','9/64'])
        self.assertEqual(receipt['closed_open_max_tv'],'3/16')
        self.assertIs(receipt['physical_P_changed'],False)
        self.assertEqual(len(receipt['joint_states']),8)

    def test_matching_anchor_makes_protocols_coincide(self):
        # With the anchor equal to the baseline profile, open loop equals closed loop.
        raw=request();raw['anchor']=copy.deepcopy(raw['players'])
        receipt=propose_multiagent(raw)
        self.assertEqual(receipt['closed_loop_kernel'],receipt['open_loop_kernel'])
        self.assertEqual(receipt['closed_open_max_tv'],'0')

    def test_treated_player_matters(self):
        raw=request();a=propose_multiagent(raw)
        raw['treated_player']=1;b=propose_multiagent(raw)
        self.assertNotEqual(a['closed_loop_kernel'],b['closed_loop_kernel'])

    def test_invalid_tables_rejected(self):
        raw=request();raw['players'][0]['action'][0]=['1/2','1/4']
        with self.assertRaises(AppError):propose_multiagent(raw)
        raw=request();raw['world']=raw['world'][1:]
        with self.assertRaises(AppError):propose_multiagent(raw)
        raw=request();raw['labels']['actions']=['a','b','c']
        with self.assertRaises(AppError):propose_multiagent(raw)

    def test_tampered_receipts_rejected(self):
        raw=request();receipt=propose_multiagent(raw)
        cases=[]
        b=copy.deepcopy(receipt);b['closed_loop_kernel'],b['open_loop_kernel']=b['open_loop_kernel'],b['closed_loop_kernel'];cases.append(b)
        b=copy.deepcopy(receipt);b['baseline_kernel'][0][0]='1/2';cases.append(b)
        b=copy.deepcopy(receipt);b['closed_open_max_tv']='0';cases.append(b)
        b=copy.deepcopy(receipt);b['physical_P_changed']=True;cases.append(b)
        for item in cases:
            with self.subTest(),self.assertRaises(AppError):
                check_multiagent(raw,item)


if __name__=='__main__':
    unittest.main()
