"""Exact adaptive admitted-block control: optimum, timing, admission and adversaries."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.adaptive import propose_adaptive
from permansson_app.receipts.adaptive import check_adaptive

EXAMPLE=Path(__file__).resolve().parents[1]/'src/permansson_app/data/examples/adaptive.v1.json'


def request():
    return json.loads(EXAMPLE.read_text())


class AdaptiveTests(unittest.TestCase):
    def test_adaptive_beats_every_admitted_frozen_block(self):
        raw=request();receipt=propose_adaptive(raw)
        self.assertEqual(check_adaptive(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['frozen_block_values'],[['1/4','1/4'],['3/8','3/8'],['3/8','3/8']])
        self.assertEqual(receipt['adaptive_values'],['9/16','9/16'])
        self.assertEqual(receipt['adaptivity_gain'],['3/16','3/16'])
        # Apply calm0 in s0 and calm1 in s1: the unadmitted joint block is never assumed.
        self.assertEqual(receipt['optimal_blocks'],[[[0,[1]],[2,[2]]],[[0,[1]],[2,[2]]]])
        self.assertEqual(receipt['monitor_table'][1][0],['0','3/4'])
        self.assertIs(receipt['P_held_fixed'],True)

    def test_admitting_the_joint_block_removes_the_gain(self):
        raw=request();raw['grammar']['admitted_blocks'].append(['calm0','calm1'])
        receipt=propose_adaptive(raw)
        self.assertEqual(check_adaptive(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['best_frozen_values'],['9/16','9/16'])
        self.assertEqual(receipt['adaptivity_gain'],['0','0'])
        # Both the joint block and the matching single block are tied optima.
        self.assertEqual(receipt['optimal_blocks'][0],[[0,[1,3]],[2,[2,3]]])

    def test_exit_objective_maximizes_exit(self):
        raw=request();raw['grammar']['value_type']='exit_by_horizon'
        receipt=propose_adaptive(raw)
        self.assertEqual(check_adaptive(raw,receipt)['status'],'PASS')
        # Staying with the baseline (no block) exits most often: 1 - 1/4.
        self.assertEqual(receipt['adaptive_values'],['3/4','3/4'])
        self.assertEqual(receipt['adaptivity_gain'],['0','0'])
        self.assertEqual(receipt['monitor_table'][0][0],['1','0'])

    def test_zero_horizon_and_single_block(self):
        raw=request();raw['grammar']['horizon']=0
        receipt=propose_adaptive(raw)
        self.assertEqual((receipt['adaptive_values'],receipt['optimal_blocks']),(['1','1'],[]))
        raw=request();raw['grammar']['admitted_blocks']=[[]]
        receipt=propose_adaptive(raw)
        self.assertEqual(receipt['adaptive_values'],['1/4','1/4'])
        self.assertEqual(receipt['adaptivity_gain'],['0','0'])

    def test_tampered_receipts_rejected(self):
        raw=request();receipt=propose_adaptive(raw)
        tampered=[('adaptive_values',['3/8','9/16']),('adaptivity_gain',['0','3/16']),
                  ('best_frozen_values',['9/16','9/16']),('optimal_blocks',[[[0,[1,2]],[2,[2]]],[[0,[1]],[2,[2]]]]),
                  ('policy_class','MARKOV_FROZEN'),('P_held_fixed',False),('lean_status','PASS')]
        for key,value in tampered:
            bad=copy.deepcopy(receipt);bad[key]=value
            with self.subTest(key=key),self.assertRaises(AppError):check_adaptive(raw,bad)
        bad=copy.deepcopy(receipt);bad['monitor_table'][2][0][1]='5/8'
        with self.assertRaises(AppError):check_adaptive(raw,bad)
        bad=copy.deepcopy(receipt);bad['extra']=1
        with self.assertRaises(AppError):check_adaptive(raw,bad)

    def test_receipt_for_different_dynamics_rejected(self):
        raw=request();receipt=propose_adaptive(raw)
        other=copy.deepcopy(raw)
        other['grammar']['baseline']['P'][1]['weights']={'safe':'1','outside':'0'}
        with self.assertRaises(AppError):check_adaptive(other,receipt)

    def test_input_scope(self):
        for mutate in (lambda r:r.__setitem__('format','other'),
                       lambda r:r.__setitem__('extra',1),
                       lambda r:r['grammar'].__setitem__('horizon',9),
                       lambda r:r['grammar']['admitted_blocks'].remove([]),
                       lambda r:r['grammar']['admitted_blocks'].append(['calm1','calm0'])):
            raw=request();mutate(raw)
            with self.assertRaises(AppError):propose_adaptive(raw)


if __name__=='__main__':
    unittest.main()
