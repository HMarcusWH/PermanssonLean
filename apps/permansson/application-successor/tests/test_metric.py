"""Exact finite W1 contraction receipts: certificates, maxima and adversaries."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.metric import propose_metric, transport
from permansson_app.receipts.metric import check_metric
from fractions import Fraction as F

EXAMPLE=Path(__file__).resolve().parents[1]/'src/permansson_app/data/examples/metric.v1.json'


def request():
    return json.loads(EXAMPLE.read_text())


class MetricTests(unittest.TestCase):
    def test_example_contraction_and_bound(self):
        raw=request();receipt=propose_metric(raw)
        self.assertEqual(check_metric(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['contraction_factor'],'1/2')
        self.assertEqual(receipt['defect'],'1/4')
        self.assertEqual(receipt['invariant_law'],['1/4','1/4','1/4','1/4'])
        self.assertEqual(receipt['perturbed_invariant_law'],['1/3','1/6','1/3','1/6'])
        self.assertEqual(receipt['invariant_transport']['w1'],'1/6')
        self.assertEqual(receipt['invariant_bound'],'1/2')
        self.assertEqual(receipt['contraction_status'],'STRICT_W1_CONTRACTION')

    def test_transport_primal_equals_dual(self):
        d=((F(0),F(1),F(2)),(F(1),F(0),F(1)),(F(2),F(1),F(0)))
        value,coupling,potential=transport((F(1),F(0),F(0)),(F(0),F(0),F(1)),d)
        self.assertEqual(value,2)
        self.assertEqual(coupling[0][2],1)
        self.assertEqual(potential[0]-potential[2],2)

    def test_reducible_or_noncontractive_kernels(self):
        raw=request()
        for row in raw['baseline']['P']:
            row['weights']={x:('1' if x==row['x'] else '0') for x in row['weights']}
        with self.assertRaises(AppError):
            propose_metric(raw)  # a frozen world splits the chain: no unique invariant law
        raw=request()
        for row in raw['baseline']['P']:
            row['weights']={x:('0' if x==row['x'] else '1') for x in row['weights']}
        receipt=propose_metric(raw)  # a deterministic world flip is nonexpansive, not contractive
        self.assertEqual(receipt['contraction_factor'],'1')
        self.assertEqual(receipt['contraction_status'],'NOT_CONTRACTIVE')
        self.assertIsNone(receipt['invariant_bound'])
        self.assertEqual(check_metric(raw,receipt)['contraction_status'],'NOT_CONTRACTIVE')

    def test_invalid_metrics_rejected(self):
        raw=request();raw['metric'][0]['distance']='5'
        with self.assertRaises(AppError):propose_metric(raw)   # triangle inequality
        raw=request();raw['metric']=raw['metric'][1:]
        with self.assertRaises(AppError):propose_metric(raw)   # missing pair

    def test_tampered_receipts_rejected(self):
        raw=request();receipt=propose_metric(raw)
        cases=[]
        bad=copy.deepcopy(receipt);bad['contraction_factor']='1/3';cases.append(bad)
        bad=copy.deepcopy(receipt);bad['invariant_bound']='1/6';cases.append(bad)
        bad=copy.deepcopy(receipt);bad['invariant_transport']['w1']='1/4';cases.append(bad)
        bad=copy.deepcopy(receipt)
        bad['invariant_transport']['coupling']=[[str(F(a)*F(b)) for b in receipt['perturbed_invariant_law']]
                                                for a in receipt['invariant_law']]
        cases.append(bad)  # a feasible but non-optimal coupling cannot certify the distance
        bad=copy.deepcopy(receipt);bad['row_defects'][0]['potential']=['0','2','0','0'];cases.append(bad)
        bad=copy.deepcopy(receipt);bad['scientific_claims_verified']=True;cases.append(bad)
        for item in cases:
            with self.subTest(),self.assertRaises(AppError):
                check_metric(raw,item)


if __name__=='__main__':
    unittest.main()
