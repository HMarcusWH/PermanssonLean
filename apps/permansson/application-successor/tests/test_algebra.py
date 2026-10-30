"""Exact rational algebra witnesses: every profile, premises and adversaries."""
from __future__ import annotations
import copy
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.algebra import propose_algebra, ldl
from permansson_app.receipts.algebra import check_algebra
from fractions import Fraction as F

R='Permansson.App.RationalAlgebraRequest.v1'
SEAM={'format':R,'profile':'seam','H':[['2','1','1'],['1','0','0'],['1','0','0']],'pivot':1}
COMMON={'format':R,'profile':'seam','H':[['3','3'],['3','3']],'pivot':0}
SCHUR={'format':R,'profile':'schur','H':[['2','1'],['1','2']],'B':[['1'],['0']],'C':[['1']],'ell':'-1'}
COMPAT={'format':R,'profile':'singular','H':[['1','1'],['1','1']],'b':['2','2'],'c':'3'}
INCOMPAT={'format':R,'profile':'singular','H':[['1','1'],['1','1']],'b':['1','0'],'c':'3'}
GRAM={'format':R,'profile':'gram','x':['1','0','0'],'y':['1','1','0'],'c':'2'}


class AlgebraTests(unittest.TestCase):
    def test_every_profile_round_trips(self):
        expected={'seam':'SEAM_RANK_AT_MOST_TWO','common':'COMMON_MODE_RANK_AT_MOST_ONE',
                  'schur':'SHELL_COMPLEMENT_IDENTIFIED','compat':'NEGATIVE_BORDERED_DIRECTION',
                  'incompat':'INCOMPATIBLE_NEGATIVE_DIRECTION','gram':'POSITIVE_GAP_SEPARATION'}
        for name,raw in (('seam',SEAM),('common',COMMON),('schur',SCHUR),('compat',COMPAT),
                         ('incompat',INCOMPAT),('gram',GRAM)):
            receipt=propose_algebra(raw)
            self.assertEqual(receipt['status'],expected[name])
            self.assertEqual(check_algebra(raw,receipt)['status'],'PASS')
            self.assertEqual(receipt['feature_identification'],'NOT_ESTABLISHED_EXPLICIT_PREMISE')

    def test_exact_values(self):
        r=propose_algebra(SCHUR)
        self.assertEqual(r['shell_complement'],[['13/8']])
        self.assertEqual(r['psd_witness'],{'L':[['1','0'],['1/2','1']],'d':['2','3/2']})
        r=propose_algebra(COMPAT)
        self.assertEqual((r['preimage'],r['gap']),(['2','0'],'-1'))
        r=propose_algebra(dict(COMPAT,c='5'))
        self.assertEqual(r['status'],'NONNEGATIVE_BORDERED_FORM')
        r=propose_algebra(GRAM)
        self.assertEqual((r['gap'],r['witness'],r['threshold'],r['signed_value']),('1',['0','1','0'],'2','-2'))

    def test_premise_failures(self):
        r=propose_algebra(dict(SEAM,H=[['1','2','0'],['2','0','0'],['0','0','5']]))
        self.assertEqual(r['status'],'SEAM_PREMISES_FAIL')
        self.assertIsNone(ldl([[F(1),F(2)],[F(2),F(1)]]))
        for bad in (dict(SCHUR,H=[['1','2'],['2','1']]),dict(SCHUR,ell='0'),
                    dict(COMPAT,H=[['1','2'],['0','1']]),dict(GRAM,c='0')):
            with self.subTest(bad=bad),self.assertRaises(AppError):
                propose_algebra(bad)
        self.assertEqual(propose_algebra(dict(GRAM,y=['2','0','0']))['status'],'ZERO_GAP_NO_SEPARATION')

    def test_tampered_receipts_rejected(self):
        cases=[]
        r=propose_algebra(SCHUR);b=copy.deepcopy(r);b['shell_complement']=[['3/2']];cases.append((SCHUR,b))
        b=copy.deepcopy(r);b['psd_witness']['d']=['2','-3/2'];cases.append((SCHUR,b))
        r=propose_algebra(COMPAT);b=copy.deepcopy(r);b['gap']='1';cases.append((COMPAT,b))
        b=copy.deepcopy(r);b['preimage']=['1','0'];cases.append((COMPAT,b))
        r=propose_algebra(INCOMPAT);b=copy.deepcopy(r);b['kernel_witness']=['1','1'];cases.append((INCOMPAT,b))
        r=propose_algebra(GRAM);b=copy.deepcopy(r);b['threshold']='3';cases.append((GRAM,b))
        r=propose_algebra(SEAM);b=copy.deepcopy(r);b['status']='COMMON_MODE_RANK_AT_MOST_ONE';cases.append((SEAM,b))
        for raw,item in cases:
            with self.subTest(),self.assertRaises(AppError):
                check_algebra(raw,item)


if __name__=='__main__':
    unittest.main()
