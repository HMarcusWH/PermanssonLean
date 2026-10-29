"""Actual original LP/Farkas source binding and all scientific-status boundaries."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import sys
import tempfile
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.lp_types import parse_lp
from permansson_app.engines.lp import propose_lp_optimum
from permansson_app.proof.lp_emit import emit_source,emit_files
from permansson_app.proof.lp_source_check import check_files
from permansson_app.errors import AppError

MODEL=APP/'src/permansson_app/data/examples/lp.v1.model.json'


def optimal_fixture():
    raw=json.loads(MODEL.read_text())
    lp=parse_lp(raw)
    candidate=propose_lp_optimum(lp)
    assert candidate['status']=='CHECKED_OPTIMAL_CANDIDATE'
    return raw,candidate['receipt']


def farkas_fixture():
    raw=json.loads(MODEL.read_text())
    raw['constraints']=[{'id':'contradiction','coefficients':{'x':'1','y':'0'},'relation':'<=','rhs':'-1'}]
    lp=parse_lp(raw)
    return raw,{'format':'Permansson.App.LPFarkasReceipt.v1',
        'model_semantic_identity':lp.semantic_id(),'multiplier':['1']}


class LPReificationTests(unittest.TestCase):
    def test_complete_optimal_soundness_candidate(self):
        raw,r=optimal_fixture()
        source,metadata=emit_source(parse_lp(raw),r)
        self.assertIn('theorem real_optimal',source)
        self.assertIn('optimum_over_reals',source)
        self.assertEqual(len(metadata['theorem_names']),4)
        self.assertEqual(metadata['scope'],{'normalized_constraints':1,'variables':2})
        self.assertEqual(metadata['lean_status'],'NOT_EXECUTED')
        self.assertFalse(metadata['compiler_evidence_authenticated'])
        self.assertFalse(metadata['independent_math_certification'])
        self.assertNotIn('native_decide',source)
        self.assertNotIn('sorry',source)
        self.assertNotIn('\naxiom ',source)

    def test_complete_farkas_soundness_candidate(self):
        raw,r=farkas_fixture()
        source,metadata=emit_source(parse_lp(raw),r)
        self.assertIn('theorem real_infeasible',source)
        self.assertIn('infeasible_over_reals',source)
        self.assertEqual(metadata['certificate_family'],'FARKAS_INFEASIBILITY')
        self.assertIn('multiplier_bound_negative',metadata['theorem_names'])
        self.assertFalse(metadata['application_release_authorized'])

    def test_original_lower_bound_shift_preserved(self):
        raw,r=optimal_fixture()
        raw['bounds']['x']['lower']='-2'
        raw['bounds']['y']['lower']='3'
        raw['constraints'][0]['rhs']='5'
        m=parse_lp(raw)
        from permansson_app.receipts.lp import check_lp_certificate
        proposal=propose_lp_optimum(m)
        self.assertEqual(proposal['status'],'CHECKED_OPTIMAL_CANDIDATE')
        source,meta=emit_source(m,proposal['receipt'])
        self.assertEqual(meta['normalization']['lower_bounds'],['-2','3'])
        self.assertIn('Lower-bound shifts',source)

    def test_minimization_sign_is_not_relabelled(self):
        raw,r=optimal_fixture()
        raw['objective']['sense']='minimize'
        m=parse_lp(raw)
        proposal=propose_lp_optimum(m)
        self.assertEqual(proposal['status'],'CHECKED_OPTIMAL_CANDIDATE')
        _,meta=emit_source(m,proposal['receipt'])
        self.assertEqual(meta['normalization']['original_sense'],'minimize')
        self.assertIn(meta['certificate_family'],'PRIMAL_DUAL_OPTIMUM')

    def test_tied_optima_do_not_assume_solver_vector_identity(self):
        raw,r=optimal_fixture()
        alt=deepcopy(r)
        alt['primal']=['1','0']
        a,b=emit_source(parse_lp(raw),r),emit_source(parse_lp(raw),alt)
        self.assertNotEqual(a[0],b[0])
        self.assertNotEqual(a[1]['lean_source_sha256'],b[1]['lean_source_sha256'])

    def test_receipt_modifications_rejected_before_emission(self):
        raw,r=optimal_fixture()
        tests=[('dual',['0']),('primal',['2','0']),('objective_value','2'),
               ('model_semantic_identity',{'profile':'not-an-identity','sha256':'0'*64})]
        for key,value in tests:
            bad=deepcopy(r);bad[key]=value
            with self.subTest(key=key),self.assertRaises(AppError):
                emit_source(parse_lp(raw),bad)

    def test_farkas_sign_and_column_rejected(self):
        raw,r=farkas_fixture()
        for val in ('-1','0'):
            bad=deepcopy(r);bad['multiplier']=[val]
            with self.subTest(val=val),self.assertRaises(AppError):
                emit_source(parse_lp(raw),bad)

    def test_foreign_model_receipt_rejected(self):
        raw,r=optimal_fixture()
        mutated=deepcopy(raw);mutated['constraints'][0]['rhs']='2'
        with self.assertRaises(AppError): emit_source(parse_lp(mutated),r)

    def test_scope_does_not_expand_unbounded_lp(self):
        raw,r=optimal_fixture()
        raw['constraints']=[{'id':'cap'+str(i),'coefficients':{'x':'1','y':'1'},'relation':'<=','rhs':'1'} for i in range(7)]
        lp=parse_lp(raw)
        # A certificate can still be valid while the *reifier* refuses the scope.
        proof={'format':'Permansson.App.LPOptimalReceipt.v1','model_semantic_identity':lp.semantic_id(),
              'primal':['1','0'],'dual':['1','0','0','0','0','0','0'],'objective_value':'1'}
        with self.assertRaisesRegex(AppError,'1..6'): emit_source(lp,proof)

    def test_source_recheck_rejects_lean_byte_tamper(self):
        raw,r=optimal_fixture()
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);model=d/'model.json';receipt=d/'receipt.json'
            model.write_text(json.dumps(raw));receipt.write_text(json.dumps(r))
            emit_files(model,receipt,d/'source')
            code=d/'source/ReifiedLP.lean'
            code.write_bytes(code.read_bytes().replace(b'gap_checked',b'gap_hidden'))
            with self.assertRaises(AppError):check_files(model,receipt,d/'source')

    def test_source_recheck_rejects_metadata_promotion(self):
        raw,r=optimal_fixture()
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);model=d/'model.json';receipt=d/'receipt.json'
            model.write_text(json.dumps(raw));receipt.write_text(json.dumps(r))
            emit_files(model,receipt,d/'source')
            meta=d/'source/source_candidate.json';current=json.loads(meta.read_text())
            current['lean_status']='VERIFIED';meta.write_text(json.dumps(current))
            with self.assertRaises(AppError):check_files(model,receipt,d/'source')

    def test_source_recheck_rejects_extra_payload(self):
        raw,r=optimal_fixture()
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);model=d/'model.json';receipt=d/'receipt.json'
            model.write_text(json.dumps(raw));receipt.write_text(json.dumps(r))
            emit_files(model,receipt,d/'source')
            (d/'source'/'extra.lean').write_text('theorem forged : True := trivial')
            with self.assertRaises(AppError):check_files(model,receipt,d/'source')

    def test_source_recheck_rejects_swapped_original_receipt(self):
        raw,r=optimal_fixture()
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);model=d/'model.json';receipt=d/'receipt.json'
            model.write_text(json.dumps(raw));receipt.write_text(json.dumps(r))
            emit_files(model,receipt,d/'source')
            changed=deepcopy(r);changed['primal']=['1','0']
            receipt.write_text(json.dumps(changed))
            with self.assertRaises(AppError):check_files(model,receipt,d/'source')

    def test_roundtrip_both_witness_types(self):
        for raw,r in (optimal_fixture(),farkas_fixture()):
            with self.subTest(r['format']),tempfile.TemporaryDirectory() as td:
                d=Path(td);model=d/'model.json';receipt=d/'receipt.json'
                model.write_text(json.dumps(raw));receipt.write_text(json.dumps(r))
                status=emit_files(model,receipt,d/'source')
                result=check_files(model,receipt,d/'source')
                self.assertEqual(status['lean_status'],'NOT_EXECUTED')
                self.assertEqual(result['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
                self.assertEqual(result['theorem_names'][ -1 ],'real_optimal' if r['format'].endswith('OptimalReceipt.v1') else 'real_infeasible')
                self.assertFalse(result['independent_math_certification'])

    def test_new_output_directory_must_not_exist(self):
        raw,r=optimal_fixture()
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);model=d/'model.json';receipt=d/'receipt.json'
            model.write_text(json.dumps(raw));receipt.write_text(json.dumps(r))
            (d/'out').mkdir()
            with self.assertRaises(AppError):emit_files(model,receipt,d/'out')


if __name__=='__main__':unittest.main()
