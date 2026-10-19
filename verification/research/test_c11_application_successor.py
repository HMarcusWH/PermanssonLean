"""C11 v0.2 scope, exact arithmetic and explicit negative trust boundaries."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'apps/permansson/closure-successor-c11/cli.py'
EX=APP.parent/'examples'

spec=importlib.util.spec_from_file_location('c11_closure_application_v020', APP)
app=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=app
spec.loader.exec_module(app)


class C11Application(unittest.TestCase):
    def load(self, filename):
        return app.strict_input(EX/filename)

    def test_periodic_exact_and_nonempirical(self):
        report, source=app.compute(self.load('periodic_two_state.json'))
        self.assertEqual([x['states'] for x in report['classes']], [[0,1]])
        self.assertEqual(report['classes'][0]['stationary'], ['1/2','1/2'])
        self.assertEqual(report['classes'][0]['true_share'], '1/2')
        self.assertIn('checkStationaryFamily',source)

    def test_two_bottom_classes_not_mixed_by_producer(self):
        report, _=app.compute(self.load('multiclass_three_state.json'))
        self.assertEqual([x['states'] for x in report['classes']], [[1],[2]])
        self.assertEqual([x['true_share'] for x in report['classes']], ['1','0'])
        from c11_verify_stationary import verify_report
        self.assertTrue(verify_report(report))

    def test_numeric_has_no_lean_claim_or_fake_identification(self):
        with tempfile.TemporaryDirectory() as td:
            out=Path(td)/'numeric'
            with mock.patch.object(app,'replay',side_effect=AssertionError('no Lean on numeric')):
                rc=app.run_cli([str(EX/'periodic_two_state.json'),'--mode','numeric',
                               '--output',str(out)])
            self.assertEqual(rc,0)
            d=json.loads((out/'result.json').read_text())
            self.assertEqual(d['lean_status'],'NOT_EXECUTED')
            self.assertFalse(d['scientific_claims_verified'])
            self.assertEqual(d['empirical_identification'],'NOT_IDENTIFIED')
            self.assertEqual(set(x.name for x in out.iterdir()),{'numeric_receipt.json','result.json'})

    def test_tampered_stationary_mass_rejected(self):
        from c11_verify_stationary import verify_report
        from c11_stationary_execution import StationaryError
        r,_=app.compute(self.load('periodic_two_state.json'))
        r['classes'][0]['stationary'][0]='3/4'
        with self.assertRaises(StationaryError):verify_report(r)

    def test_resource_limit_rejects_valid_stochastic_n7(self):
        with self.assertRaises(app.CertificateError) as caught:
            self.load('unsupported_seven_state.json')
        self.assertEqual(caught.exception.code,'INPUT_SCOPE')

    def test_duplicate_key_and_float_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            path=Path(td)/'bad.json'
            for data in (b'{"n":2,"n":2,"matrix":[],"descriptor":[]}',
                         b'{"n":2,"matrix":[[0.5,0.5],[1,0]],"descriptor":[false,true]}',
                         b'{"n":2,"matrix":[["0","1"],["1","0"]]}'):
                path.write_bytes(data)
                with self.subTest(payload=data), self.assertRaises(app.CertificateError):
                    raw=app.strict_input(path)
                    app.compute(raw)

    def test_missing_compiler_is_not_certification(self):
        with tempfile.TemporaryDirectory() as td:
            with mock.patch.object(app,'source_identity',return_value={'head':'fixture'}),\
                 mock.patch.object(app.subprocess,'run',side_effect=FileNotFoundError('lake')):
                with self.assertRaises(app.CertificateError) as caught:
                    app.replay('import Mathlib\n',1,Path(td))
                self.assertEqual(caught.exception.code,'LEAN_UNAVAILABLE')

    def test_false_green_exit_without_axiom_reports_is_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            with mock.patch.object(app,'source_identity',return_value={'head':'fixture'}),\
                 mock.patch.object(app.subprocess,'run',return_value=subprocess.CompletedProcess([],0,'','')):
                with self.assertRaises(app.CertificateError) as caught:
                    app.replay('import Mathlib\n',1,Path(td))
                self.assertEqual(caught.exception.code,'LEAN_AXIOM')

    def test_rejects_unauthorized_transitive_axiom(self):
        s="'C11ReifiedFixture.member0_accepted' depends on axioms: [unsafeOath]"
        with self.assertRaises(app.CertificateError):app.audit_axioms(s,1)

    def test_output_must_be_empty_and_outside_source(self):
        with self.assertRaises(app.CertificateError):app.prepare_output(ROOT/'inside-repo')
        with tempfile.TemporaryDirectory() as td:
            p=Path(td);(p/'occupied').write_text('x')
            with self.assertRaises(app.CertificateError):app.prepare_output(p)

    def test_exact_provider_pin_is_not_relabelled(self):
        with mock.patch.object(app,'_git',side_effect=lambda *args: (
            str(ROOT).encode() if args==('rev-parse','--show-toplevel') else
            b'0'*40 if args==('rev-parse','HEAD') or args==('rev-parse','HEAD^{tree}') else
            b'1'*40)):
            with self.assertRaises(app.CertificateError):app.source_identity()


if __name__=='__main__':unittest.main()
