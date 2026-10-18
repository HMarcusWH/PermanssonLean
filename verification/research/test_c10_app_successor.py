"""NEXT-07 C10 supported successor: strict evidence and fail-closed API tests.

These checks are ordinary Python tests, not the real Lean compiler check.
The separate test_c10_app_successor_compiler.py requires actual pinned Lean.
"""
from __future__ import annotations

from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
TARGET = ROOT / 'apps/permansson/closure-successor/cli.py'
SIX = ROOT / 'apps/permansson/closure-successor/examples/frozen_six_state.json'
WRONG = ROOT / 'apps/permansson/closure-successor/examples/unsupported_changed_baseline.json'

spec=spec_from_file_location('permannson_c10_successor',TARGET)
app=module_from_spec(spec)
spec.loader.exec_module(app)


class C10SuccessorContract(unittest.TestCase):
    def setUp(self):
        self.raw = json.loads(SIX.read_text())

    def test_supported_exact_six_state_and_menu(self):
        self.assertEqual(app.supported_input(self.raw), app.check_input(app.six_input()).canonical())
        self.assertEqual(tuple(x['id'] for x in self.raw['menu']), app.SUPPORTED_IDS)
        self.assertEqual(self.raw['comparison'], [1,2])

    def test_original_exact_numeric_optimum_independently_verified(self):
        receipt,lean=app.exact_replay(self.raw)
        self.assertTrue(app.verify_receipt(receipt))
        self.assertEqual(receipt['format'],'Permansson.C10.rational-margin.v2')
        self.assertEqual([x['margin'] for x in receipt['members']], ['1','1/2','1/1000','0','0','0'])
        self.assertEqual(receipt['selected'],'full')
        self.assertEqual(receipt['optimum'],'1')
        self.assertIn('reifiedGolden_original_margins',lean)
        self.assertIn('six_original_baseline_exactGR',lean)

    def test_normalized_but_wrong_stochastic_row_rejected(self):
        for x in [json.loads(WRONG.read_text()), self.raw]:
            x=json.loads(json.dumps(x))
            if x['baseline'] == self.raw['baseline']:
                x['menu'][1]['matrix'][2] = ['0','2/5','0','0','3/5','0']
            with self.assertRaises(app.AppFailure) as ctx:
                app.supported_input(x)
            self.assertEqual(ctx.exception.code,'INPUT_UNSUPPORTED')

    def test_omitted_comparison_start_is_not_an_equal_certificate(self):
        self.raw['comparison']=[2]
        with self.assertRaises(app.AppFailure) as ctx:
            app.supported_input(self.raw)
        self.assertEqual(ctx.exception.code,'INPUT_UNSUPPORTED')

    def test_omitted_menu_or_unsupported_history_objective_rejected(self):
        for change in (lambda x:x['menu'].pop(), lambda x:x.__setitem__('history_policy',True)):
            raw=json.loads(json.dumps(self.raw))
            change(raw)
            with self.assertRaises(app.AppFailure) as ctx:
                app.supported_input(raw)
            self.assertEqual(ctx.exception.code,'INPUT_UNSUPPORTED')

    def test_duplicate_keys_and_floating_point_json_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'bad.json'
            for value in ('{"n":6,"n":6}', '{"n":1.0}', '[true, null, NaN]'):
                p.write_text(value)
                with self.assertRaises(app.AppFailure) as ctx:
                    app.strict_input(p)
                self.assertEqual(ctx.exception.code,'INPUT_NOT_JSON')

    def test_large_json_fails_before_parsing(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'huge.json'
            p.write_bytes(b'0' * (app.MAX_INPUT_BYTES + 1))
            with self.assertRaises(app.AppFailure) as ctx:
                app.strict_input(p)
            self.assertEqual(ctx.exception.code,'INPUT_TOO_LARGE')

    def test_numeric_only_does_not_assert_lean_or_empirical_cert(self):
        with tempfile.TemporaryDirectory() as td:
            result=app.report_for(self.raw,mode='numeric',out_dir=Path(td))
            self.assertEqual(result['numeric_status'],'VERIFIED_EXACT_RATIONAL')
            self.assertEqual(result['lean_status'],'NOT_RUN')
            self.assertIs(result['scientific_claims_verified'],False)
            self.assertEqual(result['empirical_identification'],'NOT_IDENTIFIED')
            self.assertEqual(result['exact_GR_scope'],'CONSTRUCTED_SIX_STATE_WITNESS_ONLY')

    def test_missing_compiler_fails_closed(self):
        def missing(*args, **kwargs):
            raise FileNotFoundError('no Lean')
        with tempfile.TemporaryDirectory() as td:
            source=app.exact_replay(self.raw)[1]
            with self.assertRaises(app.AppFailure) as ctx:
                app.run_compiler(source,out_dir=Path(td),runner=missing)
            self.assertEqual(ctx.exception.code,'LEAN_UNAVAILABLE')

    def test_fake_green_compiler_without_axioms_fails_closed(self):
        def fake(*args,**kwargs):
            return subprocess.CompletedProcess(args,returncode=0,stdout='',stderr='')
        with tempfile.TemporaryDirectory() as td:
            source=app.exact_replay(self.raw)[1]
            with self.assertRaises(app.AppFailure) as ctx:
                app.run_compiler(source,out_dir=Path(td),runner=fake)
            self.assertEqual(ctx.exception.code,'LEAN_AXIOM_REJECTED')

    def test_compiler_error_cannot_be_transformed_into_certification(self):
        def fake(*args,**kwargs):
            return subprocess.CompletedProcess(args,returncode=1,stdout='',stderr='error: theorem false')
        with tempfile.TemporaryDirectory() as td:
            source=app.exact_replay(self.raw)[1]
            with self.assertRaises(app.AppFailure) as ctx:
                app.run_compiler(source,out_dir=Path(td),runner=fake)
            self.assertEqual(ctx.exception.code,'LEAN_COMPILATION_FAILED')

    def test_cli_numeric_write_is_outside_frozen_repo(self):
        with tempfile.TemporaryDirectory() as td:
            import io
            from contextlib import redirect_stdout
            out=Path(td)/'report'
            with redirect_stdout(io.StringIO()) as stdout:
                code=app.run_cli([str(SIX),'--output',str(out),'--mode','numeric'])
            self.assertEqual(code,0,stdout.getvalue())
            r=json.loads((out/'result.json').read_text())
            self.assertFalse(r['scientific_claims_verified'])
            self.assertEqual(r['numeric_selected'],'full')
            self.assertTrue((out/'numeric_receipt.json').is_file())


if __name__=='__main__':
    unittest.main()
