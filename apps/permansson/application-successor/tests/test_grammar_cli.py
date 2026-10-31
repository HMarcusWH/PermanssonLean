"""Installed-style finite admissible grammar CLI and wire-contract regressions."""
from __future__ import annotations
import copy,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.package_data import resource_bytes,export_extended_resources
from permansson_app.schema_validate import validate_packaged_schema
from permansson_app.strict_json import strict_loads
from permansson_app.errors import AppError


def cli(*args):
    env=dict(os.environ,PYTHONPATH=str(APP/'src'),PYTHONDONTWRITEBYTECODE='1')
    return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
                          cwd=APP,env=env,text=True,capture_output=True,timeout=40)


class GrammarCLI(unittest.TestCase):
    def test_full_offline_schema_resource_and_export(self):
        raw=strict_loads(resource_bytes('examples/grammar.v1.json'))
        self.assertEqual(validate_packaged_schema('schemas/grammar.v1.schema.json',raw)['status'],'PASS')
        with tempfile.TemporaryDirectory() as temp:
            hashes=export_extended_resources(Path(temp)/'export')
            self.assertTrue({'schemas/grammar.v1.schema.json','examples/grammar.v1.json'} <= set(hashes))
    def test_cli_reports_independent_check_with_no_scientific_promotion(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            r=cli('finite-grammar',APP/'src/permansson_app/data/examples/grammar.v1.json','--output',root/'out')
            self.assertEqual(r.returncode,0,r.stdout+r.stderr)
            receipt=json.loads((root/'out/grammar_receipt.json').read_text())
            check=json.loads((root/'out/independent_check.json').read_text())
            report=json.loads((root/'out/scientific_report.json').read_text())
            self.assertEqual(receipt['minimal_positive_blocks'],[['a'],['u']])
            self.assertEqual(receipt['four_corners'][0]['interactions_by_comparison_state'],['-1'])
            self.assertEqual(check['status'],'PASS')
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
            self.assertEqual(len(report['scientific_certificate_dimensions']),9)
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(json.loads(r.stdout)['numeric_status'],'PASS')
    def test_untrusted_extra_input_fails_before_output_creation(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            raw=strict_loads(resource_bytes('examples/grammar.v1.json'))
            raw['claim_certified']=True
            (root/'bad.json').write_text(json.dumps(raw))
            r=cli('finite-grammar',root/'bad.json','--output',root/'out')
            self.assertEqual(r.returncode,2)
            self.assertIn('SCHEMA_INVALID',r.stderr)
            self.assertFalse((root/'out').exists())
    def test_wrong_patch_type_and_admitted_family_fail_closed(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            raw=strict_loads(resource_bytes('examples/grammar.v1.json'))
            raw['patches'][0]['target']='P'
            (root/'bad.json').write_text(json.dumps(raw))
            r=cli('finite-grammar',root/'bad.json','--output',root/'out')
            self.assertEqual(r.returncode,2)
            self.assertFalse((root/'out').exists())
            self.assertIn('SCHEMA_INVALID',r.stderr)
            raw=strict_loads(resource_bytes('examples/grammar.v1.json'))
            raw['admitted_blocks']=[[],['a','u']]
            (root/'bad2.json').write_text(json.dumps(raw))
            r=cli('finite-grammar',root/'bad2.json','--output',root/'out')
            self.assertEqual(r.returncode,2)
            self.assertIn('GRAMMAR_FOUR_CORNERS',r.stderr)
    def test_existing_output_not_overwritten(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'out').mkdir()
            r=cli('finite-grammar',APP/'src/permansson_app/data/examples/grammar.v1.json','--output',root/'out')
            self.assertEqual(r.returncode,2)
            self.assertIn('OUTPUT_SCOPE',r.stderr)

if __name__=='__main__':unittest.main()
