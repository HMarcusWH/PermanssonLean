"""Installed-style end-to-end tests for strict grammar/quotient CLI endpoints."""
import json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.package_data import resource_bytes,export_extended_resources
from permansson_app.schema_validate import validate_packaged_schema
from permansson_app.strict_json import strict_loads


def call(*args):
    env=dict(os.environ);env['PYTHONPATH']=str(APP/'src');env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
        cwd=APP,capture_output=True,text=True,timeout=20,env=env)


class GrammarQuotientCLI(unittest.TestCase):
 def test_installed_resourced_schemas_and_exact_export(self):
    for profile in ('grammar','quotient'):
        with self.subTest(profile=profile):
            raw=strict_loads(resource_bytes(f'examples/{profile}.v1.json'))
            self.assertEqual(validate_packaged_schema(f'schemas/{profile}.v1.schema.json',raw)['status'],'PASS')
    with tempfile.TemporaryDirectory() as td:
        exported=export_extended_resources(Path(td)/'export')
        self.assertEqual(len(exported),46)
        for profile in ('grammar','quotient'):
            self.assertIn(f'examples/{profile}.v1.json',exported)
            self.assertIn(f'schemas/{profile}.v1.schema.json',exported)
 def test_both_engines_execute_and_keep_nine_dimensions_unverified(self):
    for profile,command in (('grammar','finite-grammar'),('quotient','finite-quotient')):
        with self.subTest(profile=profile),tempfile.TemporaryDirectory() as td:
            out=Path(td)/'result'
            r=call(command,APP/f'src/permansson_app/data/examples/{profile}.v1.json','--output',out)
            self.assertEqual(r.returncode,0,r.stderr)
            check=json.loads((out/'independent_check.json').read_text())
            self.assertEqual(check['status'],'PASS')
            result=json.loads((out/f'{profile}_receipt.json').read_text())
            self.assertEqual(result['lean_status'],'NOT_EXECUTED')
            self.assertFalse(result['scientific_claims_verified'])
            report=json.loads((out/'scientific_report.json').read_text())
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(len(report['scientific_certificate_dimensions']),9)
 def test_mutation_rejected_before_output(self):
    for profile,cmd in (('grammar','finite-grammar'),('quotient','finite-quotient')):
        with self.subTest(profile=profile),tempfile.TemporaryDirectory() as td:
            original=json.loads(resource_bytes(f'examples/{profile}.v1.json'))
            original['spoofed_release_approval']=True
            bad=Path(td)/'tampered.json';bad.write_text(json.dumps(original))
            out=Path(td)/'out'
            r=call(cmd,bad,'--output',out)
            self.assertEqual(r.returncode,2,r.stderr)
            self.assertIn('SCHEMA_INVALID',r.stderr)
            self.assertFalse(out.exists())
 def test_output_path_not_overwritten(self):
    with tempfile.TemporaryDirectory() as td:
        out=Path(td)/'already_exists';out.mkdir()
        r=call('finite-quotient',APP/'src/permansson_app/data/examples/quotient.v1.json','--output',out)
        self.assertEqual(r.returncode,2,r.stderr)
        self.assertIn('OUTPUT_SCOPE',r.stderr)

if __name__=='__main__': unittest.main()
