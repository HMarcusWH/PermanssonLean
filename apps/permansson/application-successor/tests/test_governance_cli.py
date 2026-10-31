"""Isolated installed-entrypoint-compatible governance CLI tests."""
from __future__ import annotations
import json,os,sys,subprocess,tempfile,unittest,zipfile
from pathlib import Path
APP=Path(__file__).resolve().parents[1]
SRC=str(APP/'src')

def invoke(*argv):
    env=os.environ.copy();env['PYTHONPATH']=SRC;env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run([sys.executable,'-B','-m','permansson_app.governance_cli',*map(str,argv)],
                          env=env,text=True,capture_output=True,timeout=30)

class CliTests(unittest.TestCase):
    def test_claim_registry_no_promotion(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td)/'out';r=invoke('claims-list','--output',d)
            self.assertEqual(r.returncode,0,r.stderr)
            v=json.loads((d/'claim_snapshot.json').read_text());self.assertEqual((v['original_cases'],v['later_claims']),(45,11))
            self.assertFalse(v['mathematical_certification'])
    def test_preexisting_directory_not_overwritten(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td)/'out';d.mkdir()
            r=invoke('claims-list','--output',d)
            self.assertEqual(r.returncode,2);self.assertIn('OUTPUT_SCOPE',r.stderr)
    def test_domain_case_success_but_not_identified(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);zipfile_name=root/'case.zip'
            with zipfile.ZipFile(zipfile_name,'w') as z:
                z.writestr('source/data.csv','known_at,measurement\n2026-10-02T00:00:00Z,1\n')
            d=root/'out';r=invoke('domain-import',zipfile_name,'--case','midr','--output',d)
            self.assertEqual(r.returncode,0,r.stderr)
            v=json.loads((d/'domain_import.json').read_text())
            self.assertFalse(v['causal_alpha_P_U_identified'])
            self.assertEqual(v['status'],'INCOMPLETE_EVIDENCE_BUNDLE')
    def test_provenance_missing_stays_unknown(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            x={'format':'Permansson.App.ProvenanceGraph.v1','nodes':[],'cutoff':None,'evaluation_start':None}
            (root/'graph.json').write_text(json.dumps(x))
            r=invoke('provenance-check',root/'graph.json','--output',root/'result')
            self.assertEqual(r.returncode,0,r.stderr)
            v=json.loads((root/'result/provenance_check.json').read_text())
            self.assertFalse(v['origin_authenticated'])
    def test_wrong_schema_rejected_before_output(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);(root/'graph.json').write_text(json.dumps({'format':'made-up','nodes':[]}))
            r=invoke('provenance-check',root/'graph.json','--output',root/'out')
            self.assertEqual(r.returncode,2);self.assertFalse((root/'out').exists())
    def test_self_claimed_release_evidence_never_authorizes(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);SOURCE={'repository':'HMarcusWH/PermanssonLean','commit':'a'*40,'tree':'b'*40,
                     'paper':'0.1.8','application':'successor.0.2','research':'research.0.2'}
            target={'source':SOURCE,'subject_sha256':'c'*64,'wheel_sha256':'d'*64,
                     'sdist_sha256':'e'*64,'capabilities':['c10.fixed_six_state.numeric.v1'],
                     'platforms':['linux'],'execution_profile':'numeric'}
            policy={'format':'Permansson.App.AcceptancePolicy.v1','required':{'c10.fixed_six_state.numeric.v1':{'numeric_test':['t1']}},
                    'security_review_required':True,'owner_activation_required':True}
            for name,value in [('target',target),('policy',policy),('evidence',[]),('pins',{})]:
                (root/(name+'.json')).write_text(json.dumps(value))
            args=['release-assess',root/'target.json',root/'evidence.json',root/'pins.json',root/'policy.json','--output',root/'out']
            r=invoke(*args)
            self.assertEqual(r.returncode,0,r.stderr)
            x=json.loads((root/'out/acceptance_assessment.json').read_text())
            self.assertFalse(x['authorized_release']);self.assertTrue(x['missing'])
    def test_truncated_zip_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);(root/'bad.zip').write_bytes(b'not zip')
            r=invoke('domain-import',root/'bad.zip','--case','midr','--output',root/'out')
            self.assertNotEqual(r.returncode,0);self.assertFalse((root/'out').exists())

if __name__=='__main__':unittest.main()
