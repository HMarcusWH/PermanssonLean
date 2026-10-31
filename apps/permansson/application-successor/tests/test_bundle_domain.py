"""Detached trust boundaries, chronology, scientific non-promotion."""
from __future__ import annotations
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
import json,os,sys,tempfile,unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.identity import canonical_bytes
from permansson_app.bundle import create_detached_manifest,verify_detached_bundle
from permansson_app.domain_evidence import validate_domain_evidence

BASE='3492b26707788293ca88c66637b6ba021c7e478d'
TREE='9ef00ac4b2d4f928aa6551ef3f0dfeb2d4434452'


def record():
  payload=b'bounded example'
  return {'record_id':'RU-001','data_role':'observed_event','event_at':'2022-02-24T08:00:00Z',
          'known_at':'2022-02-24T10:00:00Z','source':{'source_id':'s1',
          'sha256':sha256(payload).hexdigest(),'published_at':'2022-02-24T09:30:00Z','source_role':'primary'},
          'measurement_status':'UNEVALUABLE',
          'uncertainty':{'status':'partial','notes':'No structural transition law has been identified'},
          'payload_sha256':sha256(payload).hexdigest()}


def doc():
 return {'format':'Permansson.App.DomainEvidenceImport.v1','case_id':'russia-ukraine',
         'lane':'retrospective','freeze_at':'2026-08-12T12:00:00Z','evidence':[record()]}

class BundleTests(unittest.TestCase):
 def test_hashes_valid(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td)/'root';(root/'nested').mkdir(parents=True)
   (root/'a').write_bytes(b'hello');(root/'nested/2.txt').write_bytes(b'\x00\xff')
   m=create_detached_manifest(root,scope='numeric-only',source_commit=BASE,source_tree=TREE)
   digest=sha256(canonical_bytes(m)).hexdigest()
   r=verify_detached_bundle(root,m,expected_manifest_sha256=digest)
   self.assertEqual(r['files_checked'],2)
   self.assertTrue(r['trusted_manifest_hash_supplied'])
   self.assertFalse(r['mathematical_claims_verified'])
   self.assertFalse(r['origin_authenticated'])
 def test_mutated_file_refused(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'a').write_bytes(b'1')
   m=create_detached_manifest(root,scope='test',source_commit=BASE,source_tree=TREE)
   (root/'a').write_bytes(b'2')
   with self.assertRaises(AppError) as ctx:verify_detached_bundle(root,m)
   self.assertEqual(ctx.exception.code,'BUNDLE_INTEGRITY')
 def test_unlisted_file_refused(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'a').write_bytes(b'1')
   m=create_detached_manifest(root,scope='test',source_commit=BASE,source_tree=TREE)
   (root/'b').write_bytes(b'extra')
   with self.assertRaises(AppError) as ctx:verify_detached_bundle(root,m)
   self.assertEqual(ctx.exception.code,'BUNDLE_INVENTORY')
 def test_forged_manifest_hash_refused(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'a').write_bytes(b'1')
   m=create_detached_manifest(root,scope='test',source_commit=BASE,source_tree=TREE)
   with self.assertRaises(AppError) as ctx:verify_detached_bundle(root,m,expected_manifest_sha256='0'*64)
   self.assertEqual(ctx.exception.code,'BUNDLE_TRUST')
 def test_path_traversal_refused(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'a').write_bytes(b'1')
   m=create_detached_manifest(root,scope='test',source_commit=BASE,source_tree=TREE)
   m['files'][0]['path']='../a'
   with self.assertRaises(AppError):verify_detached_bundle(root,m)
 def test_symlink_refused(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'a').write_bytes(b'1')
   try:(root/'link').symlink_to(root/'a')
   except OSError:self.skipTest('symlinks unavailable')
   with self.assertRaises(AppError):create_detached_manifest(root,scope='test',source_commit=BASE,source_tree=TREE)
 def test_duplicate_reordered_or_extra_entry(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'a').write_bytes(b'1')
   m=create_detached_manifest(root,scope='test',source_commit=BASE,source_tree=TREE)
   m['files'].append(m['files'][0])
   with self.assertRaises(AppError):verify_detached_bundle(root,m)
 def test_size_bool_refused(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'a').write_bytes(b'1')
   m=create_detached_manifest(root,scope='test',source_commit=BASE,source_tree=TREE)
   m['files'][0]['size_bytes']=True
   with self.assertRaises(AppError):verify_detached_bundle(root,m)
 def test_directory_parent_symlink_refused(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);inner=root/'real';inner.mkdir();(inner/'a').write_bytes(b'1')
   try:(root/'link').symlink_to(inner,target_is_directory=True)
   except OSError:self.skipTest('symlinks unavailable')
   with self.assertRaises(AppError):create_detached_manifest(root/'link',scope='test',source_commit=BASE,source_tree=TREE)

class DomainTests(unittest.TestCase):
 def test_preserves_missing_not_normal(self):
  r=validate_domain_evidence(doc())
  self.assertEqual(r['records_checked'],1)
  self.assertEqual(r['retained_data_roles'],['observed_event'])
  self.assertFalse(r['estimated_transition_kernel'])
  self.assertFalse(r['exact_regime_established'])
  self.assertFalse(r['scientific_claims_verified'])
 def test_known_at_not_event_date(self):
  d=doc();d['evidence'][0]['known_at']='2022-02-23T15:00:00Z'
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_source_publication_cannot_backdate(self):
  d=doc();d['evidence'][0]['known_at']='2022-02-24T09:00:00Z'
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_prospective_late_is_ineligible(self):
  d=doc();d['lane']='prospective';d['freeze_at']='2022-02-24T09:30:00Z'
  r=validate_domain_evidence(d)
  self.assertEqual(r['records_after_freeze'],1)
  self.assertFalse(r['prospective_evidence_eligible_at_freeze'])
 def test_prospective_as_of_eligible(self):
  d=doc();d['lane']='prospective';d['freeze_at']='2022-02-25T00:00:00Z'
  r=validate_domain_evidence(d)
  self.assertTrue(r['prospective_evidence_eligible_at_freeze'])
 def test_prospective_simulation_refused(self):
  d=doc();d['lane']='prospective';d['evidence'][0]['data_role']='counterfactual_simulation'
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_support_matrix_stays_data_role(self):
  d=doc();d['case_id']='midr';d['evidence'][0]['data_role']='support_matrix'
  r=validate_domain_evidence(d)
  self.assertEqual(r['retained_data_roles'],['support_matrix'])
  self.assertFalse(r['estimated_transition_kernel'])
 def test_null_unknown_event_rejected(self):
  d=doc();d['evidence'][0]['measurement_status']=None
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_duplicate_id_rejected(self):
  d=doc();d['evidence'].append(deepcopy(d['evidence'][0]))
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_unknown_case_rejected(self):
  d=doc();d['case_id']='fantasy'
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_arbitrary_source_sha_rejected(self):
  d=doc();d['evidence'][0]['source']['sha256']='bad'
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_bad_lane_rejected(self):
  d=doc();d['lane']='omniscient'
  with self.assertRaises(AppError):validate_domain_evidence(d)
 def test_unpaired_unicode_identity_rejected(self):
  d=doc();d['evidence'][0]['record_id']='\ud800'
  with self.assertRaises(AppError):validate_domain_evidence(d)

if __name__=='__main__':unittest.main()

class BundleDomainCLITests(unittest.TestCase):
 def run_cli(self,*args):
  import subprocess,os
  env=os.environ.copy();env['PYTHONPATH']=str(APP/'src');env['PYTHONDONTWRITEBYTECODE']='1'
  return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],env=env,
                        cwd=APP,capture_output=True,text=True,timeout=15)
 def test_manifest_export_and_read_back(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);bundle=root/'raw';bundle.mkdir();(bundle/'a.json').write_text('{"a":1}')
   p=self.run_cli('bundle-inventory',bundle,'--scope','numeric','--source-commit',BASE,
                 '--source-tree',TREE,'--output',root/'manifest')
   self.assertEqual(p.returncode,0,p.stderr)
   m=root/'manifest/detached_manifest.json'
   q=self.run_cli('bundle-verify',bundle,m,'--output',root/'check')
   self.assertEqual(q.returncode,0,q.stderr)
   self.assertFalse(json.loads((root/'check/bundle_check.json').read_text())['origin_authenticated'])
 def test_bundle_mutation_cli_fails_closed(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);bundle=root/'raw';bundle.mkdir();(bundle/'a').write_text('a')
   m=create_detached_manifest(bundle,scope='numeric',source_commit=BASE,source_tree=TREE)
   (root/'m.json').write_text(json.dumps(m));(bundle/'a').write_text('b')
   q=self.run_cli('bundle-verify',bundle,root/'m.json','--output',root/'check')
   self.assertEqual(q.returncode,2,q.stdout)
   self.assertFalse((root/'check').exists())
 def test_domain_cli_unknown_certification(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);(root/'doc.json').write_text(json.dumps(doc()))
   q=self.run_cli('domain-validate',root/'doc.json','--output',root/'out')
   self.assertEqual(q.returncode,0,q.stderr)
   self.assertFalse(json.loads((root/'out/domain_evidence_check.json').read_text())['scientific_claims_verified'])
 def test_domain_cli_rejects_bad_chronology(self):
  with tempfile.TemporaryDirectory() as td:
   root=Path(td);d=doc();d['evidence'][0]['known_at']='2021-01-01T00:00:00Z'
   (root/'doc.json').write_text(json.dumps(d))
   q=self.run_cli('domain-validate',root/'doc.json','--output',root/'out')
   self.assertEqual(q.returncode,2,q.stdout)
