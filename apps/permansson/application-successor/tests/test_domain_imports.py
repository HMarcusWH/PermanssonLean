"""ZIP adversaries, chronology and six real companion profile boundaries."""
from __future__ import annotations
import hashlib,io,json,os,stat,tempfile,unittest,zipfile
from datetime import datetime,timezone
from pathlib import Path
from permansson_app.errors import AppError
from permansson_app.domain.bundle import BundleLimits,open_bundle,read_member
from permansson_app.domain.registry import PROFILES,resolve_profile
from permansson_app.domain.importer import import_domain,inspect_artifact
from permansson_app.domain.clock import validate_clocks,available_at
from permansson_app.domain.types import ObservationRecord

class ArchiveTests(unittest.TestCase):
 def zipped(self,dir,files):
  p=Path(dir)/'evidence.zip'
  with zipfile.ZipFile(p,'w') as z:
   for name,value in files:
    z.writestr(name,value)
  return p
 def test_zip_hash_recheck(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=self.zipped(tmp,[('case/a.csv','known_at,result\n2026-10-01T00:00:00Z,yes\n')])
   x=open_bundle(f)
   self.assertEqual(read_member(x,'case/a.csv'),b'known_at,result\n2026-10-01T00:00:00Z,yes\n')
 def test_path_traversal(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=self.zipped(tmp,[('../secret.txt','bad')])
   with self.assertRaises(AppError):open_bundle(f)
 def test_absolute_path(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=self.zipped(tmp,[('/tmp/secret.txt','bad')])
   with self.assertRaises(AppError):open_bundle(f)
 def test_nested_backslash(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=self.zipped(tmp,[('bad\\windows.txt','bad')])
   with self.assertRaises(AppError):open_bundle(f)
 def test_case_collision(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=self.zipped(tmp,[('X.csv','a'),('x.csv','b')])
   with self.assertRaises(AppError):open_bundle(f)
 def test_symlink_in_zip(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=Path(tmp)/'x.zip'
   link=zipfile.ZipInfo('here');link.create_system=3;link.external_attr=(stat.S_IFLNK|0o777)<<16
   with zipfile.ZipFile(f,'w') as z:z.writestr(link,'../etc/passwd')
   with self.assertRaises(AppError):open_bundle(f)
 def test_zip_expanded_limit(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=self.zipped(tmp,[('big.txt','x'*100)])
   with self.assertRaises(AppError):open_bundle(f,BundleLimits(max_member_bytes=50))
 def test_decompression_ratio(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=Path(tmp)/'bomb.zip'
   with zipfile.ZipFile(f,'w',compression=zipfile.ZIP_DEFLATED) as z:z.writestr('bomb.txt','Z'*100000)
   with self.assertRaises(AppError):open_bundle(f,BundleLimits(max_compression_ratio=10))
 def test_zip_mutated_after_indexing(self):
  with tempfile.TemporaryDirectory() as tmp:
   f=self.zipped(tmp,[('x.csv','hello')]);idx=open_bundle(f)
   with zipfile.ZipFile(f,'a') as z:z.writestr('y.txt','bad')
   with self.assertRaises(AppError):read_member(idx,'x.csv')
 def test_directory_symlink(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp)/'root';root.mkdir();(root/'target.txt').write_text('hello')
   (root/'link.txt').symlink_to(root/'target.txt')
   with self.assertRaises(AppError):open_bundle(root)
 def test_directory_changed_after_indexing(self):
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp)/'root';root.mkdir();(root/'data.csv').write_text('a')
   idx=open_bundle(root);(root/'data.csv').write_text('b')
   with self.assertRaises(AppError):read_member(idx,'data.csv')

class ProfileTests(unittest.TestCase):
 def test_all_six_profiles(self):
  self.assertEqual(set(PROFILES),{'hormuz','iran','midr','russia_ukraine','brown_mackay','cross_conflict'})
 def test_unknown_case(self):
  with self.assertRaises(AppError):resolve_profile('made_up_case')
 def test_missing_evidence_not_accepted(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp)/'empty';p.mkdir()
   r=import_domain(open_bundle(p),'midr')
   self.assertEqual(r.status,'INCOMPLETE_EVIDENCE_BUNDLE')
   self.assertFalse(r.to_dict()['causal_alpha_P_U_identified'])
 def test_complete_required_fixture_metadata_only(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp)/'root';p.mkdir();profile=resolve_profile('russia_ukraine')
   for name in profile.required_suffixes:
    dest=p/name;dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text('{}' if name.endswith('.json') else 'known_at,event\n2026-10-01T00:00:00Z,ab\n')
   result=import_domain(open_bundle(p),profile,cutoff=datetime(2026,10,1,tzinfo=timezone.utc))
   self.assertEqual(result.status,'EVIDENCE_ONLY_NOT_CAUSALLY_IDENTIFIED')
   self.assertTrue(result.selected_artifacts)
   self.assertFalse(result.to_dict()['empirical_exact_GR_PR_certified'])
 def test_future_availability_is_not_retroactive(self):
  obj=inspect_artifact(b'known_at,x\n2026-10-02T00:00:00Z,1\n2026-10-01T00:00:00Z,2\n',
                       'observation.csv',cutoff=datetime(2026,10,1,tzinfo=timezone.utc))
  self.assertEqual((obj['known_at_available'],obj['known_at_future']),(1,1))
 def test_missing_known_at_unresolved(self):
  obj=inspect_artifact(b'event_date,x\n2026-10-01,1\n','observation.csv',
                       cutoff=datetime(2026,10,1,tzinfo=timezone.utc))
  self.assertEqual(obj['known_at_unresolved'],1)
 def test_empirical_decimal_not_caused_by_json(self):
  obj=inspect_artifact(b'{"effect":0.125,"supported":false}', 'data.json')
  self.assertEqual(obj['top_level_keys'],['effect','supported'])
 def test_malicious_nonfinite_rejected(self):
  with self.assertRaises(AppError):inspect_artifact(b'{"effect":NaN}', 'data.json')
 def test_malformed_csv_rejected(self):
  with self.assertRaises(AppError):inspect_artifact(b'a,b\n1\n','a.csv')
 def test_circular_json_key_rejected(self):
  with self.assertRaises(AppError):inspect_artifact(b'{"x":1,"x":2}', 'a.json')

class ClockTests(unittest.TestCase):
 def test_cutoff_uses_known_at(self):
  r=ObservationRecord('one','2026-09-01T00:00:00Z','2026-10-02T00:00:00Z')
  t=datetime(2026,10,1,tzinfo=timezone.utc)
  self.assertFalse(available_at(r,t));self.assertEqual(validate_clocks([r],t).excluded_records,('one',))
 def test_event_future_known_now_not_inferred(self):
  r=ObservationRecord('one','2026-11-01T00:00:00Z','2026-10-01T00:00:00Z')
  self.assertTrue(available_at(r,datetime(2026,10,1,tzinfo=timezone.utc)))
 def test_prospective_late_freeze(self):
  r=ObservationRecord('one','2026-10-02T00:00:00Z','2026-10-02T00:00:00Z',
                      '2026-10-03T00:00:00Z','2026-10-02T00:00:00Z','prospective')
  self.assertEqual(validate_clocks([r],None).chronology_errors,('one',))
 def test_prospective_equal_freeze(self):
  r=ObservationRecord('one',None,'2026-10-02T00:00:00Z',
                      '2026-10-02T00:00:00Z','2026-10-02T00:00:00Z','prospective')
  self.assertEqual(validate_clocks([r],None).available_records,('one',))
 def test_unknown_time(self):
  r=ObservationRecord('one',None,None)
  self.assertEqual(validate_clocks([r],None).unresolved_times,('one',))

if __name__=='__main__':unittest.main()
