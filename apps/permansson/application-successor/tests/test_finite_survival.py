"""Genuine finite killed-kernel vs independent recurrence; mutated receipt adversaries."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction
import json,sys,unittest
from pathlib import Path
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.finite_survival import propose_finite_survival
from permansson_app.receipts.finite_survival import check_survival_receipt
from permansson_app.schema_validate import validate_packaged_schema

EXAMPLE=APP/'src/permansson_app/data/examples/finite_survival.v1.json'

class SurvivalTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.raw=json.loads(EXAMPLE.read_text())
 def test_exact_positive_margin(self):
  r=propose_finite_survival(self.raw)
  self.assertEqual(r['minimum_abs_effect'],'3/4')
  self.assertEqual(r['finite_scope_status'],'ALL_DECLARED_STARTS_SEPARATED')
  self.assertFalse(r['exact_GR_or_PR_certified'])
  self.assertEqual(check_survival_receipt(self.raw,r)['status'],'FINITE_SURVIVAL_TABLE_VERIFIED')
 def test_full_schema(self):
  self.assertEqual(validate_packaged_schema('schemas/finite_survival.v1.schema.json',self.raw)['status'],'PASS')
 def test_horizon_zero_no_effect(self):
  raw=deepcopy(self.raw);raw['horizon']=0
  r=propose_finite_survival(raw)
  self.assertEqual(r['minimum_abs_effect'],'0')
  self.assertEqual(r['finite_scope_status'],'NO_UNIFORM_FINITE_SEPARATION')
  check_survival_receipt(raw,r)
 def test_one_step_margin(self):
  raw=deepcopy(self.raw);raw['horizon']=1
  r=propose_finite_survival(raw)
  self.assertEqual(r['minimum_abs_effect'],'1/2')
  check_survival_receipt(raw,r)
 def test_nonzero_effect_different_initials(self):
  raw=deepcopy(self.raw)
  raw['region']=[['s0','x0'],['s1','x0'],['s0','x1']]
  raw['comparison_states']=[['s0','x0'],['s0','x1']]
  r=propose_finite_survival(raw)
  self.assertEqual(check_survival_receipt(raw,r)['status'],'FINITE_SURVIVAL_TABLE_VERIFIED')
 def test_tamper_entry_fails(self):
  r=propose_finite_survival(self.raw);r['baseline_survival'][2][0]='1'
  with self.assertRaises(AppError):check_survival_receipt(self.raw,r)
 def test_tamper_margin_fails(self):
  r=propose_finite_survival(self.raw);r['minimum_abs_effect']='1/2'
  with self.assertRaises(AppError):check_survival_receipt(self.raw,r)
 def test_wrong_sign_fails(self):
  r=propose_finite_survival(self.raw);r['finite_effect_signs']=['positive']*2
  with self.assertRaises(AppError):check_survival_receipt(self.raw,r)
 def test_false_gr_promotion_fails(self):
  r=propose_finite_survival(self.raw);r['exact_GR_or_PR_certified']=True
  with self.assertRaises(AppError):check_survival_receipt(self.raw,r)
 def test_wrong_model_binding_fails(self):
  r=propose_finite_survival(self.raw);r['baseline_id']['sha256']='a'*64
  with self.assertRaises(AppError):check_survival_receipt(self.raw,r)
 def test_physical_P_mutation_fails(self):
  raw=deepcopy(self.raw);raw['treated']['P'][0]['weights']['x0']='0'
  raw['treated']['P'][0]['weights']['x1']='1'
  with self.assertRaises(AppError):propose_finite_survival(raw)
 def test_treated_feasibility_change_fails(self):
  raw=deepcopy(self.raw);raw['treated']['feasible'][0]['actions']=['stay']
  with self.assertRaises(AppError):propose_finite_survival(raw)
 def test_invalid_region_fails(self):
  raw=deepcopy(self.raw);raw['region']=[['unknown','x0']]
  with self.assertRaises(AppError):propose_finite_survival(raw)
 def test_duplicate_comparison_fails(self):
  raw=deepcopy(self.raw);raw['comparison_states'].append(['s0','x0'])
  with self.assertRaises(AppError):propose_finite_survival(raw)
 def test_comparison_must_be_in_region(self):
  raw=deepcopy(self.raw);raw['comparison_states']=[['s0','x1']]
  with self.assertRaises(AppError):propose_finite_survival(raw)
 def test_float_horizon_fails(self):
  raw=deepcopy(self.raw);raw['horizon']=3.0
  with self.assertRaises(AppError):propose_finite_survival(raw)
 def test_oversized_horizon_fails(self):
  raw=deepcopy(self.raw);raw['horizon']=100
  with self.assertRaises(AppError):propose_finite_survival(raw)
 def test_changed_U_not_declared_fails(self):
  raw=deepcopy(self.raw);raw['treated']['U'][0]['weights']={'s0':'0','s1':'1'}
  with self.assertRaises(AppError):propose_finite_survival(raw)

class SurvivalCLITests(unittest.TestCase):
 def test_installed_style_cli_roundtrip(self):
  import tempfile,subprocess,os
  with tempfile.TemporaryDirectory() as td:
   root=Path(td)
   env=os.environ.copy();env['PYTHONPATH']=str(APP/'src');env['PYTHONDONTWRITEBYTECODE']='1'
   p=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-survival',str(EXAMPLE),
      '--output',str(root/'result')],cwd=APP,env=env,capture_output=True,text=True,timeout=15)
   self.assertEqual(p.returncode,0,p.stderr)
   report=json.loads((root/'result/scientific_report.json').read_text())
   receipt=json.loads((root/'result/finite_survival_receipt.json').read_text())
   self.assertFalse(report['scientific_claims_verified'])
   self.assertEqual(receipt['minimum_abs_effect'],'3/4')

if __name__=='__main__':unittest.main()

class AdvertisedScopeTests(unittest.TestCase):
 def test_numeric_registry_profiles_are_explicitly_uncertified(self):
  from permansson_app.capabilities import registry
  r=registry()
  self.assertEqual(len(r['capabilities']),2)
  self.assertEqual(len(r['exact_profiles']),16)
  self.assertTrue(all(v['lean_status']=='NOT_EXECUTED' and v['scientific_claims_verified'] is False
                      for v in r['exact_profiles'].values()))
