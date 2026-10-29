"""Exact finite frozen-menu semantics, including all tied optima, and mutation adversaries."""
from copy import deepcopy
import json,sys,unittest,tempfile,subprocess,os
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.menu import propose_menu
from permansson_app.receipts.menu import check_menu
from permansson_app.schema_validate import validate_packaged_schema

EXAMPLE=ROOT/'src/permansson_app/data/examples/finite_menu.v1.json'

class FrozenMenuTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.raw=json.loads(EXAMPLE.read_text())
 def test_exact_optimum_and_independent_check(self):
  r=propose_menu(self.raw)
  self.assertEqual((r['optimum_value'],r['attaining_ids']),('1/4',['untreated']))
  self.assertEqual(check_menu(self.raw,r)['status'],'FROZEN_MENU_OPTIMUM_VERIFIED')
  self.assertEqual(validate_packaged_schema('schemas/finite_menu.v1.schema.json',self.raw)['status'],'PASS')
 def test_swapped_max(self):
  inp=deepcopy(self.raw);inp['direction']='max'
  r=propose_menu(inp)
  self.assertEqual((r['optimum_value'],r['attaining_ids']),('1',['treated']))
  check_menu(inp,r)
 def test_exit_complement(self):
  inp=deepcopy(self.raw);inp['value_type']='exit_by_horizon';inp['direction']='max'
  r=propose_menu(inp)
  self.assertEqual((r['optimum_value'],r['attaining_ids']),('3/4',['untreated']))
  check_menu(inp,r)
 def test_ties_return_all_and_deterministic_representative(self):
  inp=deepcopy(self.raw)
  inp['menu']=[{'id':'zeta','target':'alpha','treated':deepcopy(self.raw['baseline'])},
                {'id':'alpha','target':'alpha','treated':deepcopy(self.raw['baseline'])}]
  r=propose_menu(inp)
  self.assertEqual(r['attaining_ids'],['alpha','zeta']);self.assertEqual(r['representative_id'],'alpha')
  check_menu(inp,r)
 def test_empty_region_invalid(self):
  inp=deepcopy(self.raw);inp['region']=[]
  with self.assertRaises(AppError):propose_menu(inp)
 def test_invalid_model_transition_invalid(self):
  inp=deepcopy(self.raw)
  inp['menu'][1]['treated']['P'][0]['weights']['x0']='0'
  inp['menu'][1]['treated']['P'][0]['weights']['x1']='1'
  with self.assertRaises(AppError):propose_menu(inp)
 def test_duplicate_choice_id_invalid(self):
  inp=deepcopy(self.raw);inp['menu'][1]['id']=inp['menu'][0]['id']
  with self.assertRaises(AppError):propose_menu(inp)
 def test_wrong_choice_id_receipt_invalid(self):
  r=propose_menu(self.raw);r['menu_values'][0]['id']='wrong'
  with self.assertRaises(AppError):check_menu(self.raw,r)
 def test_false_optimum_invalid(self):
  r=propose_menu(self.raw);r['optimum_value']='1'
  with self.assertRaises(AppError):check_menu(self.raw,r)
 def test_missing_tied_optimizer_invalid(self):
  inp=deepcopy(self.raw);inp['menu']=[{'id':'a','target':'alpha','treated':deepcopy(self.raw['baseline'])},
                                     {'id':'b','target':'alpha','treated':deepcopy(self.raw['baseline'])}]
  r=propose_menu(inp);r['attaining_ids']=['a']
  with self.assertRaises(AppError):check_menu(inp,r)
 def test_false_value_invalid(self):
  r=propose_menu(self.raw);r['menu_values'][1]['value']='0'
  with self.assertRaises(AppError):check_menu(self.raw,r)
 def test_false_lean_status_invalid(self):
  r=propose_menu(self.raw);r['lean_status']='PROVED'
  with self.assertRaises(AppError):check_menu(self.raw,r)
 def test_false_exact_gr_status_invalid(self):
  r=propose_menu(self.raw);r['exact_GR_or_PR_certified']=True
  with self.assertRaises(AppError):check_menu(self.raw,r)
 def test_unknown_key_invalid(self):
  inp=deepcopy(self.raw);inp['fake_certificate']='PASS'
  with self.assertRaises(AppError):propose_menu(inp)
 def test_zero_horizon_all_tied(self):
  inp=deepcopy(self.raw);inp['horizon']=0
  r=propose_menu(inp);self.assertEqual(r['optimum_value'],'1')
  self.assertEqual(r['attaining_ids'],['treated','untreated'])
  check_menu(inp,r)
 def test_model_identity_prevents_receipt_reuse(self):
  r=propose_menu(self.raw);inp=deepcopy(self.raw);inp['horizon']=1
  with self.assertRaises(AppError):check_menu(inp,r)
 def test_fractional_denom_mutation_invalid(self):
  r=propose_menu(self.raw);r['baseline_survival']='0.25'
  with self.assertRaises(AppError):check_menu(self.raw,r)
 def test_action_type_target_invalid(self):
  inp=deepcopy(self.raw);inp['menu'][0]['target']='P'
  with self.assertRaises(AppError):propose_menu(inp)
 def test_start_outside_region_invalid(self):
  inp=deepcopy(self.raw);inp['start_state']=['s0','x1']
  with self.assertRaises(AppError):propose_menu(inp)
 def test_menu_too_many_invalid(self):
  inp=deepcopy(self.raw)
  inp['menu']=[{'id':'menu'+str(i),'target':'alpha','treated':deepcopy(self.raw['baseline'])} for i in range(9)]
  with self.assertRaises(AppError):propose_menu(inp)
 def test_full_cli_and_scientific_status(self):
  with tempfile.TemporaryDirectory() as tmp:
   env=os.environ.copy();env['PYTHONPATH']=str(ROOT/'src');env['PYTHONDONTWRITEBYTECODE']='1'
   cmd=[sys.executable,'-B','-m','permansson_app','frozen-menu',str(EXAMPLE),'--output',str(Path(tmp)/'run')]
   p=subprocess.run(cmd,cwd=ROOT,env=env,text=True,capture_output=True,timeout=20)
   self.assertEqual(p.returncode,0,p.stderr)
   rep=json.loads((Path(tmp)/'run/scientific_report.json').read_text())
   self.assertEqual(rep['numerical_verification'],'FROZEN_MENU_OPTIMUM_VERIFIED')
   self.assertEqual(rep['kernel_checked_proof'],'NOT_EXECUTED')
   self.assertFalse(rep['scientific_claims_verified'])

if __name__=='__main__':unittest.main()
