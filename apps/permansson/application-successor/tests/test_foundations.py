"""Positive, negative, boundary and semantic-mutation checks for new foundations."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.identity import canonical_bytes,semantic_identity,rational_text
from permansson_app.finite_world import parse_finite_world,induced_kernel,compare_strategic_intervention
from permansson_app.receipts.finite_world import emit_finite_receipt,check_finite_receipt
from permansson_app.engines.lp_types import parse_lp
from permansson_app.engines.lp import propose_lp_optimum
from permansson_app.receipts.lp import check_lp_certificate,check_farkas_certificate


def example_world():
    S=['s0','s1'];X=['x0','x1'];A=['stay','switch']
    pairs=[(s,x) for s in S for x in X]
    return {
      'format':'Permansson.App.FiniteStrategicWorld.v1',
      'states':{'strategic':S,'world':X,'actions':A},
      'feasible':[{'s':s,'x':x,'actions':A} for s,x in pairs],
      'alpha':[{'s':s,'x':x,'weights':{'stay':'1/2','switch':'1/2'}} for s,x in pairs],
      'P':[{'s':s,'x':x,'a':a,'weights':{xp:'1' if xp==(x if a=='stay' else ('x1' if x=='x0' else 'x0')) else '0' for xp in X}} for s,x in pairs for a in A],
      'U':[{'s':s,'x':x,'a':a,'xp':xp,'weights':{sp:'1' if sp==(s if a=='stay' else ('s1' if s=='s0' else 's0')) else '0' for sp in S}} for s,x in pairs for a in A for xp in X]
    }


def example_lp():
    return {'format':'Permansson.App.ExactLP.v1','variables':['x','y'],
      'objective':{'sense':'maximize','coefficients':{'x':'1','y':'1'}},
      'bounds':{'x':{'lower':'0','upper':None},'y':{'lower':'0','upper':None}},
      'constraints':[{'id':'cap','coefficients':{'x':'1','y':'1'},'relation':'<=','rhs':'1'}]}


class IdentityTests(unittest.TestCase):
    def test_utf16_order(self):
        self.assertEqual(canonical_bytes({'\ue000':1,'\U00010000':2}).decode('utf-8'),'{"\U00010000":2,"\ue000":1}')
    def test_escaped_controls(self):
        self.assertEqual(canonical_bytes({'a':'\n\t"\\'}),b'{"a":"\\n\\t\\"\\\\"}')
    def test_insertion_order(self):
        self.assertEqual(semantic_identity('k',{'z':1,'a':2}),semantic_identity('k',{'a':2,'z':1}))
    def test_float_rejected(self):
        with self.assertRaises(AppError): canonical_bytes({'x':1.0})
    def test_bool_rejected_as_number(self):
        with self.assertRaises(AppError): canonical_bytes({'x':2**53})
    def test_surrogate_rejected(self):
        with self.assertRaises(AppError): canonical_bytes({'x':'\ud800'})
    def test_explicit_rational(self):
        self.assertEqual(rational_text(Fraction(2,4)),'1/2')


class ResultRationalTests(unittest.TestCase):
    def test_lean_emitters_never_parse_receipts_with_the_input_bound(self):
        # Emitters read computed receipt values (and engine-normalised text);
        # the 256-bit input parser would reject correct large results.
        from permansson_app.proof import nonlinear_emit
        emitters=sorted(Path(nonlinear_emit.__file__).parent.glob('*_emit.py'))  # wherever it is imported from
        self.assertGreaterEqual(len(emitters),20)
        offenders=[p.name for p in emitters if 'exact_ratio(' in p.read_text(encoding='utf-8')]
        self.assertEqual(offenders,[])

    def test_generated_files_are_never_read_with_the_request_limit(self):
        # Receipts and candidate metadata grow with the result; they are read
        # with strict_json.read_result, requests with strict_read.
        import re
        from permansson_app.proof import nonlinear_emit
        modules=sorted(Path(nonlinear_emit.__file__).parent.glob('*.py'))
        pattern=re.compile(r"(receipt\w*|actual_raw)\s*,\s*\w+\s*=\s*strict_read\(")
        offenders=[p.name for p in modules if pattern.search(p.read_text(encoding='utf-8'))]
        self.assertEqual(offenders,[])
        self.assertGreaterEqual(sum('read_result(' in p.read_text(encoding='utf-8') for p in modules),24)

    """exact_result: canonical reduced rationals with the result-sized bound."""
    def test_accepts_large_canonical_results(self):
        from permansson_app.finite_world import exact_result
        self.assertEqual(exact_result('1/'+str(2**300),probability=True),Fraction(1,2**300))
        self.assertEqual(exact_result('-7/3'),Fraction(-7,3))
    def test_rejects_noncanonical_oversized_and_out_of_range(self):
        from permansson_app.finite_world import MAX_RESULT_BITS,exact_result
        for text,code in (('2/4','RATIONAL_FORMAT'),('1/1','RATIONAL_FORMAT'),('01','RATIONAL_FORMAT'),
                          ('1/'+str(2**(MAX_RESULT_BITS+1)),'RATIONAL_SIZE'),('3/2','PROBABILITY'),
                          (1,'RATIONAL_FORMAT'),('1.5','RATIONAL_FORMAT')):
            with self.subTest(text=str(text)[:20]),self.assertRaises(AppError) as raised:
                exact_result(text,probability=True)
            self.assertEqual(raised.exception.code,code)
class FiniteTests(unittest.TestCase):
    def setUp(self):
        self.raw=example_world()
        self.model=parse_finite_world(self.raw)
    def test_exact_atom(self):
        K=induced_kernel(self.model)
        self.assertEqual(K[0],(Fraction(1,2),Fraction(0),Fraction(0),Fraction(1,2)))
        self.assertEqual(sum(K[0]),1)
    def test_receipt_check(self):
        r=emit_finite_receipt(self.model)
        self.assertEqual(check_finite_receipt(self.model,r)['checked_atoms'],16)
    def test_kernel_atoms_beyond_the_input_precision_are_checked(self):
        # alpha*P of two ~200-bit input rationals is a ~400-bit kernel atom.
        raw=deepcopy(self.raw)
        p,q=Fraction(1,2**200+1),Fraction(1,2**200+3)
        raw['alpha'][0]['weights']={a:rational_text(w) for a,w in zip(raw['alpha'][0]['weights'],(p,1-p))}
        first=next(row for row in raw['P'] if row['s']==raw['alpha'][0]['s'] and row['x']==raw['alpha'][0]['x'])
        first['weights']={y:rational_text(w) for y,w in zip(first['weights'],(q,1-q))}
        model=parse_finite_world(raw)
        receipt=emit_finite_receipt(model)
        self.assertGreater(max(Fraction(v).denominator.bit_length() for v in receipt['kernel'][0]),256)
        self.assertEqual(check_finite_receipt(model,receipt)['checked_atoms'],16)
    def test_receipt_mutant(self):
        r=emit_finite_receipt(self.model)
        r['kernel'][0][0]='1/3'
        with self.assertRaises(AppError):check_finite_receipt(self.model,r)
    def test_foreign_semantic_identity(self):
        r=emit_finite_receipt(self.model)
        r['model_semantic_identity']['sha256']='0'*64
        with self.assertRaises(AppError):check_finite_receipt(self.model,r)
    def test_forged_proof_flag(self):
        r=emit_finite_receipt(self.model)
        r['lean_status']='PASSED'
        with self.assertRaises(AppError):check_finite_receipt(self.model,r)
    def test_alpha_mass(self):
        p=deepcopy(self.raw);p['alpha'][0]['weights']['stay']='1/3'
        with self.assertRaises(AppError):parse_finite_world(p)
    def test_P_mass(self):
        p=deepcopy(self.raw);p['P'][0]['weights']['x0']='1/2'
        with self.assertRaises(AppError):parse_finite_world(p)
    def test_U_row_missing(self):
        p=deepcopy(self.raw);p['U'].pop()
        with self.assertRaises(AppError):parse_finite_world(p)
    def test_alpha_infeasible(self):
        p=deepcopy(self.raw);p['feasible'][0]['actions']=['stay']
        with self.assertRaises(AppError):parse_finite_world(p)
    def test_duplicate_alpha_row(self):
        p=deepcopy(self.raw);p['alpha'].append(deepcopy(p['alpha'][0]))
        with self.assertRaises(AppError):parse_finite_world(p)
    def test_held_fixed_P(self):
        p=deepcopy(self.raw)
        p['P'][0]['weights']={'x0':'0','x1':'1'}
        with self.assertRaises(AppError):compare_strategic_intervention(self.model,parse_finite_world(p),'alpha')
    def test_valid_alpha_intervention(self):
        p=deepcopy(self.raw);p['alpha'][0]['weights']={'stay':'1','switch':'0'}
        x=compare_strategic_intervention(self.model,parse_finite_world(p),'alpha')
        self.assertEqual(x['target'],'alpha')
    def test_normalized_rational_identity(self):
        p=deepcopy(self.raw);p['alpha'][0]['weights']={'stay':'2/4','switch':'3/6'}
        self.assertEqual(self.model.semantic_id(),parse_finite_world(p).semantic_id())
    def test_false_raw_K_cannot_pass(self):
        p=deepcopy(self.raw);p['K']=[['1']]
        with self.assertRaises(AppError):parse_finite_world(p)


class LPTests(unittest.TestCase):
    def setUp(self): self.lp=parse_lp(example_lp())
    def test_exact_optimum(self):
        r=propose_lp_optimum(self.lp)
        self.assertEqual(r['status'],'CHECKED_OPTIMAL_CANDIDATE')
        self.assertEqual(check_lp_certificate(self.lp,r['receipt'])['status'],'OPTIMAL_VERIFIED')
    def test_tied_fractional_not_solver_vector(self):
        # Reference proposer can use [0,1]. A different tied fractional optimum is equally valid.
        r=propose_lp_optimum(self.lp)['receipt']
        r['primal']=['1/2','1/2']
        self.assertEqual(check_lp_certificate(self.lp,r)['status'],'OPTIMAL_VERIFIED')
    def test_forged_objective_rejected(self):
        r=propose_lp_optimum(self.lp)['receipt'];r['objective_value']='2'
        with self.assertRaises(AppError):check_lp_certificate(self.lp,r)
    def test_primal_violation(self):
        r=propose_lp_optimum(self.lp)['receipt'];r['primal']=['1','1']
        with self.assertRaises(AppError):check_lp_certificate(self.lp,r)
    def test_dual_violation(self):
        r=propose_lp_optimum(self.lp)['receipt'];r['dual']=['0']
        with self.assertRaises(AppError):check_lp_certificate(self.lp,r)
    def test_foreign_objective_identity(self):
        r=propose_lp_optimum(self.lp)['receipt'];r['model_semantic_identity']={'profile':'invalid','sha256':'0'*64}
        with self.assertRaises(AppError):check_lp_certificate(self.lp,r)
    def test_affine_lower_and_minimize(self):
        q=example_lp();q['variables']=['x'];q['objective']={'sense':'minimize','coefficients':{'x':'1'}}
        q['bounds']={'x':{'lower':'-2','upper':'-1'}};q['constraints']=[]
        lp=parse_lp(q);r=propose_lp_optimum(lp)
        self.assertEqual(r['status'],'CHECKED_OPTIMAL_CANDIDATE')
        self.assertEqual(r['receipt']['primal'],['-2'])
        self.assertEqual(r['receipt']['objective_value'],'-2')
    def test_equality_and_ge_translation(self):
        q=example_lp();q['constraints']=[{'id':'eq','coefficients':{'x':'1','y':'1'},'relation':'=','rhs':'1'},
                                         {'id':'min','coefficients':{'x':'1','y':'0'},'relation':'>=','rhs':'1/2'}]
        lp=parse_lp(q);r=propose_lp_optimum(lp)
        self.assertEqual(r['status'],'CHECKED_OPTIMAL_CANDIDATE')
        self.assertEqual(r['receipt']['objective_value'],'1')
    def test_farkas_exact(self):
        q=example_lp();q['variables']=['x'];q['objective']={'sense':'maximize','coefficients':{'x':'1'}}
        q['bounds']={'x':{'lower':'0','upper':None}};q['constraints']=[{'id':'impossible','coefficients':{'x':'1'},'relation':'<=','rhs':'-1'}]
        lp=parse_lp(q)
        r={'format':'Permansson.App.LPFarkasReceipt.v1','model_semantic_identity':lp.semantic_id(),'multiplier':['1']}
        self.assertEqual(check_farkas_certificate(lp,r)['status'],'INFEASIBILITY_VERIFIED')
    def test_farkas_false(self):
        r={'format':'Permansson.App.LPFarkasReceipt.v1','model_semantic_identity':self.lp.semantic_id(),'multiplier':['1']}
        with self.assertRaises(AppError):check_farkas_certificate(self.lp,r)
    def test_bounded_does_not_prove_infeasible(self):
        r=propose_lp_optimum(self.lp,max_combinations=1)
        self.assertEqual(r['status'],'RESOURCE_LIMIT')
    def test_noncanonical_type(self):
        q=example_lp();q['objective']['coefficients']['x']=1
        with self.assertRaises(AppError):parse_lp(q)
    def test_declared_precision(self):
        q=example_lp();q['objective']['coefficients']['x']=str(2**260)
        with self.assertRaises(AppError):parse_lp(q)
    def test_upper_below_lower(self):
        q=example_lp();q['bounds']['x']['upper']='-1'
        with self.assertRaises(AppError):parse_lp(q)

if __name__=='__main__':unittest.main()
