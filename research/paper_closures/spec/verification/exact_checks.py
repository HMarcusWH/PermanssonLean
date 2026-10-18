#!/usr/bin/env python3
"""Independent exact arithmetic for the paper specification. Not a Lean proof.
No Permansson source module is imported. All model constants and update laws are
spelled out below; the emitted tables are candidate certificate data, not axioms.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse, copy, hashlib, json, unittest

STATES = tuple((i,j,x) for i in range(3) for j in range(3) for x in (0,1))
ACTIONS = tuple(product((0,1), repeat=2))
MODES = ('E','L')
VARIANTS = ('baseline','action','update','joint')

def reward(i:int,x:int,a:tuple[int,int])->Q:
    return Q(x,2)*a[i]-Q(193,211)*a[0]*a[1]-Q(1-x,10)
def p_world(x:int,a:tuple[int,int])->Q:
    return min(Q(1),max(Q(0),(Q(9,10) if x else Q(1,4))-Q(sum(a),4)))
def clip(q:int)->int: return max(0,min(2,q))
def next_memory(mode:str,y:tuple[int,int,int],a:tuple[int,int],reset:bool)->tuple[int,int]:
    if reset:return (1,1)
    if mode=='E':return y[:2]
    x=y[2]; ref=Q(1,20) if x else -Q(1,20)
    return tuple(clip(y[i]+(2*a[i]-1)*((reward(i,x,a)>ref)-(reward(i,x,a)<ref))) for i in (0,1))
def rates(mode:str,y:tuple[int,int,int],restrain:bool)->tuple[Q,Q]:
    if restrain:return Q(0),Q(0)
    if mode=='E':return (Q(y[2],2),)*2
    return tuple(Q(9*q+1,20) for q in y[:2])
def mat(mode:str,variant:str)->tuple[tuple[Q,...],...]:
    restrain=variant in ('action','joint'); reset=variant in ('update','joint')
    rows=[]
    for y in STATES:
        row={z:Q(0) for z in STATES}; ps=rates(mode,y,restrain)
        for a in ACTIONS:
            pa=product_q(ps[i] if a[i] else 1-ps[i] for i in (0,1))
            qn=next_memory(mode,y,a,reset); pw=p_world(y[2],a)
            for xn in (0,1):row[(*qn,xn)]+=pa*(pw if xn else 1-pw)
        rows.append(tuple(row[z] for z in STATES))
    return tuple(rows)
def product_q(xs):
    r=Q(1)
    for x in xs:r*=x
    return r

def mv(M,v):return tuple(sum((p*x for p,x in zip(row,v)),Q(0)) for row in M)
def layers(M,T=3):
    vs=[tuple(Q(y[2]) for y in STATES)]
    for _ in range(T):vs.append(mv(M,vs[-1]))
    return tuple(vs)

def direct_terminal(mode,variant,T,start):
    """Stage-by-stage dictionary recursion; does not consume the matrix."""
    law={start:Q(1)}
    for _ in range(T):
        out={}
        for y,w in law.items():
            ps=rates(mode,y,variant in ('action','joint'))
            for a in ACTIONS:
                pa=(ps[0] if a[0] else 1-ps[0])*(ps[1] if a[1] else 1-ps[1])
                qn=next_memory(mode,y,a,variant in ('update','joint'))
                pw=p_world(y[2],a)
                for x,p in ((0,1-pw),(1,pw)):
                    z=(*qn,x);out[z]=out.get(z,Q(0))+w*pa*p
        law=out
    return sum((p for z,p in law.items() if z[2]),Q(0))

def determinant(A):
    a=[list(row) for row in A];n=len(a);d=Q(1)
    for j in range(n):
        k=next((i for i in range(j,n) if a[i][j]),None)
        if k is None:return Q(0)
        if k!=j:a[j],a[k]=a[k],a[j];d=-d
        p=a[j][j];d*=p
        for i in range(j+1,n):
            c=a[i][j]/p
            for l in range(j,n):a[i][l]-=c*a[j][l]
    return d

def stationary_cramer(P):
    n=len(P)
    if not n:raise ValueError('nonempty class required')
    M=[[Q(i==j)-P[j][i]+1 for j in range(n)]for i in range(n)]
    det=determinant(M)
    if not det:raise ValueError('singular class system')
    v=[]
    for j in range(n):
        C=[r[:]for r in M]
        for i in range(n):C[i][j]=Q(1)
        v.append(determinant(C)/det)
    return tuple(v)

def x1_payload():
    out={'schema':'Permansson.PaperSpec.X1.ExactTables.v1',
         'status':'EXACT_ARITHMETIC_CANDIDATE_NOT_LEAN_CERTIFIED',
         'source_commit':'39279799834ae536bda715dedecdc11a32bf6c82',
         'state_order':[list(y)for y in STATES], 'table_horizons':[0,1,2,3],
         'property':'P(X_3=1), terminal reentry permitted', 'models':{},'margins':{}}
    for m in MODES:
        vs={v:layers(mat(m,v))for v in VARIANTS}
        for v in VARIANTS:
            out['models'][m+'/'+v]={'matrix':[[str(x)for x in r]for r in mat(m,v)],
                                   'values':[[str(x)for x in r]for r in vs[v]]}
        for v in VARIANTS[1:]:
            rows=[{'state':list(y),'baseline':str(vs['baseline'][3][j]),
                   'intervened':str(vs[v][3][j]),
                   'signed_effect':str(vs[v][3][j]-vs['baseline'][3][j]),
                   'absolute_effect':str(abs(vs[v][3][j]-vs['baseline'][3][j]))}
                  for j,y in enumerate(STATES)if y[2]]
            k=min(Q(r['absolute_effect'])for r in rows)
            out['margins'][m+'/'+v]={'rows':rows,'infimum':str(k),
                                    'attainers':[r['state']for r in rows if Q(r['absolute_effect'])==k]}
    return out

def validate_candidate_tables(data):
    """Check supplied literal data, never regenerate it and compare to itself.

    Primitive reification uses the explicit reference functions above. The DP,
    effects, minima and attainers are then checked directly from candidate rows.
    This is an executable cross-check, not a verified JSON decoder or Lean proof.
    """
    def need(ok, code):
        if not ok:raise ValueError(code)
    need(data.get('state_order')==[list(y)for y in STATES], 'E_STATE_ORDER')
    need(data.get('table_horizons')==[0,1,2,3], 'E_HORIZON')
    need(set(data.get('models',{}))=={m+'/'+v for m,v in product(MODES,VARIANTS)},'E_MODELS')
    need(set(data.get('margins',{}))=={m+'/'+v for m,v in product(MODES,VARIANTS[1:])},'E_MARGIN_KEYS')
    values={}
    for m,v in product(MODES,VARIANTS):
        key=m+'/'+v; record=data['models'][key]
        M=tuple(tuple(Q(x)for x in row)for row in record['matrix'])
        need(len(M)==18 and all(len(row)==18 for row in M),'E_MATRIX_SHAPE')
        need(M==mat(m,v),'E_ACTUAL_PRIMITIVES')
        V=tuple(tuple(Q(x)for x in row)for row in record['values'])
        need(len(V)==4 and all(len(row)==18 for row in V),'E_TABLE_SHAPE')
        need(V[0]==tuple(Q(y[2])for y in STATES),'E_INITIAL_SCORE')
        for t in range(3):need(V[t+1]==mv(M,V[t]),'E_DP_EQUATION')
        values[key]=V[3]
    for m,v in product(MODES,VARIANTS[1:]):
        r=data['margins'][m+'/'+v];rows=r['rows']
        starts=[list(y)for y in STATES if y[2]]
        need([z['state']for z in rows]==starts,'E_COMPARISON_STARTS')
        effects=[]
        for row in rows:
            i=STATES.index(tuple(row['state']))
            base=values[m+'/baseline'][i];changed=values[m+'/'+v][i]
            need(Q(row['baseline'])==base and Q(row['intervened'])==changed,'E_OUTPUT_BINDING')
            need(Q(row['signed_effect'])==changed-base,'E_SIGNED_EFFECT')
            effect=abs(changed-base);effects.append(effect)
            need(Q(row['absolute_effect'])==effect,'E_ABSOLUTE_EFFECT')
        k=min(effects)
        need(Q(r['infimum'])==k,'E_INFIMUM')
        need(r['attainers']==[row['state']for row,e in zip(rows,effects)if e==k],'E_ATTAINERS')
    return True

class ExactChecks(unittest.TestCase):
    def test_x1_all_144_rows(self):
        for m,v in product(MODES,VARIANTS):
            for row in mat(m,v):self.assertEqual(sum(row),1);self.assertGreaterEqual(min(row),0)
    def test_x1_all_432_table_step_equations(self):
        for m,v in product(MODES,VARIANTS):
            K=mat(m,v); V=layers(K)
            for t in range(3):self.assertEqual(mv(K,V[t]),V[t+1])
    def test_x1_72_terminal_values_stage_reconstruction(self):
        for m,v in product(MODES,VARIANTS):
            V=layers(mat(m,v))[3]
            for j,y in enumerate(STATES):
                if y[2]:self.assertEqual(V[j],direct_terminal(m,v,3,y))
    def test_x1_six_margins_and_attainers(self):
        r=x1_payload()['margins'];E={'action':Q(271,800),'update':Q(0),'joint':Q(271,800)}
        L={'action':Q(3010663529,6400000000),'update':Q(1244820951,25600000000),'joint':Q(3010663529,6400000000)}
        for m,expected in [('E',E),('L',L)]:
            for v,k in expected.items():self.assertEqual(Q(r[m+'/'+v]['infimum']),k)
        for v in E:self.assertEqual(len(r['E/'+v]['attainers']),9)
        self.assertEqual(r['L/action']['attainers'],[[0,0,1]])
        self.assertEqual(r['L/joint']['attainers'],[[0,0,1]])
        self.assertEqual(r['L/update']['attainers'],[[2,2,1]])
    def test_x1_update_simplification(self):
        for y,a in product(STATES,ACTIONS):
            inc=(-1,-1)if y[2] and a==(1,1)else (1,1)if y[2]else tuple(1-2*t for t in a)
            self.assertEqual(next_memory('L',y,a,False),tuple(clip(y[i]+inc[i])for i in (0,1)))
    def test_x1_exact_advantages_both_players(self):
        beta=Q(9,10);V={0:-Q(121,211),1:-Q(81,211)}
        for i,x,own in product((0,1),(0,1),(0,1)):
            p=Q(x,2);q=Q(0)
            for other in (0,1):
                a=(own,other)if i==0 else (other,own)
                pw=p_world(x,a);q+=(p if other else 1-p)*(reward(i,x,a)+beta*(pw*V[1]+(1-pw)*V[0]))
            self.assertEqual(V[x]-q,Q(9,211)if not x and own else Q(0))
    def test_x1_leak_and_nonpromotion(self):
        y=STATES.index((1,1,1))
        for m in MODES:self.assertEqual(sum(p for z,p in zip(STATES,mat(m,'baseline')[y])if z[2]),Q(13,20))
    def test_primitive_product_saturation(self):
        a,p,u=Q(1,10),Q(1,5),Q(1,4)
        good=(1-a)*(1-p)*(1-u)
        self.assertEqual(1-good,Q(23,50));self.assertLessEqual(1-good,a+p+u)
    def test_quotient_good_mass(self):
        K=((Q(45,100),Q(45,100),Q(1,10),Q(0)),(Q(4,5),Q(0),Q(0),Q(1,5)),
           (Q(1,5),Q(0),Q(2,5),Q(2,5)),(Q(0),Q(1,10),Q(0),Q(9,10)))
        B=((Q(17,20),Q(3,20)),(Q(3,20),Q(17,20)));q=lambda x:x//2
        R=[]
        for i,row in enumerate(K):
            proj=[sum(row[j]for j in range(4)if q(j)==z)for z in (0,1)]
            R.append(tuple(row[j]*min(proj[q(j)],B[q(i)][q(j)])/proj[q(j)]if proj[q(j)]else Q(0) for j in range(4)))
            self.assertGreaterEqual(sum(R[-1]),Q(19,20))
            for z in (0,1):self.assertLessEqual(sum(R[-1][j]for j in range(4)if q(j)==z),B[q(i)][z])
        good={ (0,):Q(1)};fine=good.copy();coarse={(0,):Q(1)}
        for t in range(1,5):
            def extend(law,M):
                out={}
                for h,w in law.items():
                    for j,p in enumerate(M[h[-1]]):out[h+(j,)]=w*p
                return out
            good=extend(good,R);fine=extend(fine,K);coarse=extend(coarse,B)
            pg={};pf={}
            for law,d in ((good,pg),(fine,pf)):
                for h,w in law.items():
                    z=tuple(q(j)for j in h);d[z]=d.get(z,Q(0))+w
            self.assertGreaterEqual(sum(good.values()),Q(19,20)**t)
            for h,w in pg.items():self.assertLessEqual(w,coarse[h]);self.assertLessEqual(w,pf[h])
            tv=sum(abs(pf.get(h,0)-coarse.get(h,0))for h in set(pf)|set(coarse))/2
            self.assertLessEqual(tv,1-Q(19,20)**t)
    def test_residence_monitor_exhaustive(self):
        for T in range(4):
            for m in range(4):
                N=T+m
                for word in product((0,1),repeat=N+1):
                    literal=any(all(word[e+j]for j in range(m+1))for e in range(T+1))
                    k=0;done=False
                    for y in word:k=min(m+1,k+1)if y else 0;done=done or k==m+1
                    self.assertEqual(done,literal)
    def test_first_entry_differs_from_retry(self):
        word=(1,0,1,1);m=1
        self.assertTrue(any(all(word[e+j]for j in range(2))for e in range(3)))
        e=word.index(1);self.assertFalse(all(word[e+j]for j in range(2)))
    def test_risk_constraint_exact(self):
        rho=Q(1,20);risky=rho/Q(1,10)
        self.assertEqual(risky,Q(1,2));self.assertEqual(Q(4,5)+Q(1,10)*risky,Q(17,20))
    def test_robust_quantifiers_and_rectangularity(self):
        self.assertEqual(min(Q(1,2),1-Q(1,2)),Q(1,2))
        self.assertEqual(min(Q(1,10)*Q(9,10),Q(9,10)*Q(1,10)),Q(9,100))
        self.assertEqual(min(Q(1,10),Q(9,10))**2,Q(1,100))
    def test_c11_cramer_families(self):
        Ps=[((Q(0),Q(1)),(Q(1),Q(0))),((Q(1),),)]
        for n in range(2,7):
            Ps.append(tuple(tuple(Q(1+((3*i+5*j)%7),sum(1+((3*i+5*k)%7)for k in range(n)))for j in range(n))for i in range(n)))
        for P in Ps:
            p=stationary_cramer(P)
            self.assertEqual(sum(p),1);self.assertGreater(min(p),0)
            self.assertEqual(tuple(sum(p[i]*P[i][j]for i in range(len(p)))for j in range(len(p))),p)
    def test_strict_autonomous_anchor_paths(self):
        # q=0,1 is a closed autonomous key set. q=2 never occurs from q=0.
        # Compare complete four-transition path laws, not just endpoint marginals.
        ys=tuple(product(range(3),(0,1)))
        for controls in product((0,1),repeat=6):
            laws=[]
            for variant in (0,1):
                law={((0,0),):Q(1)}
                for _ in range(4):
                    out={}
                    for history,w in law.items():
                        y=history[-1]
                        p=(Q(1,4),Q(3,4),Q(variant))[y[0]]
                        a1=controls[ys.index(y)]
                        for a2,pa in ((0,1-p),(1,p)):
                            new=history+((a2,a1),)
                            out[new]=out.get(new,Q(0))+w*pa
                    law=out
                laws.append(law)
            self.assertEqual(*laws)
    def test_new_positive_economic_witness(self):
        beta=Q(3,4);V=Q(4)
        self.assertEqual(1+beta*V,V);self.assertLess(Q(2),V)
        P=((Q(1,2),Q(1,2),Q(0)),(Q(1,2),Q(1,2),Q(0)),(Q(0),Q(0),Q(1)))
        pi=(Q(1,2),Q(1,2),Q(0))
        self.assertEqual(tuple(sum(pi[i]*P[i][j]for i in range(3))for j in range(3)),pi)
    def test_scalar_defect_seam(self):
        H=((Q(0),Q(1)),(Q(1),Q(2)));v=(1,-1)
        self.assertEqual(sum(v[i]*H[i][j]*v[j]for i in range(2)for j in range(2)),0)
        self.assertEqual(determinant(H),-1) # rank two, not scalar rank one
    def test_gram_witness(self):
        for x,y in [((Q(1),Q(0)),(Q(1),Q(2))),((Q(2),Q(1)),(Q(1),Q(3)))]:
            dot=lambda a,b:sum(i*j for i,j in zip(a,b));a=dot(x,x);b=dot(x,y);d=a*dot(y,y)-b*b
            w=tuple(a*yi-b*xi for xi,yi in zip(x,y));c=Q(3,2)
            self.assertEqual(c*(dot(x,w)**2-dot(y,w)**2),-c*d*d)
            self.assertEqual(dot(w,w),a*d)
    def test_singular_schur_compatibility(self):
        # H=diag(1,0), b=(0,1): a pseudoinverse alone misses the negative direction.
        H=((Q(1),Q(0)),(Q(0),Q(0)));b=(Q(0),Q(1));v=(Q(0),Q(-1));c=Q(1)
        self.assertLess(sum(v[i]*H[i][j]*v[j]for i in range(2)for j in range(2))+2*sum(v[i]*b[i]for i in range(2))+c,0)
    def test_discounted_geometric_error_sum(self):
        b=Q(9,10);eta=Q(1,20);closed=b*eta/(1-b*(1-eta))
        approx=(1-b)*sum(b**t*(1-(1-eta)**t)for t in range(400))
        self.assertLessEqual(approx,closed);self.assertLess(closed-approx,b**400)

    def test_delivered_candidate_table_validates(self):
        self.assertTrue(validate_candidate_tables(x1_payload()))
    def test_each_54_supplied_effect_mutations_rejected(self):
        data=x1_payload()
        for key in data['margins']:
            for i in range(9):
                bad=copy.deepcopy(data)
                row=bad['margins'][key]['rows'][i]
                row['absolute_effect']=str(Q(row['absolute_effect'])+Q(1,997))
                with self.assertRaisesRegex(ValueError,'E_ABSOLUTE_EFFECT'):
                    validate_candidate_tables(bad)
    def test_missing_start_and_wrong_attainer_rejected(self):
        bad=x1_payload();bad['margins']['L/action']['rows'].pop(0)
        with self.assertRaisesRegex(ValueError,'E_COMPARISON_STARTS'):validate_candidate_tables(bad)
        bad=x1_payload();bad['margins']['L/action']['attainers']=[[1,1,1]]
        with self.assertRaisesRegex(ValueError,'E_ATTAINERS'):validate_candidate_tables(bad)
    def test_stochastic_but_wrong_world_matrix_rejected(self):
        bad=x1_payload();row=bad['models']['L/baseline']['matrix'][0]
        positive=next(i for i,x in enumerate(row)if Q(x)>0);j=(positive+1)%18
        eps=Q(row[positive])/2;row[positive]=str(Q(row[positive])-eps);row[j]=str(Q(row[j])+eps)
        self.assertEqual(sum(Q(x)for x in row),1)
        with self.assertRaisesRegex(ValueError,'E_ACTUAL_PRIMITIVES'):validate_candidate_tables(bad)
    def test_wrong_horizon_and_table_value_rejected(self):
        bad=x1_payload();bad['table_horizons']=[0,1,2,4]
        with self.assertRaisesRegex(ValueError,'E_HORIZON'):validate_candidate_tables(bad)
        bad=x1_payload();bad['models']['L/update']['values'][3][5]='1/2'
        with self.assertRaisesRegex(ValueError,'E_DP_EQUATION'):validate_candidate_tables(bad)
    def test_six_wrong_reported_minima_rejected(self):
        for key in x1_payload()['margins']:
            bad=x1_payload();r=bad['margins'][key];r['infimum']=str(Q(r['infimum'])+Q(1,997))
            with self.assertRaisesRegex(ValueError,'E_INFIMUM'):validate_candidate_tables(bad)
    def test_label_swap_rejected(self):
        bad=x1_payload();d=bad['models'];d['L/action'],d['L/update']=d['L/update'],d['L/action']
        with self.assertRaisesRegex(ValueError,'E_ACTUAL_PRIMITIVES'):validate_candidate_tables(bad)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(ExactChecks)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    payload=x1_payload()
    validate_candidate_tables(payload)
    raw=(json.dumps(payload,indent=2,sort_keys=True)+'\n').encode()
    (args.output/'x1_exact_tables.json').write_bytes(raw)
    report={'status':'PASS'if result.wasSuccessful()else'FAIL','test_methods_run':result.testsRun,
            'failures':len(result.failures),'errors':len(result.errors),'skipped':len(result.skipped),
            'x1_table_sha256':hashlib.sha256(raw).hexdigest(),
            'scope':'Independent exact finite calculations; no Lean compilation or universal-proof validation.'}
    (args.output/'exact_check_report.json').write_text(json.dumps(report,indent=2)+'\n')
    raise SystemExit(0 if result.wasSuccessful()else 1)
if __name__=='__main__':main()
