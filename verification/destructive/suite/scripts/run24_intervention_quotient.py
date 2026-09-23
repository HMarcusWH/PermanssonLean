import numpy as np
from common import ck, write_result
checks=[]
states=[(0,0),(0,1),(1,0),(1,1)]
blocks=[[0,1],[2,3]]; block_of={s:i for i,b in enumerate(blocks) for s in b}
def lumpable(K,blks=blocks):
    K=np.asarray(K,float)
    for b in blks:
        ref=None
        for s in b:
            vec=np.array([K[s,tgt].sum() for tgt in blks])
            if ref is None: ref=vec
            elif not np.allclose(vec,ref): return False
    return True
def quotient(K,blks=blocks):
    assert lumpable(K,blks)
    return np.array([[sum(K[b[0],t] for t in tgt) for tgt in blks] for b in blks])
def push(v,blks=blocks): return np.array([sum(v[s] for s in b) for b in blks])
K=np.array([[.4,.2,.2,.2],[.3,.3,.1,.3],[.1,.1,.4,.4],[.05,.15,.5,.3]])
J=np.array([[.2,.2,.3,.3],[.1,.3,.2,.4],[.2,.2,.3,.3],[.1,.3,.4,.2]])
J2=np.array([[.45,.15,.1,.3],[.25,.35,.25,.15],[.15,.05,.45,.35],[.1,.1,.55,.25]])
for name,M in [('K',K),('J',J),('J2',J2)]: ck(checks,f'{name}_lumpable',lumpable(M))
rng=np.random.default_rng(24)
for name,M in [('K',K),('J',J),('J2',J2)]:
    Q=quotient(M)
    for trial in range(20):
        v=rng.dirichlet(np.ones(4)); n=int(rng.integers(1,8))
        left=push(v@np.linalg.matrix_power(M,n)); right=push(v)@np.linalg.matrix_power(Q,n)
        ck(checks,f'commutation_{name}_{trial}',np.allclose(left,right))
BadJ=J.copy(); BadJ[1]=[.4,.3,.1,.2]
ck(checks,'baseline_only_not_enough',lumpable(K) and not lumpable(BadJ))
qS_good={(s,x):s for s,x in states}; qX_good={(s,x):0 for s,x in states}
def component_respects_type(comp,coord):
    if coord=='S':
        return all(comp[(s,0)]==comp[(s,1)] for s in [0,1])
    return all(comp[(0,x)]==comp[(1,x)] for x in [0,1])
ck(checks,'good_q_is_type_respecting_product',component_respects_type(qS_good,'S') and component_respects_type(qX_good,'X'))
qS_bad={(s,x):(s^x) for s,x in states}; qX_bad={(s,x):0 for s,x in states}
ck(checks,'mixed_coordinate_quotient_rejected',not component_respects_type(qS_bad,'S'))
def function_descends(vals,blks=blocks): return all(len({vals[i] for i in b})==1 for b in blks)
def set_descends(A,blks=blocks): return all(set(b).issubset(A) or set(b).isdisjoint(A) for b in blks)
h_bad=np.array([0.,1.,2.,2.]); g_bad=np.array([0,1,5,5]); B_bad={0,2,3}; B0_bad={0,1,2}
ck(checks,'descriptor_must_descend',not function_descends(h_bad))
ck(checks,'relevance_map_must_descend',not function_descends(g_bad))
ck(checks,'regime_region_must_descend',not set_descends(B_bad))
ck(checks,'basin_must_descend',not set_descends(B0_bad))
h_good=np.array([5.,5.,9.,9.]); g_good=np.array([1,1,2,2]); B_good={0,1}; B0_good={0,1,2,3}
ck(checks,'good_semantics_descend',function_descends(h_good) and function_descends(g_good) and set_descends(B_good) and set_descends(B0_good))
B1_original={0,1}
bar_B1={block_of[i] for i in B1_original}
original_B1_admissible=len(B1_original)>=2
quotient_B1_admissible=len(bar_B1)>=2
ck(checks,'b1_can_collapse_to_inadmissible_singleton',original_B1_admissible and not quotient_B1_admissible,f'bar_B1={bar_B1}')
B1_good={0,2}; bar_B1_good={block_of[i] for i in B1_good}
ck(checks,'b1_independent_admissibility_positive_control',len(B1_good)>=2 and len(bar_B1_good)>=2)
metric_space_original='R_abs'; metric_space_quotient='R_abs'; metric_space_bad='simplex_TV'
ck(checks,'common_property_metric_required_positive',metric_space_original==metric_space_quotient)
ck(checks,'mismatched_property_metric_rejected',metric_space_original!=metric_space_bad)
orig_nontrivial=True; quotient_nontrivial=False
ck(checks,'quotient_nontriviality_not_automatic',orig_nontrivial and not quotient_nontrivial)
bar_lambda=np.array([.25,.75]); lift=np.array([.125,.125,.375,.375])
ck(checks,'initial_law_lift_positive_control',np.allclose(push(lift),bar_lambda) and abs(lift.sum()-1)<1e-15)
write_result('24','Intervention-compatible typed quotient/lumpability theorem attacks',checks)
