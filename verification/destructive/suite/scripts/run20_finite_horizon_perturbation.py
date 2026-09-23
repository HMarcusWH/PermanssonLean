import numpy as np
from common import ck, write_result, tv, path_distribution, tv_dict
checks=[]; rng=np.random.default_rng(17020)
p=np.array([1.,0.]); q=np.array([.9,.1])
ck(checks,'tv_convention_half_l1',abs(tv(p,q)-.1)<1e-15 and abs(np.abs(p-q).sum()-.2)<1e-15,f'tv={tv(p,q)} l1={np.abs(p-q).sum()}')
p3=np.array([.6,.3,.1]); q3=np.array([.2,.5,.3])
sup=0.0
for mask in range(1<<3):
    inds=[i for i in range(3) if mask&(1<<i)]
    sup=max(sup,abs(p3[inds].sum()-q3[inds].sum()))
ck(checks,'tv_equals_sup_event',abs(tv(p3,q3)-sup)<1e-15,f'tv={tv(p3,q3)} sup={sup}')
for trial in range(120):
    n=3; eps=float(rng.uniform(.001,.15)); T=int(rng.integers(1,6))
    K=rng.dirichlet(np.ones(n),size=n); R=rng.dirichlet(np.ones(n),size=n); Kt=(1-eps)*K+eps*R
    roweps=max(tv(K[i],Kt[i]) for i in range(n))
    init=rng.dirichlet(np.ones(n))
    pth=path_distribution(K,init,T); qth=path_distribution(Kt,init,T); actual=tv_dict(pth,qth)
    bound=1-(1-roweps)**T
    ck(checks,f'random_coupling_bound_{trial}',actual<=bound+1e-10,f'actual={actual:.6g} bound={bound:.6g} roweps={roweps:.6g} T={T}')
    ck(checks,f'union_bound_{trial}',bound<=T*roweps+1e-12)
for eps in [0.0,.01,.1,.3,1.0]:
  K=np.array([[1,0],[0,1]],float); Kt=np.array([[1-eps,eps],[0,1]],float); init=np.array([1.,0.])
  for T in [1,2,5,10]:
    actual=tv_dict(path_distribution(K,init,T),path_distribution(Kt,init,T)); expected=1-(1-eps)**T
    ck(checks,f'tight_eps{eps}_T{T}',abs(actual-expected)<1e-12,f'{actual} vs {expected}')
wrong_eps=np.abs(p-q).sum(); right_eps=tv(p,q)
ck(checks,'factor_two_mutation_detected',abs(wrong_eps-2*right_eps)<1e-15 and wrong_eps!=right_eps,f'wrong={wrong_eps}, right={right_eps}')
write_result('20','Finite-horizon kernel perturbation accumulation + TV convention boundaries',checks)
