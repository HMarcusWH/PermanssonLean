import numpy as np, math
from common import ck, write_result, tv, path_distribution, tv_dict
checks=[]
for delta in [1e-1,1e-2,1e-4,1e-6]:
    K=np.array([[1,0],[delta,1-delta]],float)
    L=np.array([[1-delta,delta],[0,1]],float)
    row=max(tv(K[i],L[i]) for i in range(2))
    statdist=tv([1,0],[0,1])
    ck(checks,f'small_kernel_big_stationary_delta{delta}',row<=delta+1e-15 and statdist==1.0,f'row={row}, statTV={statdist}')
for e in [1e-2,1e-6,1e-10]:
    p=np.array([.5+e/2,.5-e/2]); q=np.array([.5-e/2,.5+e/2])
    psi=lambda r: 1 if r[0]>.5 else 0
    ck(checks,f'discontinuous_psi_flip_{e}',tv(p,q)<=e+1e-15 and psi(p)!=psi(q),f'TV={tv(p,q)}')
p=.50; q=.51
prev=0
for T in [1,5,20,100,500]:
    probs_p=[]; probs_q=[]
    for k in range(T+1):
        c=math.comb(T,k); probs_p.append(c*p**k*(1-p)**(T-k)); probs_q.append(c*q**k*(1-q)**(T-k))
    cur=tv(probs_p,probs_q)
    ck(checks,f'bernoulli_path_tv_monotone_T{T}',cur+1e-12>=prev,f'{cur} >= {prev}')
    prev=cur
ck(checks,'bernoulli_long_horizon_material_divergence',prev>0.17,f'TV500={prev}')
write_result('21','Infinite-horizon robustness failure modes',checks,{'bernoulli_T500_TV':prev})
