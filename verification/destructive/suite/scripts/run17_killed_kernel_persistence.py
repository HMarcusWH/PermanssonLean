import numpy as np
from common import ck, write_result
checks=[]
K=np.array([[0.6,0.3,0.1],[0.2,0.5,0.3],[0,0,1.0]])
Q=K[:2,:2]
ones=np.ones(2)
for y in range(2):
    dist=np.zeros(3); dist[y]=1
    for L in range(0,7):
        if L==0:
            brute=1.0
        else:
            pass
        exact=float(np.linalg.matrix_power(Q,L)[y]@ones)
        d=np.zeros(2); d[y]=1
        for _ in range(L): d=d@Q
        brute=float(d.sum())
        ck(checks,f'survival_identity_y{y}_L{L}',abs(brute-exact)<1e-12,f'{brute} vs {exact}')
K2=np.array([[0,1],[0,1]],float); Q2=np.array([[0.0]])
ck(checks,'off_by_one_L0_survival_one',float(np.linalg.matrix_power(Q2,0)[0]@np.ones(1))==1.0)
ck(checks,'off_by_one_L1_survival_zero',float(np.linalg.matrix_power(Q2,1)[0]@np.ones(1))==0.0)
q=min(Q.sum(axis=1))
for L in range(1,8):
    surv=np.linalg.matrix_power(Q,L)@ones
    ck(checks,f'q_lower_bound_L{L}',bool(np.all(surv+1e-12>=q**L)),f'min={surv.min()} q^L={q**L}')
N=np.linalg.inv(np.eye(2)-Q)
mean=N@ones
for y in range(2):
    series=0.0
    for n in range(500): series+=float(np.linalg.matrix_power(Q,n)[y]@ones)
    ck(checks,f'green_exit_time_y{y}',abs(series-mean[y])<1e-10,f'{series} vs {mean[y]}')
Qinv=np.array([[0.7,0.3],[0.1,0.9]])
for L in [1,2,10,50]:
    ck(checks,f'exact_invariance_L{L}',np.allclose(np.linalg.matrix_power(Qinv,L)@ones,ones))
write_result('17','Killed-kernel exact persistence',checks,{'q':q,'mean_exit':mean.tolist()})
