import numpy as np
from common import ck, write_result
checks=[]; rng=np.random.default_rng(25)
for n in range(2,10):
    one=np.ones(n); a=rng.normal(size=n); A=np.outer(one,a)+np.outer(a,one)
    ds=[np.eye(n)[i]-np.eye(n)[0] for i in range(1,n)]
    for i,d in enumerate(ds):
      for j,e in enumerate(ds): ck(checks,f'core_invisible_n{n}_{i}_{j}',abs(d@A@e)<1e-10)
    ck(checks,f'rank_le2_n{n}',np.linalg.matrix_rank(A,tol=1e-10)<=2)
for n in [3,5,8]:
    a=rng.normal(size=n); one=np.ones(n); A=np.outer(one,a)+np.outer(a,one)
    arec=np.diag(A)/2; Arec=np.outer(one,arec)+np.outer(arec,one)
    ck(checks,f'reconstruct_from_diagonal_n{n}',np.allclose(A,Arec))
for n in [2,4,7]:
    c=float(rng.normal()); a=np.full(n,c); one=np.ones(n); A=np.outer(one,a)+np.outer(a,one); delta=2*c
    ck(checks,f'scalar_rank1_collapse_n{n}',np.allclose(A,delta*np.ones((n,n))) and np.linalg.matrix_rank(A if abs(delta)>1e-12 else np.zeros_like(A))<=1)
n=5; a=np.arange(1,n+1,dtype=float); A=np.outer(np.ones(n),a)+np.outer(a,np.ones(n))
ck(checks,'core_agreement_alone_not_scalar',np.linalg.matrix_rank(A)==2 and not np.allclose(np.diag(A),np.diag(A)[0]))
a=np.arange(n,dtype=float); b=np.arange(n,0,-1,dtype=float); A=np.outer(np.ones(n),a)+np.outer(b,np.ones(n)); ds=[np.eye(n)[i]-np.eye(n)[0] for i in range(1,n)]
core=max(abs(d@A@e) for d in ds for e in ds)
ck(checks,'symmetry_is_material',core<1e-10 and not np.allclose(A,A.T))
u=np.array([1,0,0,0,0.]); v=np.array([0,1,0,0,0.]); a=rng.normal(size=n); b=rng.normal(size=n)
A=np.outer(u,a)+np.outer(a,u)+np.outer(v,b)+np.outer(b,v)
ck(checks,'codim2_can_exceed_rank2',np.linalg.matrix_rank(A)>2 and np.linalg.matrix_rank(A)<=4)
write_result('25','Scalar-defect architecture and necessity attacks',checks)
