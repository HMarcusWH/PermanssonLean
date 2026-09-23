import numpy as np
from common import ck, write_result
checks=[]; rng=np.random.default_rng(28)
H=np.diag([2.,5.,0.]); ker=np.array([0.,0.,1.]); Pr=np.diag([1.,1.,0.]); Pk=np.diag([0.,0.,1.])
for b in [np.array([1.,2.,0.]),np.array([0.,0.,0.]),np.array([1.,-1.,3.])]:
    solvable=np.linalg.norm(Pk@b)<1e-12
    x=np.linalg.pinv(H)@b
    exact=np.linalg.norm(H@x-b)<1e-10
    ck(checks,'range_kernel_equivalence_'+str(b.tolist()),solvable==exact,f'solvable={solvable}, exact={exact}')
b=np.array([1.,2.,0.]); x0=np.linalg.pinv(H)@b; val=float(x0@b)
for t in [-10,-1,0,2,100]:
    x=x0+t*ker
    ck(checks,f'preimage_response_independent_t{t}',np.allclose(H@x,b) and abs(float(x@b)-val)<1e-12)
for _ in range(50):
    b=rng.normal(size=3); lam=-float(rng.uniform(.01,3))
    R=np.linalg.inv(H-lam*np.eye(3)); lhs=Pk@(R@b); rhs=(1/(-lam))*(Pk@b)
    ck(checks,'kernel_resolvent_pole_'+str(_),np.allclose(lhs,rhs))
b=np.array([1.,2.,3.]); x=np.linalg.pinv(H)@b
ck(checks,'pseudoinverse_not_exact_for_incompatible_source',not np.allclose(H@x,b) and np.allclose(H@x,Pr@b))
write_result('28','Singular kernel/range compatibility',checks,{'canonical_response':val})
