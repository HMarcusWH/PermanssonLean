import numpy as np
from common import ck, write_result
checks=[]; rng=np.random.default_rng(29)
for trial in range(100):
    n=5; x=rng.normal(size=n); y=rng.normal(size=n); c=float(rng.uniform(.1,3))
    Delta=float(x@x*y@y-(x@y)**2)
    if Delta<1e-8: continue
    w=(x@x)*y-(x@y)*x
    B=c*(np.outer(x,x)-np.outer(y,y))
    lhs=float(w@B@w); rhs=-c*Delta**2
    ck(checks,f'gram_identity_{trial}',abs(lhs-rhs)<=1e-7*max(1,abs(rhs)))
    wh=w/np.linalg.norm(w); margin=c*Delta/(x@x)
    ck(checks,f'normalized_margin_{trial}',abs(float(wh@B@wh)+margin)<1e-8*max(1,margin))
    E=rng.normal(size=(n,n)); E=(E+E.T)/2; op=np.linalg.norm(E,2); E=E*(.5*margin/op)
    ck(checks,f'gram_perturbation_robust_{trial}',float(wh@(B+E)@wh)<0)
A=.8; B=.8; R=1.
ck(checks,'shared_budget_max_valid',max(A,B)<=R)
ck(checks,'shared_budget_sum_not_licensed',A+B>R)
F=lambda t:t*t
h=1e-5; deriv=(F(h)-F(-h))/(2*h); second=(F(h)-2*F(0)+F(-h))/h**2
ck(checks,'zero_first_order_nonzero_second_order',abs(deriv)<1e-10 and second>1.999)
def D(n,m): return n==m
for m in [1,2,10,100]:
    ck(checks,f'pointwise_detector_exists_m{m}',any(D(n,m) for n in range(1,m+2)))
    ck(checks,f'no_tail_completenesses_m{m}',not all(D(n,m) for n in range(m, m+5)))
A0=np.array([[2.,1.],[1.,4.]]); c0=7.; vals,V=np.linalg.eigh(A0); vals2,V2=np.linalg.eigh(A0+c0*np.eye(2))
ck(checks,'scalar_identity_shift_eigenvalues',np.allclose(vals2,vals+c0))
ck(checks,'scalar_identity_shift_eigenvectors',np.allclose(np.abs(V),np.abs(V2)))
write_result('29','Specialized novel-math theorem architectures',checks)
