import numpy as np
from common import ck, write_result
checks=[]; rng=np.random.default_rng(27)
for trial in range(50):
    m=3; R=rng.normal(size=(m,m)); H=R.T@R + .1*np.eye(m); b=rng.normal(size=m); c=-abs(float(rng.normal()))-.2
    A=np.block([[H,b[:,None]],[b[None,:],np.array([[c]])]])
    ev=np.linalg.eigvalsh(A); neg=ev[0]
    ck(checks,f'predecessor_good_{trial}',np.linalg.eigvalsh(H).min()>0)
    ck(checks,f'successor_bad_{trial}',neg<0)
    lam=float(neg)
    F=c-lam-b@np.linalg.solve(H-lam*np.eye(m),b)
    ck(checks,f'secular_equivalence_{trial}',abs(F)<1e-8,f'lambda={lam}, F={F}')
H=np.eye(2); B=np.array([[1.,0.],[0.,1.]]); C=np.array([[-2.,.3],[.3,.5]])
A=np.block([[H,B],[B.T,C]])
lam=float(np.linalg.eigvalsh(A)[0])
S=C-lam*np.eye(2)-B.T@np.linalg.solve(H-lam*np.eye(2),B)
ck(checks,'r2_schur_determinant_zero',abs(np.linalg.det(S))<1e-8)
ck(checks,'r2_not_one_scalar_coordinate',abs(S[0,0])>1e-4 or abs(S[1,1])>1e-4,f'S={S}')
Hbad=np.diag([-1.,2.]); A=np.block([[Hbad,np.zeros((2,1))],[np.zeros((1,2)),np.array([[3.]])]])
ck(checks,'minimality_is_material',np.linalg.eigvalsh(Hbad).min()<0 and np.linalg.eigvalsh(A).min()<0)
write_result('27','First-bad quotient and Schur reduction',checks)
