import numpy as np
from common import ck, write_result
checks=[]
x=0.0; F=lambda z:z-1.0
vals=[]
for n in range(1,100): vals.append(F(1/n))
ck(checks,'continuous_strict_failure_eventually_detected',all(v<0 for v in vals[2:]))
F0=lambda z:z
vals=[F0(1/n) for n in range(1,1000)]
ck(checks,'zero_margin_no_strict_transfer',F0(0)==0 and all(v>0 for v in vals))
Fd=lambda z:-1 if z==0 else 1
vals=[Fd(1/n) for n in range(1,1000)]
ck(checks,'continuity_is_necessary',Fd(0)<0 and all(v>0 for v in vals))
target=np.array([1.,-1.,2.,-2.])
for n in [2,5,20,100]:
    raw=target+np.array([1/n,0,0,0])
    corrected=raw-raw.sum()/len(raw)*np.ones(len(raw))
    ck(checks,f'constraint_correction_n{n}',abs(corrected.sum())<1e-12 and np.linalg.norm(corrected-target)<=np.linalg.norm(raw-target)+1e-12)
A2=np.diag([-1.,2.]); x2=np.array([1.,0.]); base=float(x2@A2@x2)
for m in [3,5,10]:
    A=np.diag([-1.,2.]+[3.]*(m-2)); x=np.r_[x2,np.zeros(m-2)]
    ck(checks,f'exact_nesting_preserves_failure_m{m}',abs(float(x@A@x)-base)<1e-12 and float(x@A@x)<0)
A3=np.diag([1.,2.,3.]); x3=np.array([1.,0.,0.])
ck(checks,'broken_nesting_can_erase_failure',base<0 and float(x3@A3@x3)>0)
write_result('26','Persistent finite-detection architecture',checks)
