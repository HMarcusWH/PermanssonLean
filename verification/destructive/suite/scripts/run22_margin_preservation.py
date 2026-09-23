import numpy as np
from common import ck, write_result
checks=[]; rng=np.random.default_rng(17022)
for trial in range(2000):
    a,b=rng.normal(size=2); e0=float(rng.uniform(0,.5)); eJ=float(rng.uniform(0,.5))
    at=a+rng.uniform(-e0,e0); bt=b+rng.uniform(-eJ,eJ)
    D=abs(a-b); Dt=abs(at-bt)
    ck(checks,f'reverse_triangle_{trial}',abs(D-Dt)<=e0+eJ+1e-12)
a=np.array([0.,1.,-2.,4.]); b=np.array([2.,4.,1.,7.]); kappa=float(np.min(np.abs(a-b)))
e0=.2; eJ=.3
at=a+np.array([.2,-.1,.05,-.2]); bt=b+np.array([-.3,.2,-.25,.1])
kt=float(np.min(np.abs(at-bt)))
ck(checks,'uniform_margin_lower_bound',kt+1e-12>=kappa-e0-eJ,f'kappa={kappa}, kt={kt}')
ck(checks,'strict_margin_certifies_positive',kappa>e0+eJ and kt>0)
k=1.0; e0=.4; eJ=.6; a=0.; b=k; at=a+e0; bt=b-eJ
ck(checks,'equality_boundary_can_collapse',abs(at-bt)<1e-12 and k==e0+eJ)
gaps=np.array([1/n for n in range(1,100000)],float)
ck(checks,'pointwise_not_uniform',np.all(gaps>0) and gaps.min()<2e-5)
write_result('22','Constitutive margin-preservation theorem',checks,{'example_kappa':kappa,'example_perturbed_kappa':kt})
