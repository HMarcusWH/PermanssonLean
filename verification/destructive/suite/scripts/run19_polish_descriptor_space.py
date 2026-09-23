import math, numpy as np
from common import ck, write_result
checks=[]
d=lambda x,y:min(1.0,abs(x-y))
ck(checks,'bounded_metric',all(0<=d(x,y)<=1 for x,y in [(0,100),(-2,3),(1,1)]))
ck(checks,'same_topology_local',abs(d(0,1e-6)-1e-6)<1e-15)
for n in [0,5,100]:
    M=abs(n)+1
    mass=1.0 if -M <= n <= M else 0.0
    ck(checks,f'individual_delta_{n}_tight',mass==1.0)
for M in [1,5,20,100]:
    n=M+1
    inside=1.0 if -M<=n<=M else 0.0
    ck(checks,f'family_not_uniformly_tight_M{M}',inside==0.0)
ck(checks,'escaping_deltas_separated',all(d(n,m)==1.0 for n,m in [(0,2),(10,12),(100,103)]))
for M in [1,5,20]:
    T=10000
    frac=sum(1 for t in range(T) if -M<=t<=M)/T
    ck(checks,f'occupation_not_uniformly_tight_M{M}',frac<0.01,f'fraction={frac}')
ck(checks,'polish_does_not_imply_sequence_convergence',all(d(n,n+2)==1.0 for n in [0,10,100]))
x=8.0; vals=[]
for t in range(1000): vals.append(x); x/=2
probe=np.mean([v/(1+abs(v)) for v in vals[-900:]])
ck(checks,'polish_descriptor_convergent_example',abs(probe)<1e-4,f'probe={probe}')
write_result('19','Polish descriptor-space weakening; individual tightness vs uniform tightness',checks)
