import numpy as np
from common import ck, write_result, normalize
checks=[]
Q=np.array([[0.4,0.4],[0.2,0.5]],float)
vals,vecs=np.linalg.eig(Q.T); j=int(np.argmax(np.real(vals))); theta=float(np.real(vals[j])); mu=np.real(vecs[:,j])
if mu.sum()<0: mu=-mu
mu=normalize(mu)
ck(checks,'unique_qsd_eigenrelation',np.allclose(mu@Q,theta*mu),f'theta={theta}, mu={mu}')
for n in [1,2,5,10]:
    surv=float(mu@np.linalg.matrix_power(Q,n)@np.ones(2))
    cond=mu@np.linalg.matrix_power(Q,n); cond=cond/cond.sum()
    ck(checks,f'qsd_geometric_survival_n{n}',abs(surv-theta**n)<1e-11)
    ck(checks,f'qsd_conditional_stationarity_n{n}',np.allclose(cond,mu))
Qzero=np.array([[0,1],[0,0]],float)
vals=np.linalg.eigvals(Qzero)
ck(checks,'no_positive_qsd_nilpotent',not np.any(np.real(vals)>1e-12),f'eigs={vals}')
theta2=.8; Qmany=theta2*np.eye(3)
for idx,mu2 in enumerate([np.array([1,0,0.]),np.array([0.2,0.3,0.5]),np.array([1/3]*3)]):
    ck(checks,f'many_qsd_sample_{idx}',np.allclose(mu2@Qmany,theta2*mu2))
Qred=np.diag([.9,.8])
for idx,(mu3,th) in enumerate([(np.array([1.,0]),.9),(np.array([0.,1.]),.8)]):
    ck(checks,f'reducible_qsd_{idx}',np.allclose(mu3@Qred,th*mu3))
mu_mix=np.array([.5,.5])
for n in [10,50,200]:
    v=mu_mix@np.linalg.matrix_power(Qred,n); cond=v/v.sum()
    if n==200: ck(checks,'yaglom_selects_dominant_class',cond[0]>.999999,f'cond={cond}')
v=np.array([0.,1.])@np.linalg.matrix_power(Qred,100); cond=v/v.sum()
ck(checks,'yaglom_not_universal_across_initial_laws',np.allclose(cond,[0,1]))
Q_local=np.array([[.9,0.0],[0.0,0.0]])
mu_local=np.array([1.0,0.0]); theta_local=.9
qsd_exists=np.allclose(mu_local@Q_local,theta_local*mu_local)
L=1; eta=.2
survivals=np.linalg.matrix_power(Q_local,L)@np.ones(2)
finite_gate=float(survivals.min()) >= 1-eta
ck(checks,'local_qsd_exists',qsd_exists,f'survivals={survivals}')
ck(checks,'qsd_alone_does_not_imply_uniform_finite_persistence',qsd_exists and not finite_gate,f'inf_survival={survivals.min()} threshold={1-eta}')
qsd_certified = finite_gate and qsd_exists
ck(checks,'qsd_certified_requires_finite_gate',not qsd_certified)
Q_good=np.array([[.9,0.0],[0.0,.85]])
vals2,vecs2=np.linalg.eig(Q_good.T); j2=int(np.argmax(np.real(vals2))); theta_good=float(np.real(vals2[j2])); mu_good=np.real(vecs2[:,j2]);
if mu_good.sum()<0: mu_good=-mu_good
mu_good=normalize(mu_good)
finite_good=float((Q_good@np.ones(2)).min()) >= .8
ck(checks,'qsd_plus_finite_gate_positive_control',finite_good and np.allclose(mu_good@Q_good,theta_good*mu_good),f'theta={theta_good}')
write_result('18','QSD existence/uniqueness/pathology guards + finite-persistence gate',checks,{'theta_unique':theta,'mu_unique':mu.tolist()})
