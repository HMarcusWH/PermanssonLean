"""Independent exact TV bound and killed-kernel recurrence receipt checker.

Uses P/U/alpha from separately re-parsed source, not the proposal's
induced-kernel or survival helper.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes,rational_text
from ..engines.robustness import PerturbationProblem,RECEIPT

_KEYS={'format','problem_semantic_identity','baseline_model_identity','alternative_model_identity',
       'joint_states','region_indices','horizon','row_total_variations','maximum_row_tv',
       'initial_law_tv','bound_at_horizon','baseline_survival_rows','alternative_survival_rows',
       'baseline_event_probability','alternative_event_probability','observed_abs_difference',
       'scope','no_long_run_claim','scientific_claims_verified','lean_status','empirical_identification'}

def check_perturbation(problem:PerturbationProblem,receipt:object)->dict:
    if type(receipt) is not dict or set(receipt)!=_KEYS or receipt['format']!=RECEIPT:
        raise AppError('PERTURBATION_RECEIPT','missing/foreign certificate fields')
    b,a=problem.baseline,problem.alternative
    states=[(s,x) for s in b.strategic for x in b.world]
    n=len(states)
    expected={'problem_semantic_identity':problem.identity,'baseline_model_identity':b.semantic_id(),
              'alternative_model_identity':a.semantic_id(),
              'joint_states':[{'strategic':s,'world':x} for s,x in states],
              'region_indices':list(problem.region),'horizon':problem.horizon,
              'scope':'FINITE_PATH_EVENT_TV_COUPLING_BOUND_ONLY',
              'no_long_run_claim':True,'scientific_claims_verified':False,
              'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED'}
    for k,v in expected.items():
        if type(v) is bool:
            if receipt[k] is not v:raise AppError('PERTURBATION_RECEIPT',f'{k} status altered')
        elif receipt[k]!=v:
            raise AppError('PERTURBATION_RECEIPT',f'{k} mismatch')
    def kernel(m):
        K=[]
        for s,x in states:
            row=[]
            for sp,xp in states:
                q=Fraction(0)
                for a in m.feasible[s,x]:
                    q+=m.alpha[s,x][m.actions.index(a)]*m.P[s,x,a][m.world.index(xp)]*m.U[s,x,a,xp][m.strategic.index(sp)]
                row.append(q)
            if sum(row,Fraction(0))!=1:raise AppError('PERTURBATION_RECEIPT','stochastic row failure')
            K.append(row)
        return K
    K,L=kernel(b),kernel(a)
    row_tv=[sum((abs(K[i][j]-L[i][j]) for j in range(n)),Fraction(0))/2 for i in range(n)]
    d=max(row_tv)
    initial=sum((abs(p-q) for p,q in zip(problem.initial_baseline,problem.initial_alternative)),Fraction(0))/2
    bound=min(Fraction(1),initial+problem.horizon*d)
    def table_check(label,matrix):
        values=[Fraction(int(i in problem.region)) for i in range(n)]
        rows=receipt[label+'_survival_rows']
        if type(rows) is not list or len(rows)!=problem.horizon+1:
            raise AppError('PERTURBATION_RECEIPT','survival table height incorrect')
        for h,record in enumerate(rows):
            if type(record) is not list or len(record)!=n or any(type(v) is not str for v in record):
                raise AppError('PERTURBATION_RECEIPT','survival table width/type incorrect')
            actual=[exact_result(x,probability=True) for x in record]
            if actual!=values:raise AppError('PERTURBATION_RECEIPT',f'{label}: false killed survival recurrence at {h}')
            if h!=problem.horizon:
                values=[sum((matrix[i][j]*actual[j] for j in problem.region),Fraction(0)) if i in problem.region else Fraction(0) for i in range(n)]
        return actual
    eb,ea=table_check('baseline',K),table_check('alternative',L)
    pb=sum((v*w for v,w in zip(problem.initial_baseline,eb)),Fraction(0))
    pa=sum((v*w for v,w in zip(problem.initial_alternative,ea)),Fraction(0))
    actual=abs(pb-pa)
    if actual>bound:raise AppError('PERTURBATION_RECEIPT','finite path inequality mathematically false')
    required={'row_total_variations':[rational_text(v) for v in row_tv],
             'maximum_row_tv':rational_text(d),'initial_law_tv':rational_text(initial),
             'bound_at_horizon':rational_text(bound),
             'baseline_event_probability':rational_text(pb),
             'alternative_event_probability':rational_text(pa),
             'observed_abs_difference':rational_text(actual)}
    for key,val in required.items():
        if receipt[key]!=val:raise AppError('PERTURBATION_RECEIPT',f'false {key}')
    return {'format':'Permansson.App.IndependentFinitePerturbationCheck.v1',
            'status':'PASS','horizon':problem.horizon,'checked_joint_states':n,
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED',
            'claim_status':'FINITE_PATH_PERTURBATION_ONLY'}
