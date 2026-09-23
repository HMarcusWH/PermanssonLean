from __future__ import annotations
import json, math
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
RESULTS=ROOT/'results'; LOGS=ROOT/'logs'
RESULTS.mkdir(parents=True,exist_ok=True); LOGS.mkdir(parents=True,exist_ok=True)

def tv(p,q):
    p=np.asarray(p,dtype=float); q=np.asarray(q,dtype=float)
    return 0.5*np.abs(p-q).sum()

def normalize(v):
    v=np.asarray(v,dtype=float)
    s=v.sum()
    if s<=0: raise ValueError('nonpositive mass')
    return v/s

def stationary(K):
    K=np.asarray(K,dtype=float)
    vals, vecs=np.linalg.eig(K.T)
    j=int(np.argmin(np.abs(vals-1)))
    v=np.real(vecs[:,j])
    if v.sum()<0: v=-v
    v=np.maximum(v,0)
    return normalize(v)

def path_distribution(K, initial, T):
    '''Distribution on state paths of T transitions: (X0,...,XT).'''
    K=np.asarray(K,float); initial=np.asarray(initial,float); n=len(initial)
    d={ (i,): float(initial[i]) for i in range(n) if initial[i]>0 }
    for _ in range(T):
        nd={}
        for path,p in d.items():
            i=path[-1]
            for j in range(n):
                q=p*K[i,j]
                if q: nd[path+(j,)]=nd.get(path+(j,),0.0)+q
        d=nd
    return d

def tv_dict(a,b):
    keys=set(a)|set(b)
    return 0.5*sum(abs(a.get(k,0)-b.get(k,0)) for k in keys)

def write_result(run_id, title, checks, extra=None):
    data={
        'run':run_id,'title':title,
        'checks_total':len(checks),
        'passed':sum(bool(c.get('pass')) for c in checks),
        'failed':sum(not bool(c.get('pass')) for c in checks),
        'checks':checks,
    }
    if extra: data.update(extra)
    (RESULTS/f'run_{run_id}.json').write_text(json.dumps(data,indent=2,default=float),encoding='utf-8')
    lines=[f"{'PASS' if c.get('pass') else 'FAIL'} {c['name']}: {c.get('detail','')}" for c in checks]
    lines.append(f"\nTOTAL {data['passed']}/{data['checks_total']}")
    (RESULTS/f'run_{run_id}.txt').write_text('\n'.join(lines),encoding='utf-8')
    print(json.dumps({'run':run_id,'passed':data['passed'],'failed':data['failed']},indent=2))
    if data['failed']:
        raise SystemExit(1)
    return data

def ck(checks,name,cond,detail=''):
    checks.append({'name':name,'pass':bool(cond),'detail':detail})
