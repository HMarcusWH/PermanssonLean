from pathlib import Path
import subprocess,json,time,sys
from concurrent.futures import ThreadPoolExecutor,as_completed
start=int(sys.argv[1]); end=int(sys.argv[2])
OLD=Path('/mnt/data/permannson_fullsuite'); ROOT=Path('/mnt/data/Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE')
allold=json.loads((OLD/'legacy_rerun_results.json').read_text()); subset=allold[start:end]
logdir=ROOT/'logs'/'v016_legacy_postproofread'; logdir.mkdir(parents=True,exist_ok=True)
def one(local_i,x):
    p=OLD/'runs'/x['script']; t=time.time()
    try:
        cp=subprocess.run(['python',p.name],cwd=p.parent,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
        st='PASS' if cp.returncode==0 else 'FAIL'; rc=cp.returncode; out=cp.stdout
    except subprocess.TimeoutExpired as e:
        st='TIMEOUT'; rc=124; out=e.stdout or ''
        if isinstance(out,bytes): out=out.decode(errors='replace')
    dur=time.time()-t; rel=p.relative_to(OLD/'runs')
    (logdir/(str(rel).replace('/','__')+'.log')).write_text(out or '',encoding='utf-8',errors='replace')
    return local_i,{'script':str(rel),'status':st,'rc':rc,'seconds':round(dur,3)}
rows=[None]*len(subset)
with ThreadPoolExecutor(max_workers=4) as ex:
    futs=[ex.submit(one,i,x) for i,x in enumerate(subset)]
    for f in as_completed(futs):
        i,r=f.result(); rows[i]=r; print(f"{start+i+1:02d}/85 {r['status']} {r['script']} {r['seconds']}s",flush=True)
out=ROOT/'results'/f'v016_legacy_chunk_{start}_{end}.json'; out.write_text(json.dumps(rows,indent=2))
print('SUMMARY',sum(r['status']=='PASS' for r in rows),'/',len(rows))
raise SystemExit(0 if all(r['status']=='PASS' for r in rows) else 1)
