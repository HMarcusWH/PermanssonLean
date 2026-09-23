from pathlib import Path
import subprocess, json, time
from concurrent.futures import ThreadPoolExecutor, as_completed
OLD=Path('/mnt/data/permannson_fullsuite')
ROOT=Path('/mnt/data/Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE')
results_old=json.loads((OLD/'legacy_rerun_results.json').read_text())
paths=[OLD/'runs'/x['script'] for x in results_old]
logdir=ROOT/'logs'/'v016_legacy_postproofread'; logdir.mkdir(parents=True,exist_ok=True)
def one(i,p):
    t=time.time()
    try:
        cp=subprocess.run(['python',p.name],cwd=p.parent,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
        st='PASS' if cp.returncode==0 else 'FAIL'; rc=cp.returncode; out=cp.stdout
    except subprocess.TimeoutExpired as e:
        st='TIMEOUT'; rc=124; out=e.stdout or ''
        if isinstance(out,bytes): out=out.decode(errors='replace')
    dur=time.time()-t
    rel=p.relative_to(OLD/'runs')
    stem=str(rel).replace('/','__')
    (logdir/(stem+'.log')).write_text(out or '',encoding='utf-8',errors='replace')
    return i,{'script':str(rel),'status':st,'rc':rc,'seconds':round(dur,3)}
rows=[None]*len(paths)
with ThreadPoolExecutor(max_workers=24) as ex:
    futs=[ex.submit(one,i,p) for i,p in enumerate(paths)]
    for fut in as_completed(futs):
        i,r=fut.result(); rows[i]=r; print(f"{i+1:02d}/{len(paths)} {r['status']} {r['script']} {r['seconds']}s",flush=True)
(ROOT/'results'/'v016_legacy_python_rerun_postproofread.json').write_text(json.dumps(rows,indent=2))
print('SUMMARY',sum(r['status']=='PASS' for r in rows),'/',len(rows))
raise SystemExit(0 if all(r['status']=='PASS' for r in rows) else 1)
