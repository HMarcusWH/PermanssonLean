from pathlib import Path
import subprocess,json,time
OLD=Path('/mnt/data/permannson_fullsuite')
ROOT=Path('/mnt/data/Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE')
prev=json.loads((OLD/'baseline_validation_rerun.json').read_text())
base=OLD/'baseline_validation'; logdir=ROOT/'logs'/'baseline_validation_postproofread'; logdir.mkdir(parents=True,exist_ok=True)
rows=[]
for i,x in enumerate(prev):
    rel=Path(x['script']); p=base/rel; t=time.time()
    if not p.exists():
        rows.append({'script':str(rel),'status':'MISSING','rc':127,'seconds':0}); print('MISSING',rel); continue
    try:
        cp=subprocess.run(['python',p.name],cwd=p.parent,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
        st='PASS' if cp.returncode==0 else 'FAIL'; rc=cp.returncode; out=cp.stdout
    except subprocess.TimeoutExpired as e:
        st='TIMEOUT'; rc=124; out=e.stdout or ''
        if isinstance(out,bytes): out=out.decode(errors='replace')
    dur=time.time()-t
    (logdir/(str(rel).replace('/','__')+'.log')).write_text(out or '',encoding='utf-8',errors='replace')
    rows.append({'script':str(rel),'status':st,'rc':rc,'seconds':round(dur,3)})
    print(f"{i+1:02d}/{len(prev)} {st} {rel} {dur:.2f}s",flush=True)
(ROOT/'results'/'v016_baseline_validation_rerun_postproofread_full.json').write_text(json.dumps(rows,indent=2))
status={'status':'PASS' if len(rows)==16 and all(r['status']=='PASS' for r in rows) else 'FAIL','passed':sum(r['status']=='PASS' for r in rows),'total':len(rows)}
(ROOT/'results'/'v016_baseline_validation_postproofread.json').write_text(json.dumps(status,indent=2))
print('SUMMARY',status)
raise SystemExit(0 if status['status']=='PASS' else 1)
