from pathlib import Path
import subprocess, sys, json, time
HERE=Path(__file__).parent; ROOT=HERE.parent; logs=ROOT/'logs'; logs.mkdir(exist_ok=True)
rows=[]
for r in range(17,31):
    matches=sorted(HERE.glob(f'run{r}_*.py'))
    if len(matches)!=1:
        print('missing/ambiguous',r,matches); sys.exit(2)
    p=matches[0]; t=time.time(); cp=subprocess.run([sys.executable,str(p)],cwd=HERE,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    dur=time.time()-t; (logs/f'run_{r}.log').write_text(cp.stdout)
    rows.append({'run':r,'script':p.name,'rc':cp.returncode,'seconds':round(dur,3)})
    print(f"RUN {r}: {'PASS' if cp.returncode==0 else 'FAIL'} {dur:.2f}s {p.name}")
    if cp.returncode!=0:
        print(cp.stdout); break
(ROOT/'results'/'v17_run_summary.json').write_text(json.dumps(rows,indent=2))
if any(x['rc'] for x in rows) or len(rows)!=14: sys.exit(1)
