import datetime
import hashlib
import json
from pathlib import Path
import urllib.request

OUT = Path(__file__).parent / 'hardening-capture'
BASE = 'https://api.github.com/repos/HMarcusWH/PermanssonLean'
index = []

def get(endpoint, name):
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    request = urllib.request.Request(BASE + endpoint, headers={'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28','User-Agent':'Permansson-hardening-readonly'})
    with urllib.request.urlopen(request, timeout=45) as response:
        data = response.read(8*1024*1024+1)
        if len(data)>8*1024*1024:
            raise RuntimeError('Response budget')
        metadata={'path':name,'endpoint':BASE+endpoint,'requested_at':started,'received_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'http_status':response.status,'representation':'raw_http_response_body','sha256':hashlib.sha256(data).hexdigest(),'size':len(data),'headers':{k:v for k,v in response.headers.items() if k.lower() in {'etag','date','x-github-request-id','x-github-api-version-selected'}}}
        if response.headers.get('Link'):
            metadata['link']=response.headers['Link']
    target=OUT/name
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(data)
    index.append(metadata)
    return json.loads(data),metadata

for endpoint,name in [('/pulls/76','pr76.json'),('/issues/comments/6235925253','final-code-review-comment.json'),('/issues/comments/6236142249','acceptance-comment.json'),('/actions/artifacts/12106535829','R-c10-artifact-metadata.json')]:
    get(endpoint,name)
page=1
reviews=[]
while True:
    data,meta=get(f'/pulls/76/reviews?per_page=100&page={page}',f'review-pages/{page}.json')
    reviews.extend(data)
    if not data or len(data)<100:
        break
    page+=1
(OUT/'final-review-submissions.json').write_text(json.dumps(reviews,indent=2)+'\n',encoding='utf-8')
index.append({'path':'final-review-submissions.json','representation':'assembled_paginated_api_json','pages':page,'sha256':hashlib.sha256((OUT/'final-review-submissions.json').read_bytes()).hexdigest()})
runs,meta=get('/actions/runs?head_sha=cdbe7ed5124781be495404122fac1de3315cb6ec&per_page=100','runs/source-head-runs.json')
if runs['total_count']>100:
    raise RuntimeError('More run pages required')
latest={}
for run in runs['workflow_runs']:
    if run['event']=='pull_request':
        latest.setdefault(run['workflow_id'],run)
for run in latest.values():
    run_id=run['id']
    get(f'/actions/runs/{run_id}',f'runs/{run_id}.json')
    jobs,_=get(f'/actions/runs/{run_id}/jobs?per_page=100',f'runs/{run_id}-jobs.json')
    if jobs['total_count']>100:
        raise RuntimeError('More job pages required')
zip_data=(OUT/'R-c10.zip').read_bytes()
if len(zip_data)!=9377 or hashlib.sha256(zip_data).hexdigest()!='75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8':
    raise RuntimeError('R ZIP mismatch')
index.append({'path':'R-c10.zip','endpoint':BASE+'/actions/artifacts/12106535829/zip','representation':'original_publisher_zip_via_GitHub_connector','acquired_on':'2026-10-17','sha256':hashlib.sha256(zip_data).hexdigest(),'size':len(zip_data)})
(OUT/'acquisition-index.json').write_text(json.dumps({'format':'Permansson.Hardening.Acquisition.v1','records':index},sort_keys=True,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'captures':len(index),'final_runs':[{k:r[k] for k in ['id','name','conclusion','head_sha']} for r in latest.values()]}))
