"""Validate separately acquired main-push checks and publisher evidence, without changing PR records."""
import argparse
from datetime import datetime, timezone
import hashlib,json,re,stat
from pathlib import Path,PurePosixPath
from zipfile import ZipFile

H='92e45179a5e3ecbe1b2bcadc4da54a0d1657f501'
B='37c0cb8f2fbe7934639127e5f8b6d64a01e6950f'
S='d5f2d3a72bda670859c5da87bb173f9eb96696ee'
TREE='d1c01b2812a13b672f164841a7cc4a8ab7dcc778'
T='71cc34fa0bc4b639c05d2ec5f39f0b88afd56388'
A='d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618'
EXPECTED={'build','research','executable-verification','Application contract (ubuntu-latest)','Application contract (windows-latest)','integrity-portability-windows','frozen-source-preservation','release-export-integrity','archive-reproducibility'}
LEGACY={'legacy-build-source-context':('build','Build'),'legacy-research-source-context':('research','Build research library and audit its transitive axioms'),'legacy-executable-source-context':('executable-verification','Install Python dependencies'),'legacy-application-source-context-ubuntu-latest':('Application contract (ubuntu-latest)','Install application-only dependencies'),'legacy-application-source-context-windows-latest':('Application contract (windows-latest)','Install application-only dependencies')}
INTEGRITY={'hardening-preservation-reports','hardening-export-reports','hardening-archive-reports','hardening-windows-portability-reports'}
def need(test,message):
    if not test: raise RuntimeError(message)
def sha(data):return hashlib.sha256(data).hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('--main',required=True);p.add_argument('--directory',type=Path,required=True);args=p.parse_args()
    M=args.main;root=args.directory
    need(re.fullmatch('[0-9a-f]{40}',M),'Full actual M SHA required')
    def load(name):return json.loads((root/name).read_bytes())
    def api(name):return load(name)['response']
    def context(value,run,flat=False):
        expected={'repository':'HMarcusWH/PermanssonLean','pr_number':None,'head_sha':None,'base_sha':None,'checked_sha':M,'checked_tree':TREE,'accepted_release':A,'event':'push','run_id':run,'run_attempt':1,'scope':'canonical_commit_objects'}
        need(all(k in value and value[k]==v for k,v in expected.items()),'Wrong actual main-push context')
        if flat:need(value.get('format')=='Permansson.Hardening.CIContext.v1','Wrong flat source-context envelope')
        need(re.fullmatch('[0-9a-f]{64}',value.get('event_sha256','')),'Missing event digest')
    checks=api('main-checks.json')
    need(checks['total_count']==len(checks['check_runs'])==9 and {c['name'] for c in checks['check_runs']}==EXPECTED,'Nine exact checks required')
    runids=set()
    for c in checks['check_runs']:
        need(c['status']=='completed' and c['conclusion']=='success' and c['head_sha']==M and c['app']['id']==15368,'Failed or wrong-source/publisher main check')
        match=re.fullmatch(r'https://github\.com/HMarcusWH/PermanssonLean/actions/runs/([0-9]+)/job/([0-9]+)',c['details_url'])
        need(match is not None and int(match[2])==c['id'],'Check resource mismatch');runids.add(int(match[1]))
    runs=api('main-runs.json')
    need(runs['total_count']==len(runs['workflow_runs'])==len(runids)==6 and {r['id'] for r in runs['workflow_runs']}==runids,'Six exact main runs required')
    for r in runs['workflow_runs']:
        need(r['event']=='push' and r['head_branch']=='main' and r['head_sha']==M and r['status']=='completed' and r['conclusion']=='success' and r['repository']['full_name']=='HMarcusWH/PermanssonLean','Wrong main run source/result')
    commit=api('main-commit.json')
    need(commit['sha']==M and [p['sha'] for p in commit['parents']]==[B,H] and commit.get('commit',commit)['tree']['sha']==TREE,'Main parent/tree differs from reviewed synthetic')
    jobs=[]
    for run in runids:
        v=api('final-jobs-'+str(run)+'.json');need(v['total_count']==len(v['jobs']),'Incomplete main job page')
        for j in v['jobs']:need(j['head_sha']==M and j['run_id']==run and j['status']=='completed' and j['conclusion']=='success','Wrong main job source/result')
        jobs.extend(v['jobs'])
    need(len(jobs)==9 and {j['id'] for j in jobs}=={c['id'] for c in checks['check_runs']},'Main job/check inventories differ')
    metadata=[];acquisitions=[]
    for run in sorted(runids):
        name='run-'+str(run)+'.json';v=load(name)
        need(v['response']['total_count']==len(v['response']['artifacts']),'Incomplete main artifact page')
        for row in v['response']['artifacts']:
            metadata.append(row)
            if row['name'] in LEGACY:acquisitions.append({'metadata_file':name,'fetched_at':v['fetched_at'],'request_url':v['request_url'],'artifact':row})
    need(len(metadata)==10 and len({a['id'] for a in metadata})==10 and {a['name'] for a in metadata}==INTEGRITY|set(LEGACY)|{'d0-finite-calculation-evidence'},'Ten exact main publisher artifacts required; PR-only C10 prohibited')
    decoded={};raw_members={};records=[];tests=[]
    for a in metadata:
        path=root/(a['name']+'.zip');raw=path.read_bytes()
        need(len(raw)==a['size_in_bytes'] and 'sha256:'+sha(raw)==a['digest'] and a['expired'] is False and a['workflow_run']['head_sha']==M and a['workflow_run']['id'] in runids,'Main artifact publisher size/digest/source differs')
        with ZipFile(path) as z:
            entries=z.infolist();need(0<len(entries)<=32 and len({e.filename for e in entries})==len(entries),'Unsafe main ZIP count')
            values={}
            for e in entries:
                n=e.filename;parts=PurePosixPath(n).parts
                need(parts and not n.startswith('/') and '\\' not in n and ':' not in n and all(x not in ('','.','..') for x in parts) and not e.is_dir() and not e.flag_bits&1 and e.file_size<=2*1024*1024 and stat.S_IFMT(e.external_attr>>16) in (0,stat.S_IFREG),'Unsafe main ZIP member')
                if n.endswith('.json'):values[n]=json.loads(z.read(e))
            decoded[a['name']]=values;raw_members[a['name']]={e.filename for e in entries}
        if a['name'] in INTEGRITY:
            context(values['context.json'],a['workflow_run']['id'],flat=True)
            for name,value in values.items():
                if name=='context.json':continue
                context(value['context'],a['workflow_run']['id']);need(value['status']=='PASS','Main hardening check non-PASS')
                if name.endswith('-tests.json'):
                    need(value['errors']==value['failures']==value['skips']==0 and value['execution_tracked_clean'] is True and all(x['status']=='PASS' for x in value['results']),'Main tests failed/skipped/dirty')
                    tests.append({'artifact':a['name'],'suite':value['suite'],'methods':value['methods_run'],'subtests':value['subtests_run']})
        records.append({'id':a['id'],'name':a['name'],'run_id':a['workflow_run']['id'],'bytes':len(raw),'sha256':sha(raw)})
    expectedmembers={'hardening-preservation-reports':{'context.json','preservation.json','reference-tests.json','preservation-tests.json','context-tests.json','workflow-tests.json'},'hardening-export-reports':{'context.json','tex-export.json','tex-tests.json'},'hardening-archive-reports':{'context.json','archive-tests.json','archive-replay.json'},'hardening-windows-portability-reports':{'context.json','reference-tests.json','preservation-tests.json','tex-tests.json'}}
    for n,e in expectedmembers.items():need(raw_members[n]==e and set(decoded[n])==e,'Main report member inventory differs')
    counts={'reference':17,'preservation':26,'context':6,'workflow':8,'tex':20,'archive':35}
    need(all(r['methods']==counts[r['suite']] for r in tests) and sum(r['methods'] for r in tests if r['artifact']!='hardening-windows-portability-reports')==112 and sum(r['methods'] for r in tests if r['artifact']=='hardening-windows-portability-reports')==63,'Main full test method counts differ')
    preserved=decoded['hardening-preservation-reports']['preservation.json']['details'];need(preserved['protected_count']==369 and preserved['protected_bytes']==6680695,'Main preservation changed')
    tex=decoded['hardening-export-reports']['tex-export.json']['details'];need(tex['actual_size']==71379 and tex['equation_records']==10 and tex['actual_sha256']=='3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416','Main faithful export changed')
    replay=decoded['hardening-archive-reports']['archive-replay.json']['details'];iso=replay['isolation']
    need(iso['network_isolation']=='ENFORCED' and iso['uid']>0 and iso['gid']>0 and iso['supplementary_groups']==[] and iso['capabilities']=='all_zero' and iso['no_new_privileges'] is True and iso['outward_routes']==[] and iso['parent_network_namespace']!=iso['child_network_namespace'] and iso['outward_socket_denied_errno'] in (1,13,101,113),'Main offline enforcement failed')
    need(replay['source_restore']==replay['artifact_replay']=='PASS' and replay['replay_target']==A and replay['counts']=={'refs':36,'input_commits':26,'objects':8202,'legacy_test_methods':29} and all(v['exit_code']==0 for v in replay['legacy']),'Main restoration/replay failed')
    tooling=replay['tooling'];need(tooling['binding']=='canonical_T_C_and_executing_code' and tooling['source_commit']==T and tooling['source_candidate']==M and tooling['files']==35 and tooling['reproduction_instructions_match'] is True and tooling['guide_blob']=='39fda5fa453fc66985c1cf9f227c81eaf4c1ce6f','Main tooling binding differs')
    publication=replay['publication'];need(publication['candidate']==M and publication['scope']=='canonical_candidate_objects' and publication['status']=='PASS' and publication['verified_filesystem_matches_C'] is True and publication['canonical_inner_files']==publication['members']==71 and publication['zip_bytes']==7465148 and publication['zip_sha256']=='f6f119cadb1a3ebe09f9010510476bab2e75194ededde922eb99a8891652eca4','Main canonical publication differs')
    legacy=[]
    for name,(jobname,firstwork) in LEGACY.items():
        need(raw_members[name]=={'required-source.json'} and set(decoded[name])=={'required-source.json'},'Main legacy context payload differs')
        value=decoded[name]['required-source.json'];row=next(x for x in records if x['name']==name);context(value,row['run_id'],flat=True)
        js=[j for j in jobs if j['name']==jobname and j['run_id']==row['run_id']];need(len(js)==1,'Ambiguous main legacy job')
        j=js[0];guard=[s for s in j['steps'] if s['name']=='Bind genuine required-check source'];work=[s for s in j['steps'] if s['name']==firstwork]
        need(len(guard)==len(work)==1 and guard[0]['conclusion']==work[0]['conclusion']=='success' and guard[0]['number']<work[0]['number'],'Main required guard did not precede work')
        legacy.append({'name':name,'job':jobname,'job_id':j['id'],'run_id':row['run_id'],'report':value,'sha256':row['sha256'],'bytes':row['bytes'],'guard_step':guard[0]['number'],'work_step':work[0]['number'],'status':'PASS'})
    research=next(j for j in jobs if j['name']=='research')
    need(api('research-jobs.json')==api('final-jobs-'+str(research['run_id'])+'.json'),'Research duplicate record differs')
    skipnames=['Generate and independently verify C10 release proof evidence','Upload source-bound C10 proof evidence']
    for n in skipnames:
        steps=[s for s in research['steps'] if s['name']==n];need(len(steps)==1 and steps[0]['conclusion']=='skipped','PR-only C10 step not skipped on main')
    (root/'legacy-context-artifacts.json').write_text(json.dumps({'format':'Permansson.LegacyContextArtifactAcquisition.v1','source_main':M,'artifacts':acquisitions},indent=2,sort_keys=True)+'\n',encoding='utf-8')
    (root/'legacy-context-verification.json').write_text(json.dumps({'format':'Permansson.IndependentLegacySourceContextJoin.v1','status':'PASS','source':{'main':M,'tree':TREE,'head':H,'base':B,'synthetic':S},'records':legacy,'limits':['Consistency and execution ordering; no independent publisher authentication']},indent=2,sort_keys=True)+'\n',encoding='utf-8')
    summary={'format':'Permansson.Hardening.MainPushArtifactVerification.v1','status':'PASS','executed_at':datetime.now(timezone.utc).isoformat(),'source':{'main':M,'tree':TREE,'head':H,'base':B,'synthetic':S},'checks':[{'id':c['id'],'name':c['name'],'app_id':c['app']['id'],'status':c['status'],'conclusion':c['conclusion']} for c in checks['check_runs']],'runs':sorted(runids),'artifacts':records,'tests':tests,'isolation':iso,'archive_tooling':tooling,'publication':publication,'legacy_source_contexts':legacy,'c10_main':{'generation':'skipped','upload':'skipped','artifact':'absent','scope':'PR-only current C10 proof preserved in separate frozen premerge packet'},'limits':['Does not constitute GitHub APPROVED review or mathematical peer review','No administrative settings/tag/external publication performed','Copied metadata and hashes provide consistency, not independent publisher authentication']}
    (root/'verification-summary.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    print(json.dumps({'status':'PASS','main':M,'checks':9,'artifacts':10,'linux_methods':112,'windows_methods':63,'offline':'ENFORCED','main_C10':'both_steps_skipped_no_artifact'}))
if __name__=='__main__':main()
