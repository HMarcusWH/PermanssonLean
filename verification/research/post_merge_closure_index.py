"""Strict, additive PR79 source/CI evidence index verification.

This verifies byte-bound source/receipt claims against an available local Git object
store, and validates archived run metadata. It deliberately cannot reauthenticate
unavailable GitHub job logs, reviewer approval, or empirical identification.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from typing import Callable

BASE = '39279799834ae536bda715dedecdc11a32bf6c82'
HEAD = 'a1f1a77a301178e33412595265e823a873fb7301'
SYNTHETIC = 'fa0441227aa8b245b384b01b32f3bfb43a897f07'
MERGE = '674c1b557d99ab080afb65a797a99cb5840eab62'
TREE = 'b391f32f503f07bcfd7b29d8c24c1f9ad61eb19f'
TRUSTED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
PATH = 'research/paper_closures/post_merge_79'
FILE_NAMES = ('source_ci_index.json', 'receipt_normalization.json', 'acceptance_decisions.json')
REFS = {'B':BASE, 'H':HEAD, 'S':SYNTHETIC, 'M':MERGE}
HEX64 = re.compile(r'^[0-9a-f]{64}$')
HEX40 = re.compile(r'^[0-9a-f]{40}$')

class EvidenceError(ValueError): pass


def need(condition: bool, what: str) -> None:
    if not condition: raise EvidenceError(what)


def strict_json(raw: bytes) -> dict:
    def distinct(pairs):
        out = {}
        for k,v in pairs:
            need(k not in out, f'duplicate JSON key: {k}')
            out[k]=v
        return out
    obj=json.loads(raw, object_pairs_hook=distinct,
                   parse_constant=lambda x: (_ for _ in ()).throw(EvidenceError(f'nonfinite JSON: {x}')))
    need(isinstance(obj, dict), 'index top level must be object')
    return obj


def read_bundle(repo: Path) -> tuple[dict, dict, dict]:
    return tuple(strict_json((repo/PATH/n).read_bytes()) for n in FILE_NAMES)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def old_newline_variant(raw: bytes, variant: str) -> bytes:
    if variant=='RAW': return raw
    need(b'\r' not in raw and raw.endswith(b'\n'), f'cannot map {variant} on noncanonical source')
    if variant=='CRLF': return raw.replace(b'\n',b'\r\n')
    if variant=='LF_FINAL_CRLF': return raw[:-1]+b'\r\n'
    if variant=='LF_FINAL_TWO_CRLF':
        need(raw.count(b'\n')>=2,'no two final LF to convert')
        parts=raw.rsplit(b'\n',2)
        return b'\r\n'.join(parts)
    raise EvidenceError(f'unrecognized newline class: {variant}')


def git_object(repo: Path, selector: str) -> bytes:
    r=subprocess.run(['git','cat-file','-p',selector],cwd=repo,capture_output=True,check=False,timeout=45)
    if r.returncode: raise EvidenceError(f'Git object missing {selector}: {r.stderr.decode("utf-8","replace")[:280]}')
    return r.stdout


def verify_index(index: dict, norms: dict, decisions: dict,
                 *, source_reader: Callable[[str],bytes]|None = None,
                 commit_reader: Callable[[str],bytes]|None = None) -> dict:
    for obj,label,fmt in ((index,'source index','Permansson.PostPR79.SourceCIIndex.v1'),
                          (norms,'normalization','Permansson.PostPR79.ReceiptNormalization.v1'),
                          (decisions,'decisions','Permansson.PostPR79.AcceptanceDecisions.v1')):
        need(obj.get('format')==fmt,f'{label} format drift')
        need(all(obj['reference'].get(k)==v for k,v in REFS.items()),f'{label} B/H/S/M mismatch')
        need(obj['reference'].get('tree',obj['reference'].get('tree_H_S_M'))==TREE,
             f'{label} source tree mismatch')
    ref=index['reference']
    need(ref.get('S_parent_order')==['B','H'] and ref.get('M_parent_order')==['B','H'], 'incorrect merge parent order')
    need(index.get('contract_count')==42 and len(index.get('contracts',[]))==42,'not 42 contracts')
    ids=[x['id'] for x in index['contracts']]
    need(len(set(ids))==42 and 'A2-P02' in ids,'contract set duplicate or omitted')
    need(sum(index['contract_dispositions'].values())==42,'contract status census mismatch')
    need(index.get('review_status','').startswith('NO_SUBMITTED_REVIEW'),'review falsely promoted')
    need('UNVERIFIED' in index.get('claimed_17_check_679_reference_census',''),'unsupported census promoted')
    need(index['CI']['Research_PR79_declarations']==10443 and index['CI']['Research_PR79_test_methods']==918,'historic audit counters drift')
    need(set(index['CI']['axiom_allowlist'])==TRUSTED_AXIOMS,'axiom allowlist changed')
    for k,sha,n in (('PR79_source_head',HEAD,10),('merged_main',MERGE,6)):
        runs=index['CI'][k]
        need(len(runs)==n and len({x['id'] for x in runs})==n,f'{k} count or duplicate')
        for x in runs:
            need(x['head_sha']==sha and x['conclusion']=='success', f'{k} wrong source/conclusion')
            need(x['run_url']==f'https://github.com/HMarcusWH/PermanssonLean/actions/runs/{x["id"]}',f'{k} wrong run URL')
    for k,n in (('local_audit_archived_job_logs',22),('locally_verified_downloaded_GitHub_artifact_ZIPs',6)):
        rows=index['CI'][k]
        need(len(rows)==n and len({tuple(sorted(x.items())) for x in rows})==n,f'{k} duplicate or missing')
        for x in rows:
            need(HEX64.fullmatch(x['sha256']) is not None and type(x['bytes']) is int and x['bytes']>0,f'{k} digest invalid')
    need(norms['count']==256 and len(norms['records'])==256,'owner receipt census missing')
    need(norms['counts']=={'RAW':234,'CRLF':4,'LF_FINAL_CRLF':16,'LF_FINAL_TWO_CRLF':1,'UNRESOLVED':1},'owner classifications changed')
    need(norms['status'].startswith('HISTORICAL_MISMATCH_DISCLOSED'), 'missing owner-source warning')
    disp=norms['historical_mismatch_disposition']
    need(disp['source']=='PermanssonResearch/EconomicWitness/ConstitutionCore.lean', 'wrong retired source')
    need(disp['status']=='RETIRED_UNRECONCILED_OWNER_RECEIPT_BINDING','unresolved digest promoted')
    for k in ('canonical_sha256','published_sha256'):
        need(HEX64.fullmatch(disp[k]) is not None,f'invalid owner hash {k}')
    need(disp['canonical_sha256']!=disp['published_sha256'],'unresolved binding magically identical')
    need(decisions['case_count']==45 and len(decisions['cases'])==45,'not 45 cases')
    need(decisions['full_selected_programme_accepted'] is False,'false full acceptance')
    need(decisions['unverified_owner_digest_retired_from_authority'] is True,'owner digest promotion')
    need(decisions['retired_owner_historical_digest']==disp['published_sha256'],'retired digest mismatch')
    cids=[x['id'] for x in decisions['cases']]
    need(len(set(cids))==45,'duplicate acceptance case')
    pending=[x['id'] for x in decisions['cases'] if x['acceptance_decision'].startswith('PENDING_')]
    need(pending==decisions['pending_ids'] and pending,'pending case missing or suppressed')
    need(all(x['source_head']==HEAD and x['required_for_full_acceptance'] for x in decisions['cases']),'case source or required flag drift')
    need({aid for x in index['contracts'] for aid in x['acceptance_ids']}==set(cids), 'contract acceptance routing not exact')
    need(all(HEX64.fullmatch(x['canonical_sha256']) and HEX64.fullmatch(x['published_sha256']) for x in norms['records']), 'bad source digest')
    for x in norms['records']:
        need(x['classification'] in norms['counts'], 'unknown normalization class')
        if x['classification']=='UNRESOLVED':
            need(x['source']==disp['source'] and x['published_sha256']==disp['published_sha256'], 'wrong unresolved row')
        else:
            if x['classification']=='RAW': need(x['canonical_sha256']==x['published_sha256'],'false RAW identity')
            else: need(x['canonical_sha256']!=x['published_sha256'],'unnecessary newline mapping')
    source_checked=0
    if source_reader:
        cache={}
        def source(path):
            if path not in cache:
                need(isinstance(path,str) and path.startswith(('PermanssonResearch/','verification/research/','research/paper_closures/spec/')) and path.endswith(('.lean','.py','.json')) and '..' not in path and '\\' not in path and not path.startswith('/'), 'unsafe source path')
                cache[path]=source_reader(path)
            return cache[path]
        for record in norms['records']:
            src=source(record['source'])
            need(digest(src)==record['canonical_sha256'],f'canonical Git source mismatch: {record["source"]}')
            if record['classification']!='UNRESOLVED':
                variant=old_newline_variant(src,record['classification'])
                need(digest(variant)==record['published_sha256'],f'newline normalization mismatch: {record["source"]}')
            source_checked+=1
        for contract in index['contracts']:
            for declaration in contract['declarations']:
                src=source(declaration['path'])
                target=declaration['source_sha256']
                need(any(digest(old_newline_variant(src,v))==target for v in ('RAW','CRLF','LF_FINAL_CRLF','LF_FINAL_TWO_CRLF') if (v=='RAW' or (b'\r' not in src and src.endswith(b'\n') and (v!='LF_FINAL_TWO_CRLF' or src.count(b'\n')>=2)))), f'wrong declaration source: {declaration["declaration"]}')
                line=declaration['line']
                need(type(line) is int and 1<=line<=len(src.splitlines()),f'bad declaration locator: {declaration["declaration"]}')
    if commit_reader:
        raw=commit_reader(MERGE).decode('utf-8','strict')
        need('tree '+TREE+'\n' in raw, 'merged tree mismatch')
        need(raw.count('parent ')==2 and ('parent '+BASE+'\nparent '+HEAD+'\n') in raw,'merged parent order mismatch')
        # This packet indexes original historic S; the local Git clone may not retain
        # synthetic PR merge refs. S is not implicitly "verified" by an absent commit.
    return {'contracts':42,'acceptance_cases':45,'pending_cases':pending,
            'owner_records':256,'source_rows_checked':source_checked,
            'source_tree':TREE,'source_head':HEAD,'merge_commit':MERGE,
            'historical_synthetic_merge_locally_rechecked':False,
            'release_ready':False}


def release_gate(report: dict) -> None:
    if not report['release_ready'] or report['pending_cases']:
        raise EvidenceError('RELEASE BLOCKED: pending semantic fixtures / unresolved historical review acceptance')


def main() -> None:
    p=argparse.ArgumentParser()
    p.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[2])
    p.add_argument('--release-gate',action='store_true')
    p.add_argument('--skip-git',action='store_true',help='Only for isolated data-unit tests; not a source certificate')
    args=p.parse_args()
    vals=read_bundle(args.repo)
    reader=(lambda path:git_object(args.repo,f'{MERGE}:{path}')) if not args.skip_git else None
    committer=(lambda sha:git_object(args.repo,sha)) if not args.skip_git else None
    result=verify_index(*vals,source_reader=reader,commit_reader=committer)
    print(json.dumps(result,indent=2,sort_keys=True))
    if args.release_gate: release_gate(result)

if __name__=='__main__': main()
