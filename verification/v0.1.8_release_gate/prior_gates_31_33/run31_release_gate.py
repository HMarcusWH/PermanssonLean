#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, shutil, subprocess, sys, tempfile, zipfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
checks=[]

def ck(name, cond, detail=''):
    checks.append({'name':name,'pass':bool(cond),'detail':str(detail)})

def sha256(p:Path):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1<<20),b''): h.update(b)
    return h.hexdigest()

def run(cmd, cwd=None):
    return subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)

hashes=json.loads((ROOT/'provenance/ARTIFACT_HASHES.json').read_text())
for key in ['paper_pdf','paper_tex','frozen_test_archive']:
    p=ROOT/hashes[key]['path']
    ck(f'{key}_present',p.exists(),p)
    if p.exists(): ck(f'{key}_sha256',sha256(p)==hashes[key]['sha256'],sha256(p))

pdf=ROOT/hashes['paper_pdf']['path']
tex=ROOT/hashes['paper_tex']['path']
frozen=ROOT/hashes['frozen_test_archive']['path']
control=ROOT/'provenance/Permansson_v0.1.7_CONTROL.tex'
ck('v017_control_tex_present',control.exists(),control)
if control.exists(): ck('v017_control_tex_sha256',sha256(control)==hashes['v017_control_tex']['sha256'],sha256(control))

try:
    with zipfile.ZipFile(frozen) as z:
        bad=z.testzip()
    ck('frozen_test_archive_crc',bad is None,bad or 'all entries OK')
except Exception as e: ck('frozen_test_archive_crc',False,e)

sum_path=ROOT/'verification/destructive/POST_PROOFREAD_FULL_SUITE_SUMMARY.json'
summary=json.loads(sum_path.read_text())
ck('historical_85_of_85',summary['v016_historical_script_executions']['passed']==85 and summary['v016_historical_script_executions']['failed']==0,summary['v016_historical_script_executions'])
ck('baseline_16_of_16',summary['v016_baseline_validation']['status']=='PASS' and summary['v016_baseline_validation']['passed']==16,summary['v016_baseline_validation'])
ck('runs_17_30_3240_of_3240',summary['v017_runs_17_30']['passed_checks']==3240 and summary['v017_runs_17_30']['failed_checks']==0,summary['v017_runs_17_30']['passed_checks'])
ck('all_numbered_runs_01_30_green',summary.get('all_numbered_runs_01_30_green') is True,summary.get('all_numbered_runs_01_30_green'))
fresh=json.loads((ROOT/'verification/destructive/V017_RUNS_17_30_FRESH_RERUN_2026-09-23.json').read_text())
ck('fresh_runs_17_30_all_rc0',len(fresh)==14 and all(x.get('rc')==0 for x in fresh),f"{sum(x.get('rc')==0 for x in fresh)}/{len(fresh)}")

t=tex.read_text(encoding='utf-8')
c=control.read_text(encoding='utf-8')
ck('tex_v018_header','v0.1.8' in t and '23 September 2026' in t)
ck('tex_formal_verification_appendix','Appendix D - Formal Verification and Reproducibility' in t)
ck('tex_stale_uniqueness_claim_removed','explicit uniqueness integration remains outside' not in t and 'outside the machine-verified claim boundary' not in t)
ck('tex_section_11_5_noncore','Finite-certificate and rigidity programme (non-core research lane)' in t)
labels=re.findall(r'\\label\{([^}]+)\}',t)
dups=sorted({x for x in labels if labels.count(x)>1})
ck('tex_labels_unique',not dups,dups)
tags_new=re.findall(r'\\tag\{([^}]*)\}',t)
tags_old=re.findall(r'\\tag\{([^}]*)\}',c)
ck('equation_tag_sequence_unchanged',tags_new==tags_old,f'{len(tags_new)} tags')
ck('equation_18a_before_19',t.find(r'\tag{18a}\label{eq:18a}')>=0 and t.find(r'\tag{19}\label{eq:19}')>t.find(r'\tag{18a}\label{eq:18a}'))
ck('no_equation_19a_tag',r'\tag{19a}' not in t)

lean=json.loads((ROOT/'verification/lean/LEAN_CI_EVIDENCE.json').read_text())
commit=lean['formalization_commit']; runid=str(lean['workflow_run_id'])
ck('paper_contains_lean_commit',commit in t,commit)
ck('paper_contains_ci_run',runid in t,runid)
ck('lean_ci_success',lean['run_conclusion']=='success' and lean['job_conclusion']=='success',lean['workflow_url'])
ck('lean_ci_all_required_steps_success',all(x['conclusion']=='success' for x in lean['steps']),lean['steps'])
ck('lean_toolchain_pinned',lean['lean']=='4.34.0' and lean['mathlib']=='v4.34.0',f"Lean {lean['lean']}; mathlib {lean['mathlib']}")

cross=json.loads((ROOT/'verification/lean/LEAN_DECLARATION_CROSSWALK.json').read_text())
ck('lean_crosswalk_commit_match',cross['commit']==commit,cross['commit'])
ck('lean_crosswalk_all_found',cross.get('all_found') is True and all(x.get('found_at_commit') for x in cross['declarations']),f"{sum(x.get('found_at_commit') for x in cross['declarations'])}/{len(cross['declarations'])}")
root_imports=(ROOT/'verification/lean/PermanssonLean_root_imports_snapshot.lean').read_text()
required_modules={
 'PermanssonLean.StrategicWorld.WellPosedness','PermanssonLean.Regime.PolishDescriptor','PermanssonLean.Regime.Persistence',
 'PermanssonLean.Regime.QuasiStationary','PermanssonLean.Regime.Perturbation','PermanssonLean.Regime.UniformPermansson',
 'PermanssonLean.Probability.FinitePrefixTV','PermanssonLean.EGR.RegimeEmbedding','PermanssonLean.EGR.PermanssonTransport',
 'PermanssonLean.Regime.RepresentationEquivalence','PermanssonLean.Regime.FamilyEquivalence','PermanssonLean.Quotient.Preservation',
 'PermanssonLean.Regime.NuisancePadding','PermanssonLean.Examples.PeriodicExactGR'}
missing=[m for m in sorted(required_modules) if f'import {m}' not in root_imports]
ck('lean_crosswalk_modules_root_reachable',not missing,missing)

if shutil.which('pdfinfo'):
    info=run(['pdfinfo',str(pdf)]).stdout
    ck('pdf_31_pages',re.search(r'^Pages:\s+31$',info,re.M) is not None,re.search(r'^Pages:.*$',info,re.M).group(0) if re.search(r'^Pages:.*$',info,re.M) else '')
    ck('pdf_a4',('595.276 x 841.89' in info or '595 x 842' in info),next((x for x in info.splitlines() if x.startswith('Page size:')),''))
    ck('pdf_unencrypted','Encrypted:       no' in info,next((x for x in info.splitlines() if x.startswith('Encrypted:')),''))
else: ck('pdfinfo_available',False,'pdfinfo missing')
if shutil.which('pdftotext'):
    with tempfile.TemporaryDirectory() as td:
        txt=Path(td)/'paper.txt'; run(['pdftotext','-layout',str(pdf),str(txt)])
        ptxt=txt.read_text(errors='replace')
    ck('pdf_v018_text','Working Paper v0.1.8' in ptxt and 'v0.1.8 revised 23 Sep 2026' in ptxt)
    ck('pdf_equation_18a_present','(18a)' in ptxt)
    ck('pdf_stale_19a_absent','(19a)' not in ptxt)
    ck('pdf_formal_appendix_present','Appendix D - Formal Verification and Reproducibility' in ptxt)
else: ck('pdftotext_available',False,'pdftotext missing')

if shutil.which('pdffonts'):
    fonts=run(['pdffonts',str(pdf)]).stdout.splitlines()[2:]
    emb_bad=[]
    for line in fonts:
        parts=line.split()
        if len(parts)>=7:
            tail=parts[-5:]
            if len(tail)>=5 and tail[0]=='no': emb_bad.append(line)
    ck('pdf_fonts_embedded',not emb_bad,emb_bad)

if shutil.which('pdflatex'):
    with tempfile.TemporaryDirectory() as td:
        td=Path(td)
        src=td/tex.name
        shutil.copy2(tex,src)
        cp1=run(['pdflatex','-interaction=nonstopmode','-halt-on-error',src.name],cwd=td)
        cp2=run(['pdflatex','-interaction=nonstopmode','-halt-on-error',src.name],cwd=td) if cp1.returncode==0 else cp1
        built=td/(src.stem+'.pdf')
        ck('cold_tex_compile',cp1.returncode==0 and cp2.returncode==0 and built.exists(),f'pass1={cp1.returncode}, pass2={cp2.returncode}')
        if built.exists() and shutil.which('pdfinfo'):
            binfo=run(['pdfinfo',str(built)]).stdout
            ck('cold_compile_31_pages',re.search(r'^Pages:\s+31$',binfo,re.M) is not None,next((x for x in binfo.splitlines() if x.startswith('Pages:')),''))
        if built.exists() and shutil.which('pdftotext'):
            a=td/'a.txt'; b=td/'b.txt'
            run(['pdftotext','-layout',str(pdf),str(a)])
            run(['pdftotext','-layout',str(built),str(b)])
            ck('cold_compile_text_matches_packaged_pdf',a.read_bytes()==b.read_bytes(),f'{len(a.read_bytes())} vs {len(b.read_bytes())} bytes')
else:
    ck('cold_tex_compile',False,'pdflatex missing')

diff=(ROOT/'provenance/SOURCE_DIFF_v0.1.7_to_v0.1.8.patch').read_text(errors='replace')
ck('source_diff_records_v018','v0.1.8' in diff and 'Formal Verification and Reproducibility' in diff)

passed=sum(c['pass'] for c in checks); total=len(checks); failed=total-passed
result={'run':'31','title':'v0.1.8 final release boarding gate','checks_total':total,'passed':passed,'failed':failed,'checks':checks}
(HERE/'RUN_31_RESULTS.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
lines=['# Run 31 - v0.1.8 final release boarding gate','',f'**Result: {"PASS" if failed==0 else "FAIL"} - {passed}/{total} checks passed.**','']
for x in checks: lines.append(f"- {'PASS' if x['pass'] else 'FAIL'} **{x['name']}** - {x['detail']}")
(HERE/'RUN_31_RELEASE_GATE_REPORT.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
print(json.dumps({'run':31,'passed':passed,'failed':failed,'total':total},indent=2))
sys.exit(1 if failed else 0)
