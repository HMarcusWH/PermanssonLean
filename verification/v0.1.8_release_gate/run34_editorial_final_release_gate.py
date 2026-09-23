#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, tempfile, shutil, sys, zipfile
ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT/'paper'
GATE = ROOT/'verification'/'v0.1.8_release_gate'
PDF = PAPER/'Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.pdf'
TEX = PAPER/'Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.tex'
FROZEN = ROOT/'verification'/'destructive'/'Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE_FROZEN.zip'
PORTABLE = ROOT/'verification'/'destructive'/'Permansson_TestSuite_v0.1.7_WINDOWS_SAFE.zip'
CONTROL = ROOT/'provenance'/'Permansson_v0.1.7_CONTROL.tex'
EXPECTED_PDF='24f7dd43c8996b6fc8bedf708704969ba2124e159783bbd2ded45db61525df54'
EXPECTED_TEX='8235f6140bca33e7e3f0e96b4fd3aa2431c476fbdaf7c5d86d6d0b703ea54ed9'
EXPECTED_FROZEN='7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a'
EXPECTED_PORTABLE='864e2fec88b345194b0a9dc4ce9431e6a9a754eb88adea75fb8835b6244f41c3'
checks=[]
def add(name,ok,detail=''): checks.append({'name':name,'ok':bool(ok),'detail':str(detail)})
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
 return h.hexdigest()
def cmd(a,cwd=None):
 p=subprocess.run(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 return p.returncode,p.stdout

for name,p,exp in [('paper_pdf',PDF,EXPECTED_PDF),('paper_tex',TEX,EXPECTED_TEX),('frozen_suite',FROZEN,EXPECTED_FROZEN),('portable_suite',PORTABLE,EXPECTED_PORTABLE)]:
 add(name+'_present',p.is_file(),p)
 add(name+'_sha256',p.is_file() and sha(p)==exp, sha(p) if p.is_file() else '')

tex=TEX.read_text() if TEX.is_file() else ''
body=tex.split(r'\section{17. Appendix D - Formal Verification and Reproducibility}',1)[0]
appd=tex.split(r'\section{17. Appendix D - Formal Verification and Reproducibility}',1)[1] if r'\section{17. Appendix D - Formal Verification and Reproducibility}' in tex else ''

for name,pat in [
 ('main_no_version_017',r'Version 0\.1\.7'),('main_no_version_018',r'Version 0\.1\.8'),
 ('main_no_v017_narrative',r'v0\.1\.7'),('main_no_release_gate',r'release gate'),
 ('main_no_control_lineage',r'control lineage'),('main_no_nonpromotion',r'non-promotion'),
 ('main_no_research_lane',r'non-core research lane'),('main_no_promotion_rule',r'Promotion rule'),
 ('main_no_section_11_5',r'Section 11\.5')]:
 add(name,re.search(pat,body,re.I) is None,'')
add('appendix_d_present', r'\section{17. Appendix D - Formal Verification and Reproducibility}' in tex,'')
add('revision_lineage_in_appendix_d', 'Revision and artifact lineage' in appd,'')
add('tool_disclosure_in_appendix_d', 'Tool use and author responsibility' in appd,'')
add('appendix_e_present', 'Appendix E - Specialized Finite-Certificate and Rigidity Extensions' in tex,'')
add('appendix_e_scope_condition', 'Scope condition.' in tex,'')
add('old_section_11_5_heading_absent', '11.5 Finite-certificate and rigidity programme' not in tex,'')

add('lean_snapshot_present','c018f79ea4ce46f4f679ad5bca254509778fc53c' in tex,'')
add('lean_ci_present','35808810682' in tex,'')
add('lean_crosswalk_present','Paper-to-Lean crosswalk' in tex,'')

tags=re.findall(r'\\tag\{([^}]+)\}',tex)
ctags=re.findall(r'\\tag\{([^}]+)\}',CONTROL.read_text() if CONTROL.exists() else '')
add('equation_tag_count_34',len(tags)==34,len(tags))
add('equation_tag_sequence_matches_v017',tags==ctags,f'{len(tags)} vs {len(ctags)}')
add('equation_18a_before_19',tags.index('18a')<tags.index('19') if '18a' in tags and '19' in tags else False,tags)
add('no_equation_19a_tag','19a' not in tags,'')
add('labels_unique', len(re.findall(r'\\label\{[^}]+\}',tex))==len(set(re.findall(r'\\label\{([^}]+)\}',tex))), '')
add('theorem_count_6',tex.count(r'\textbf{Theorem ')==6,tex.count(r'\textbf{Theorem '))
add('proposition_count_9',tex.count(r'\textbf{Proposition ')==9,tex.count(r'\textbf{Proposition '))
add('corollary_count_3',tex.count(r'\textbf{Corollary ')==3,tex.count(r'\textbf{Corollary '))

for name,needle in [
 ('fig1_joint_state',r'Joint state\\$Y_t=(S_t,X_t)$'),('fig1_action_kernel',r'Action selection\\$\alpha(\cdot\mid S_t,X_t)$'),
 ('fig1_world_kernel',r'World transition\\$P(\cdot\mid S_t,X_t,A_t)$'),('fig1_update_kernel',r'Strategic update\\$U(\cdot\mid S_t,X_t,A_t,X_{t+1})$'),
 ('fig3_finite_gate','Finite-horizon persistence gate'),('fig3_qsd',r'\mu_BK_B=\theta_B\mu_B'),('fig3_finite_L',r'for every finite $L$')]:
 add(name,needle in tex,needle)

rc,info=cmd(['pdfinfo',str(PDF)]); add('pdfinfo_success',rc==0,rc)
add('pdf_30_pages','Pages:           30' in info,next((x for x in info.splitlines() if x.startswith('Pages:')),''))
add('pdf_a4','Page size:       595.276 x 841.89 pts (A4)' in info,next((x for x in info.splitlines() if x.startswith('Page size:')),''))
add('pdf_unencrypted','Encrypted:       no' in info,next((x for x in info.splitlines() if x.startswith('Encrypted:')),''))
rc,pdftxt=cmd(['pdftotext','-layout',str(PDF),'-']); add('pdftotext_success',rc==0,rc)
for name,needle in [('pdf_title','Permansson Regimes: A General Framework for'),('pdf_appendix_d','Appendix D - Formal Verification and Reproducibility'),('pdf_appendix_e','Appendix E - Specialized Finite-Certificate and Rigidity Extensions')]: add(name,needle in pdftxt,needle)

with tempfile.TemporaryDirectory(prefix='permannson_run34_') as td:
 td=Path(td); shutil.copy2(TEX,td/'paper.tex')
 rc1,o1=cmd(['pdflatex','-interaction=nonstopmode','-halt-on-error','paper.tex'],cwd=td)
 rc2,o2=cmd(['pdflatex','-interaction=nonstopmode','-halt-on-error','paper.tex'],cwd=td) if rc1==0 else (999,'')
 add('cold_tex_compile',rc1==0 and rc2==0,f'pass1={rc1}, pass2={rc2}')
 log=(td/'paper.log').read_text(errors='ignore') if (td/'paper.log').exists() else ''
 bad=[x for x in ['Overfull \\hbox','Underfull \\hbox','There were undefined references','multiply defined'] if x in log]
 add('cold_compile_no_layout_reference_warnings',not bad,bad)
 if (td/'paper.pdf').exists():
  rc,ci=cmd(['pdfinfo',str(td/'paper.pdf')]); add('cold_compile_30_pages','Pages:           30' in ci,next((x for x in ci.splitlines() if x.startswith('Pages:')),''))
  _,t1=cmd(['pdftotext','-layout',str(td/'paper.pdf'),'-']); _,t2=cmd(['pdftotext','-layout',str(PDF),'-']); add('cold_compile_text_matches_packaged_pdf',t1==t2,f'{len(t1)} vs {len(t2)} chars')
 else:
  add('cold_compile_30_pages',False,'no pdf'); add('cold_compile_text_matches_packaged_pdf',False,'no pdf')

for name,p in [('frozen_zip_integrity',FROZEN),('portable_zip_integrity',PORTABLE)]:
 try:
  with zipfile.ZipFile(p) as z: bad=z.testzip()
  add(name,bad is None,bad or '')
 except Exception as e: add(name,False,e)

prior=GATE/'prior_gates_31_33'
for run,needle in [(31,'PASS - 42/42'),(32,'PASS - 45/45'),(33,'PASS - 50/50')]:
 matches=list(prior.glob(f'RUN_{run}_*REPORT.md'))
 txt=matches[0].read_text() if matches else ''
 add(f'prior_run{run}_preserved',needle in txt,matches[0] if matches else 'missing')

passed=sum(c['ok'] for c in checks); total=len(checks)
result={'run':34,'name':'v0.1.8 editorial-final release gate','passed':passed,'total':total,'result':'PASS' if passed==total else 'FAIL','checks':checks}
(GATE/'RUN_34_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# Run 34 - v0.1.8 editorial-final release gate','',f"**Result: {result['result']} - {passed}/{total} checks passed.**",'']
for c in checks: lines.append(f"- {'PASS' if c['ok'] else 'FAIL'} **{c['name']}**"+(f" - {c['detail']}" if c['detail'] else ''))
(GATE/'RUN_34_EDITORIAL_FINAL_RELEASE_GATE_REPORT.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'result':result['result'],'passed':passed,'total':total},indent=2))
sys.exit(0 if passed==total else 1)
