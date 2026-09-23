#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, subprocess, tempfile, shutil, sys

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
PROV = ROOT / 'provenance'
GATE = ROOT / 'verification' / 'v0.1.8_release_gate'
PDF = PAPER / 'Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.pdf'
TEX = PAPER / 'Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.tex'
FROZEN = ROOT / 'verification' / 'destructive' / 'Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE_FROZEN.zip'
EXPECTED_PDF = '0fc957f19ac95bd1e3cced5558dc696930cf898714c5cd6dbbc9b928c69663f5'
EXPECTED_TEX = 'a181b5aa1236376134f562a76abbbe090f378d521aa8f33df69f746e5adba71c'
EXPECTED_FROZEN = '7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a'

checks=[]
def add(name, ok, detail=''):
    checks.append({'name':name,'ok':bool(ok),'detail':str(detail)})

def sha(p: Path):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024), b''): h.update(b)
    return h.hexdigest()

def cmd(args, cwd=None):
    p=subprocess.run(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    return p.returncode,p.stdout

add('paper_pdf_present', PDF.is_file(), PDF)
add('paper_tex_present', TEX.is_file(), TEX)
add('paper_pdf_sha256', PDF.is_file() and sha(PDF)==EXPECTED_PDF, sha(PDF) if PDF.is_file() else '')
add('paper_tex_sha256', TEX.is_file() and sha(TEX)==EXPECTED_TEX, sha(TEX) if TEX.is_file() else '')
add('frozen_test_archive_sha256', FROZEN.is_file() and sha(FROZEN)==EXPECTED_FROZEN, sha(FROZEN) if FROZEN.is_file() else '')

tex=TEX.read_text() if TEX.is_file() else ''
for name,needle in [
    ('fig1_joint_state', r'Joint state\\$Y_t=(S_t,X_t)$'),
    ('fig1_action_kernel_signature', r'Action selection\\$\alpha(\cdot\mid S_t,X_t)$'),
    ('fig1_realized_action', r'Realized action\\$A_t$'),
    ('fig1_world_kernel_signature', r'World transition\\$P(\cdot\mid S_t,X_t,A_t)$'),
    ('fig1_update_kernel_signature', r'Strategic update\\$U(\cdot\mid S_t,X_t,A_t,X_{t+1})$'),
    ('fig1_next_joint_state', r'Joint state\\$Y_{t+1}=(S_{t+1},X_{t+1})$'),
    ('fig1_kernel_notation', r'K_{\mathfrak G,P}'),
]: add(name, needle in tex, needle)
add('fig1_old_behavior_label_absent', r'Behavior\\$A_t$' not in tex, '')
add('fig1_single_action_to_world_edge', tex.count(r'\draw[arr] (at.east)--(pw.west);')==1, tex.count(r'\draw[arr] (at.east)--(pw.west);'))

for name,needle in [
    ('fig2_implications_title', 'Persistence implications and QSD certification'),
    ('fig2_finite_gate_label', 'Finite-horizon persistence gate'),
    ('fig2_finite_gate_formula', r'\inf_{y\in B}(K_B^L\mathbf 1_B)(y)\ge 1-\eta'),
    ('fig2_exact_implication', r'implies $(L,0)$-persistence'),
    ('fig2_qsd_certificate', r'\mu_BK_B=\theta_B\mu_B'),
    ('fig2_qsd_guardrail', 'The QSD equation alone does not imply the uniform finite-persistence gate.'),
]: add(name, needle in tex, needle)
add('fig2_old_hierarchy_caption_absent', 'Persistence hierarchy in v0.1.7' not in tex, '')
add('fig2_baked_figure_number_absent', 'Figure 2: Persistence implications and QSD certification' not in tex, '')

add('section_11_5_noncore_boundary', 'non-core' in tex.lower() and '11.5' in tex, '')
add('lean_snapshot_preserved', 'c018f79ea4ce46f4f679ad5bca254509778fc53c' in tex, '')
add('lean_ci_preserved', '35808810682' in tex, '')

alltags=re.findall(r'\\tag\{([^}]+)\}',tex)
add('equation_tag_count_34', len(alltags)==34, len(alltags))
try:
    i18=alltags.index('18a'); i19=alltags.index('19')
    add('equation_18a_before_19', i18<i19, f'{i18}<{i19}')
except ValueError:
    add('equation_18a_before_19', False, alltags)
add('no_equation_19a_tag', '19a' not in alltags, '')

diff=(PROV/'SOURCE_DIFF_v0.1.7_to_v0.1.8.patch').read_text() if (PROV/'SOURCE_DIFF_v0.1.7_to_v0.1.8.patch').exists() else ''
add('source_diff_records_joint_state_figure', 'Y_t=(S_t,X_t)' in diff and 'Realized action' in diff, '')
add('source_diff_records_persistence_gate', 'Finite-horizon persistence gate' in diff and 'implies $(L,0)$-persistence' in diff, '')

r31=(GATE/'RUN_31_RELEASE_GATE_REPORT.md').read_text() if (GATE/'RUN_31_RELEASE_GATE_REPORT.md').exists() else ''
add('run31_preserved', 'PASS - 42/42' in r31, '')

rc,info=cmd(['pdfinfo',str(PDF)])
add('pdfinfo_success', rc==0, rc)
add('pdf_31_pages', 'Pages:           31' in info, next((x for x in info.splitlines() if x.startswith('Pages:')),''))
add('pdf_a4', 'Page size:       595.276 x 841.89 pts (A4)' in info, next((x for x in info.splitlines() if x.startswith('Page size:')),''))
add('pdf_unencrypted', 'Encrypted:       no' in info, next((x for x in info.splitlines() if x.startswith('Encrypted:')),''))
rc,pdftxt=cmd(['pdftotext','-layout',str(PDF),'-'])
add('pdftotext_success', rc==0, rc)
for name,needle in [
    ('pdf_fig1_title','Typed strategic-world process'),
    ('pdf_fig1_realized_action','Realized action'),
    ('pdf_fig2_title','Persistence implications and QSD certification'),
    ('pdf_fig2_finite_gate','Finite-horizon persistence gate'),
    ('pdf_fig2_qsd','QSD-certified quasi-regime'),
]: add(name, needle in pdftxt, needle)

with tempfile.TemporaryDirectory(prefix='permannson_run32_') as td:
    td=Path(td)
    shutil.copy2(TEX,td/'paper.tex')
    rc1,o1=cmd(['pdflatex','-interaction=nonstopmode','-halt-on-error','paper.tex'],cwd=td)
    rc2,o2=cmd(['pdflatex','-interaction=nonstopmode','-halt-on-error','paper.tex'],cwd=td) if rc1==0 else (999,'')
    add('cold_tex_compile', rc1==0 and rc2==0, f'pass1={rc1}, pass2={rc2}')
    log=(td/'paper.log').read_text(errors='ignore') if (td/'paper.log').exists() else ''
    bad=[x for x in ['Overfull \\hbox','Underfull \\hbox','There were undefined references','multiply defined'] if x in log]
    add('cold_compile_no_layout_reference_warnings', not bad, bad)
    if (td/'paper.pdf').exists():
        rc,ci=cmd(['pdfinfo',str(td/'paper.pdf')])
        add('cold_compile_31_pages', 'Pages:           31' in ci, next((x for x in ci.splitlines() if x.startswith('Pages:')),''))
        rc,t1=cmd(['pdftotext','-layout',str(td/'paper.pdf'),'-'])
        rc,t2=cmd(['pdftotext','-layout',str(PDF),'-'])
        add('cold_compile_text_matches_packaged_pdf', t1==t2, f'{len(t1)} vs {len(t2)} chars')
    else:
        add('cold_compile_31_pages',False,'no pdf')
        add('cold_compile_text_matches_packaged_pdf',False,'no pdf')

passed=sum(c['ok'] for c in checks); total=len(checks)
result={'run':32,'name':'v0.1.8 figure-correction and rebuild gate','passed':passed,'total':total,'result':'PASS' if passed==total else 'FAIL','checks':checks}
(GATE/'RUN_32_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# Run 32 - v0.1.8 figure-correction and rebuild gate','',f"**Result: {result['result']} - {passed}/{total} checks passed.**",'']
for c in checks:
    lines.append(f"- {'PASS' if c['ok'] else 'FAIL'} **{c['name']}**" + (f" - {c['detail']}" if c['detail'] else ''))
(GATE/'RUN_32_FIGURE_CORRECTION_GATE_REPORT.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'result':result['result'],'passed':passed,'total':total},indent=2))
sys.exit(0 if passed==total else 1)
