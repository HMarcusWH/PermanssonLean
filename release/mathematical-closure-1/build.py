#!/usr/bin/env python3
"""Reproducible draft PDF/TeX/manifest build; no source release or approval."""
from __future__ import annotations
import argparse, hashlib, json, os, shutil, subprocess, sys, zipfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
PAPER=ROOT/"research_papers/mathematical_closure"
RELEASE=ROOT/"release/mathematical-closure-1"
SRC=["README.md","main.tex","preamble.tex","references.bib",
     *[f"sections/{x}" for x in (
      "01_scope_and_semantics.tex","02_existing_foundations.tex",
      "03_discounted_original_margin.tex","04_measurable_multiagent_recovery.tex",
      "05_nonlinear_occupation.tex","06_counterexamples_and_limits.tex",
      "07_formal_verification.tex")],
     "appendices/A_theorem_crosswalk.tex","appendices/B_reproducibility.tex"]

def sha(data: bytes)->str: return hashlib.sha256(data).hexdigest()
def run(cmd,cwd,env=None):
    p=subprocess.run(cmd,cwd=cwd,env=env,check=False,capture_output=True,text=True,timeout=420)
    if p.returncode: raise RuntimeError(f"{cmd}: {p.returncode}\n{(p.stdout+p.stderr)[-7000:]}")
    return p.stdout+"\n"+p.stderr
def git_head():
    try:return run(["git","rev-parse","HEAD"],ROOT).strip()
    except (OSError,RuntimeError):return None

def build(out:Path,engine:str,render:bool)->dict:
    if out.resolve().is_relative_to(ROOT.resolve()):
        raise ValueError("use an out-of-repository output directory")
    for f in SRC:
        if not (PAPER/f).is_file(): raise ValueError(f"missing manuscript source {f}")
    compiler=shutil.which(engine)
    if not compiler: raise ValueError(f"TeX compiler unavailable: {engine}")
    out.mkdir(parents=True,exist_ok=True)
    work=out/"_texwork"; work.mkdir(exist_ok=True)
    env=os.environ.copy()
    # Bind timestamps to the authentic source commit, not wall-clock build time.
    source_date_epoch=run(["git","show","-s","--format=%ct","HEAD"],ROOT).strip()
    if not source_date_epoch.isdigit():
        raise ValueError("authentic source commit epoch unavailable")
    env["SOURCE_DATE_EPOCH"]=source_date_epoch
    env["FORCE_SOURCE_DATE"]="1"
    env["TZ"]="UTC"
    env["LC_ALL"]="C"
    env["TEXINPUTS"]=str(PAPER)+os.pathsep+env.get("TEXINPUTS","")
    env["BIBINPUTS"]=str(PAPER)+os.pathsep+env.get("BIBINPUTS","")
    cmd=[compiler,"-halt-on-error","-interaction=nonstopmode","-file-line-error",
         f"-output-directory={work}","main.tex"]
    logs=[run(cmd,PAPER,env)]
    if shutil.which("bibtex"): logs.append(run(["bibtex","main"],work,env))
    logs += [run(cmd,PAPER,env),run(cmd,PAPER,env)]
    # The original LaTeX log contains transient output-root paths; preserve
    # diagnostics while replacing only those root locations deterministically.
    raw_merged="\n".join(logs)
    # Retain a literal, non-published diagnostic transcript in each detached
    # output root. It is NOT the hashed/scientific manuscript build receipt.
    (out/"latex_build.raw.log").write_text(raw_merged)
    normalized=raw_merged
    for actual,label in ((str(work.resolve()),"<TEX_WORK>"),
                         (str(out.resolve()),"<OUTPUT_ROOT>"),
                         (str(PAPER.resolve()),"<MANUSCRIPT_ROOT>")):
        normalized=normalized.replace(actual,label)
    (out/"latex_build.log").write_text(normalized)
    pdf=work/"main.pdf"
    if not pdf.is_file() or not pdf.read_bytes().startswith(b"%PDF-"):
        raise RuntimeError("no valid PDF from TeX")
    shutil.copyfile(pdf,out/"Permansson_Mathematical_Closure.pdf")
    shutil.copyfile(PAPER/"main.tex",out/"Permansson_Mathematical_Closure.tex")
    pages=None
    if shutil.which("pdfinfo"):
        for line in run(["pdfinfo",str(pdf)],out).splitlines():
            if line.startswith("Pages:"): pages=int(line.partition(":")[2].strip())
    if render:
        if not shutil.which("pdftoppm"):raise RuntimeError("pdftoppm unavailable")
        (out/"pages").mkdir(exist_ok=True)
        run(["pdftoppm","-png","-r","100",str(pdf),"page"],out/"pages")
    sources={f"research_papers/mathematical_closure/{p}":sha((PAPER/p).read_bytes())
             for p in SRC}
    m=json.loads((RELEASE/"manifest.json").read_text())
    data={"format":"Permansson.MathClosure.BuildReceipt.v1","status":"DRAFT_NOT_ACCEPTED",
          "mode":"DRAFT","source_commit_sha":git_head(),
          "source_date_epoch":source_date_epoch,"source_tree_files":sources,
          "pdf_sha256":sha((out/"Permansson_Mathematical_Closure.pdf").read_bytes()),
          "tex_sha256":sha((out/"Permansson_Mathematical_Closure.tex").read_bytes()),
          "latex_log_sha256":sha((out/"latex_build.log").read_bytes()),
          "manifest_source_sha256":sha((RELEASE/"manifest.json").read_bytes()),
          "pdf_page_count":pages,"compiler":engine,
          "compiler_version":run([compiler,"--version"],PAPER).splitlines()[0],
          "visual_inspection":"NOT_PERFORMED","independent_review":"NOT_RECEIVED",
          "source_ci_validation":"NOT_BOUND_TO_MERGED_MAIN","claims":m["claims"],
          "empirical_identification_status":"NOT_ESTABLISHED"}
    (out/"manifest.lock.json").write_text(json.dumps(data,sort_keys=True,indent=2)+"\n")
    (out/"source_ci_receipts.lock.json").write_text(json.dumps(
        {"status":"MISSING_POST_MERGE_SOURCE_AND_REVIEWS","ci_receipts":[],
         "independent_reviews":[]},indent=2)+"\n")
    members={"manuscript/"+p:(PAPER/p).read_bytes() for p in SRC}
    members.update({p:(out/p).read_bytes() for p in
        ("Permansson_Mathematical_Closure.pdf","Permansson_Mathematical_Closure.tex",
         "manifest.lock.json","source_ci_receipts.lock.json","latex_build.log")})
    archive=out/"Permansson_Mathematical_Closure_E2E.zip"
    with zipfile.ZipFile(archive,"w") as z:
        for name,payload in sorted(members.items()):
            entry=zipfile.ZipInfo(name,(1980,1,1,0,0,0))
            entry.compress_type=zipfile.ZIP_DEFLATED
            entry.external_attr=0o100644<<16
            z.writestr(entry,payload,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    names=["Permansson_Mathematical_Closure.pdf",
           "Permansson_Mathematical_Closure.tex","manifest.lock.json",
           "source_ci_receipts.lock.json","Permansson_Mathematical_Closure_E2E.zip"]
    (out/"SHA256SUMS.txt").write_text(
        "".join(f"{sha((out/p).read_bytes())}  {p}\n" for p in names))
    return {"status":data["status"],"pdf_pages":pages,"archive":str(archive)}

def main(argv=None):
    ap=argparse.ArgumentParser()
    ap.add_argument("--mode",choices=["draft"],default="draft")
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--engine",choices=["pdflatex","xelatex","lualatex"],default="pdflatex")
    ap.add_argument("--render",action="store_true")
    args=ap.parse_args(argv)
    try: print(json.dumps(build(args.out,args.engine,args.render),indent=2));return 0
    except (RuntimeError,ValueError,OSError,subprocess.TimeoutExpired) as e:
        print("BUILD BLOCKED:",e,file=sys.stderr);return 2
if __name__=="__main__":raise SystemExit(main())
