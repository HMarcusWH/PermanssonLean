#!/usr/bin/env python3
"""Byte and canonical-source validator; no implied scholarly approval."""
from __future__ import annotations
import argparse,hashlib,json,sys,zipfile
from pathlib import Path

def sha(p:Path):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(b,msg):
    if not b: raise ValueError(msg)
def verify(manifest:Path,strict:bool=False):
    d=json.loads(manifest.read_text()); out=manifest.parent
    require(d.get("format")=="Permansson.MathClosure.BuildReceipt.v1","wrong receipt format")
    require(d.get("mode")=="DRAFT","mode mismatch")
    require(d.get("empirical_identification_status")=="NOT_ESTABLISHED","false empirical claim")
    names={"Permansson_Mathematical_Closure.pdf":d["pdf_sha256"],
           "Permansson_Mathematical_Closure.tex":d["tex_sha256"],
           "latex_build.log":d["latex_log_sha256"]}
    for n,h in names.items():require((out/n).exists() and sha(out/n)==h,f"source/output corrupt {n}")
    require((out/"Permansson_Mathematical_Closure.pdf").read_bytes().startswith(b"%PDF-"),"bad PDF")
    zpath=out/"Permansson_Mathematical_Closure_E2E.zip"
    require(zpath.exists(),"missing release archive")
    with zipfile.ZipFile(zpath) as z:
        require(z.testzip() is None,"broken archive")
        for p,h in d["source_tree_files"].items():
            name="manuscript/"+p.partition("mathematical_closure/")[2]
            require(name in z.namelist() and hashlib.sha256(z.read(name)).hexdigest()==h,
                    f"archived source divergence {p}")
    sums=out/"SHA256SUMS.txt";require(sums.is_file(),"missing checksum ledger")
    for line in sums.read_text().splitlines():
        h,p=line.split("  ",1)
        require(sha(out/p)==h,f"checksum mismatch: {p}")
    if strict:
        require(d.get("status")=="APPROVED_SOURCE_BOUND","draft not approved")
        require(d.get("visual_inspection")=="SIGNED_OFF" and
                d.get("independent_review")=="RECEIVED" and
                d.get("source_ci_validation")=="VERIFIED_MAIN",
                "actual reviews or main CI missing")
    return {"integrity":"PASS","accepted":False if not strict else True,
            "pdf_pages":d.get("pdf_page_count"),"source_files":len(d["source_tree_files"])}
def main(argv=None):
    ap=argparse.ArgumentParser()
    ap.add_argument("--manifest",required=True,type=Path)
    ap.add_argument("--strict",action="store_true")
    a=ap.parse_args(argv)
    try:print(json.dumps(verify(a.manifest,a.strict),indent=2));return 0
    except (OSError,ValueError,KeyError,zipfile.BadZipFile) as e:
        print("NOT ACCEPTED:",e,file=sys.stderr);return 2
if __name__=="__main__":raise SystemExit(main())
