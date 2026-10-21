#!/usr/bin/env python3
"""Byte and canonical-source validator; no implied scholarly approval."""
from __future__ import annotations
import argparse,hashlib,json,sys,zipfile
from pathlib import Path

def sha(p:Path):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(b,msg):
    if not b: raise ValueError(msg)
def verify(manifest:Path,strict:bool=False,*,source_receipts:Path|None=None,approved_manifest:Path|None=None):
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
        raise ValueError("draft artifact cannot be approved; use --approved-seal and genuine external review")
    return {"integrity":"PASS","accepted":False if not strict else True,
            "pdf_pages":d.get("pdf_page_count"),"source_files":len(d["source_tree_files"])}
def main(argv=None):
    ap=argparse.ArgumentParser()
    ap.add_argument("--manifest",required=True,type=Path)
    ap.add_argument("--strict",action="store_true")
    ap.add_argument("--source-receipts",type=Path)
    ap.add_argument("--approved-manifest",type=Path)
    ap.add_argument("--approved-seal",type=Path,
                    help="immutable approved ZIP, independently source/PDF authenticated")
    ap.add_argument("--bundle",type=Path)
    a=ap.parse_args(argv)
    try:
        if a.approved_seal:
            require(a.source_receipts and a.approved_manifest and a.bundle,
                    "approved verification requires detached source/review and diagnostic bundle")
            from seal_approved import verify_approved_archive
            checkdir=Path(__file__).resolve().parents[2]/"verification/research"
            sys.path.insert(0,str(checkdir))
            from final_closure_verify import strict as strict_closure
            # The approved seal cannot rely solely on a cached green flag.
            approved=json.loads(a.approved_manifest.read_bytes())
            receipts=json.loads(a.source_receipts.read_bytes())
            with zipfile.ZipFile(a.approved_seal) as z:
                seal=json.loads(z.read("approved_seal.json"))
            verify_approved_archive(a.approved_seal,seal)
            outcome=strict_closure(receipts,"scoped-release-strict",approved,
                                   bundle_path=a.bundle)
            require(seal["source_commit_sha"]==outcome["source"] and
                    seal["head_sha"]==outcome["frozen_head"] and
                    seal["pdf_sha256"]==approved["pdf_sha256"] and
                    seal["pdf_pages"]==approved["pdf_pages"] and
                    seal["claims"]==approved["claims"],
                    "sealed reviewed claims or PDF source does not match live authentication")
            print(json.dumps({"integrity":"PASS","accepted":True,
                              "source":outcome["source"],"scope":"SCOPED_ONLY"},indent=2))
            return 0
        print(json.dumps(verify(a.manifest,a.strict,
              source_receipts=a.source_receipts,
              approved_manifest=a.approved_manifest),indent=2))
        return 0
    except (OSError,ValueError,KeyError,zipfile.BadZipFile) as e:
        print("NOT ACCEPTED:",e,file=sys.stderr);return 2
if __name__=="__main__":raise SystemExit(main())
