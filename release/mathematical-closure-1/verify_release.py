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
        require(source_receipts is not None and approved_manifest is not None,
                "strict release requires authenticated source and approved claim manifests")
        require(d.get("status") == "APPROVED_SOURCE_BOUND",
                "draft PDF/build receipt cannot be approved by a status claim")
        require(d.get("visual_inspection") == "SIGNED_OFF" and
                d.get("independent_review") == "RECEIVED" and
                d.get("source_ci_validation") == "VERIFIED_MAIN",
                "actual reviews, final main CI and PDF inspection missing")
        check_dir = Path(__file__).resolve().parents[2] / "verification/research"
        sys.path.insert(0, str(check_dir))
        from final_closure_verify import strict as verify_mathematical_acceptance
        receipts = json.loads(source_receipts.read_bytes())
        approved = json.loads(approved_manifest.read_bytes())
        result = verify_mathematical_acceptance(
            receipts, "scoped-release-strict", approved)
        require(d.get("source_commit_sha") == result["source"] and
                d.get("source_commit_sha") == approved.get("source_commit_sha"),
                "PDF artifact does not match independently accepted merged source")
        require(sorted(d.get("claims", [])) == sorted(approved.get("claims", [])),
                "rendered paper's actual claims differ from signed inventory")
        require(d.get("pdf_sha256") == sha(out/"Permansson_Mathematical_Closure.pdf"),
                "accepted PDF checksum changed after inspection")
    return {"integrity":"PASS","accepted":False if not strict else True,
            "pdf_pages":d.get("pdf_page_count"),"source_files":len(d["source_tree_files"])}
def main(argv=None):
    ap=argparse.ArgumentParser()
    ap.add_argument("--manifest",required=True,type=Path)
    ap.add_argument("--strict",action="store_true")
    ap.add_argument("--source-receipts",type=Path)
    ap.add_argument("--approved-manifest",type=Path)
    a=ap.parse_args(argv)
    try:print(json.dumps(verify(a.manifest,a.strict,source_receipts=a.source_receipts,approved_manifest=a.approved_manifest),indent=2));return 0
    except (OSError,ValueError,KeyError,zipfile.BadZipFile) as e:
        print("NOT ACCEPTED:",e,file=sys.stderr);return 2
if __name__=="__main__":raise SystemExit(main())
