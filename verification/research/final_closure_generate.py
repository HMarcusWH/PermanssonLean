#!/usr/bin/env python3
"""Produce a scratch current-source candidate audit. NEVER auto-promote a case."""
from __future__ import annotations
import argparse,hashlib,json,subprocess,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
SNAP=ROOT/"research/paper_closures/post_merge_112"

def sha256(path:Path)->str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def root_head():
    try:return subprocess.check_output(["git","rev-parse","HEAD"],
          cwd=ROOT,text=True,timeout=15).strip()
    except (OSError,subprocess.CalledProcessError,subprocess.TimeoutExpired):
        return None

def generate(output:Path)->dict:
    decisions=json.loads((SNAP/"acceptance_decisions.json").read_text())
    cross=json.loads((SNAP/"theorem_crosswalk.json").read_text())
    sources=[]
    for item in cross["closure_additions"]:
        path=ROOT/item["path"]
        sources.append({"id":item["id"],"path":item["path"],
            "source_sha256":sha256(path) if path.is_file() else None,
            "status":"SOURCE_PRESENT_UNREVIEWED" if path.is_file() else "MISSING_SOURCE",
            "axiom_receipts":[],"compiled_head_sha":None})
    record={"format":"Permansson.FinalClosureCandidateObservation.v1",
        "source_head_sha":root_head(),"source_rows":sources,
        "case_count":len(decisions["cases"]),
        "pending_cases":[c["case_id"] for c in decisions["cases"]
                         if c["decision"] not in ("VERIFIED_SELECTED_SCOPE","VERIFIED_NEGATIVE")],
        "trust_boundary":"No acceptance decisions generated from hashes or mere existence.",
        "source_bound_ci":[],"reviews":[],"status":"CANDIDATE_UNREVIEWED"}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(record,indent=2,sort_keys=True)+"\n")
    return record

def main(argv=None):
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",required=True,type=Path)
    args=ap.parse_args(argv)
    report=generate(args.output)
    print(json.dumps({"source":report["source_head_sha"],
       "files_seen":sum(x["source_sha256"] is not None for x in report["source_rows"]),
       "pending":len(report["pending_cases"]),"output":str(args.output)},indent=2))
    return 0
if __name__=="__main__":raise SystemExit(main())
