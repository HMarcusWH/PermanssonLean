"""Review-only P1-05 exact-H trigger migration; never change active CI.

The original 4+9+8 producer jobs exist, but path-filtered push events are not
guaranteed at frozen H, and manual dispatch of a workflow absent on the
default branch is not a reliable substitute. Retain all original jobs and
change only the branch-scoped push trigger after independent security review.

This program cannot attest independent approval or run any required check.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[2]
MANIFEST="docs/operations/pr113_unapproved_workflows/trigger_candidates/manifest.json"
SHA40=re.compile(r"^[a-f0-9]{40}$")
TRIGGER="on:\n  push:\n    branches: [research/final-mathematical-closure]\n  workflow_dispatch:"
PRODUCER_IDS={
    "pr113-all-case-compiler.yml":"compiler-shard",
    "pr113-all-original-semantic-candidates.yml":"semantic-candidate-shard",
    "pr113-legacy-semantic-evidence.yml":"legacy-original-shard",
}
SHARD_COUNT={
    "pr113-all-case-compiler.yml":4,
    "pr113-all-original-semantic-candidates.yml":9,
    "pr113-legacy-semantic-evidence.yml":8,
}
class TriggerReviewError(ValueError):pass

def demand(ok,reason):
    if not ok:raise TriggerReviewError(reason)

def git(*args):
    try:
        proc=subprocess.run(["git", *args],cwd=ROOT,
                            timeout=35,capture_output=True,check=False)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise TriggerReviewError("Git source unavailable") from exc
    demand(proc.returncode==0 and len(proc.stdout)<4*1024*1024,
           "real Git source object missing")
    return proc.stdout

def committed(head,path):
    demand(isinstance(path,str) and
           (path.startswith(".github/workflows/") or
            path.startswith("docs/operations/pr113_unapproved_workflows/")) and
           ".." not in Path(path).parts and "\\" not in path,
           "untrusted original or proposed CI path")
    return git("show",head+":"+path)

def digest(value):return hashlib.sha256(value).hexdigest()
def blob_oid(value):
    return hashlib.sha1(b"blob "+str(len(value)).encode()+b"\0"+value).hexdigest()

def revised(original):
    """Strict original bytes transformation, never a YAML reformatter."""
    demand(type(original) is bytes and len(original)<1_000_000,
           "invalid original source-controlled workflow")
    try:src=original.decode("utf-8")
    except UnicodeError as exc:raise TriggerReviewError("invalid UTF-8") from exc
    begin=src.find("on:\n")
    end=src.find("  workflow_dispatch:",begin)
    demand(begin>=0 and end>begin and src.count("on:\n")==1
           and src.count("  workflow_dispatch:")==1
           and "    paths:" in src[begin:end]
           and "research/final-mathematical-closure" in src[begin:end]
           and src[:begin].startswith("name: PR113 "),
           "unknown original workflow trigger format")
    return (src[:begin]+TRIGGER+src[end+len("  workflow_dispatch:"):]).encode()

def validate_proposals(head,data,read=committed):
    demand(isinstance(head,str) and SHA40.fullmatch(head) and
           isinstance(data,dict) and
           data.get("format")=="Permansson.PR113.StagedFullProducerTriggerReview.v1" and
           data.get("status")=="REVIEW_PENDING__ACTIVE_WORKFLOWS_UNCHANGED" and
           data.get("original_requested_producer_jobs")==21 and
           data.get("independent_security_review") is False and
           data.get("owner_approved_installation") is False and
           data.get("mathematical_acceptance") is False and
           data.get("publication_authorized") is False and
           isinstance(data.get("proposals"),list) and len(data["proposals"])==3,
           "candidate source contract claimed approval or lost original shards")
    seen=set();rows=[]
    for row in data["proposals"]:
        demand(isinstance(row,dict) and
               set(row)=={"active","proposal","original_blob","proposed_blob",
                           "producer_shards","expected_job"},
               "invalid protected workflow proposal member")
        old,new=row["active"],row["proposal"]
        name=Path(old).name
        demand(name in PRODUCER_IDS and
               old==".github/workflows/"+name and
               new=="docs/operations/pr113_unapproved_workflows/trigger_candidates/"+name and
               name not in seen and
               row["expected_job"]==PRODUCER_IDS[name] and
               type(row["producer_shards"]) is int and
               row["producer_shards"]==SHARD_COUNT[name] and
               all(isinstance(row[key],str) and SHA40.fullmatch(row[key])
                   for key in ("original_blob","proposed_blob")),
               "foreign original job, replay shard or byte identity")
        seen.add(name)
        original=read(head,old)
        candidate=read(head,new)
        demand(blob_oid(original)==row["original_blob"] and
               blob_oid(candidate)==row["proposed_blob"],
               "staged or active producer blob differs from pinned review object")
        demand(candidate==revised(original),
               "candidate CI differs from active source beyond approved trigger patch")
        demand(("  "+PRODUCER_IDS[name]+":").encode() in candidate,
               "original producing job removed")
        shard=("        shard: ["+
               ", ".join(str(i) for i in range(SHARD_COUNT[name]))+
               "]").encode()
        demand(shard in candidate and
               ("--shard-count "+str(SHARD_COUNT[name])).encode() in candidate,
               "original shard matrix/count changed")
        rows.append({
            "workflow":old,"staged_candidate":new,
            "old_source_sha256":digest(original),
            "new_source_sha256":digest(candidate),
            "producer_job":PRODUCER_IDS[name],
            "original_shard_count":SHARD_COUNT[name],
            "reviewed":False,"installed":False,
        })
    demand(seen==set(PRODUCER_IDS),"original producer workflow family missing")
    return {
        "format":"Permansson.PR113.TriggerCandidateAudit.v1",
        "status":"THREE_BYTE_EXACT_CANDIDATES_SECURITY_REVIEW_PENDING",
        "source_head":head,
        "original_shard_count":sum(SHARD_COUNT.values()),
        "original_producing_workflow_count":3,
        "active_files_unchanged":True,
        "proposed":rows,
        "independent_security_review":False,
        "installed":False,
        "accepted_controls":0,
        "publication_authorized":False,
    }

def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--head",required=True)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args(argv)
    try:
        demand(git("rev-parse","HEAD").decode().strip()==a.head,
               "checkout differs from requested exact H")
        target=a.out.absolute()
        demand(not target.exists() and
               not any(p.is_symlink() for p in (target,*target.parents)) and
               not target.is_relative_to(ROOT.resolve()),
               "review output must be a fresh detached nonsymlinked source path")
        result=validate_proposals(a.head,json.loads(committed(a.head,MANIFEST)))
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
        print(json.dumps({"status":result["status"],
                          "original_shards":result["original_shard_count"]}))
        return 0
    except (TriggerReviewError,OSError,ValueError,KeyError,TypeError) as exc:
        print("PR113 ALL-SHARD CI TRIGGER REVIEW BLOCKED:",exc,file=sys.stderr)
        return 2

if __name__=="__main__":raise SystemExit(main())
