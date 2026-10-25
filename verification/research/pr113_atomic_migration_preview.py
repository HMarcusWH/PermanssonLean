"""Read-only virtual 30-workflow activation profile for independent review.

No branch, workflow, required check, Git object or authority record is edited.
The preactivation checkout MUST be the original active 25-workflow source.
The program replaces two of those only in an in-memory preview and adds five
explicit staged source blobs. Approval of these bytes must be obtained from an
actual authorized independent security reviewer; this artifact grants none.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from verification.integrity.workflow_contract import APPROVED_WORKFLOWS
from pr113_successor_workflow_profile import audit as old_staged_audit

ROOT = Path(__file__).resolve().parents[2]
OLD = "docs/operations/pr113_unapproved_workflows/manifest.json"
FULL = "docs/operations/pr113_required_gate_replacement_unapproved/full_workflow_manifest.json"
R3 = "docs/operations/pr113_required_gate_replacement_unapproved/manifest.json"
FORMAT = "Permansson.PR113.AtomicWorkflowTransitionReview.v1"
SHA = re.compile(r"^[a-f0-9]{40}$")


class TransitionError(ValueError):
    pass


def need(ok, why):
    if not ok:
        raise TransitionError(why)


def git(*args):
    try:
        data=subprocess.check_output(["git",*args],cwd=ROOT,
            stderr=subprocess.DEVNULL,timeout=30).decode("utf-8")
        # Git blob bytes must be preserved exactly, including final newlines.
        # Only identity-command scalar output is stripped.
        return data if args and args[0]=="show" else data.strip()
    except (OSError,subprocess.CalledProcessError,
            subprocess.TimeoutExpired) as exc:
        raise TransitionError("real Git source unavailable") from exc


def raw(head, path, *, git=git):
    need(isinstance(path,str) and path
         and ".." not in Path(path).parts
         and not Path(path).is_absolute(),
         "invalid Git source path")
    return git("show",head+":"+path).encode("utf-8")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git_blob_oid(blob):
    payload=b"blob "+str(len(blob)).encode()+b"\0"+blob
    return hashlib.sha1(payload).hexdigest()


def preview(head, *, git=git, old_audit=old_staged_audit):
    need(isinstance(head,str) and SHA.fullmatch(head) and
         git("rev-parse","HEAD")==head,
         "virtual activation must bind one real, original preactivation H")
    original=old_audit(head)
    need(original.get("status") ==
         "EXACT_25_PLUS_5_SOURCE_PROFILE_CANDIDATE_NOT_ACTIVATED" and
         original.get("original_workflow_count")==25 and
         original.get("successor_proposal_count")==5,
         "original 25+5 source review profile not valid")
    original_members={}
    for name,hash_value in sorted(APPROVED_WORKFLOWS.items()):
        path=".github/workflows/"+name
        data=raw(head,path,git=git)
        need(digest(data)==hash_value and
             git("rev-parse",head+":"+path)==git_blob_oid(data),
             "original workflow changed before review: "+path)
        original_members[path]={
            "path":path,"sha256":digest(data),"git_blob_oid":git_blob_oid(data),
            "origin":"UNCHANGED_ORIGINAL_25",
        }
    full=json.loads(raw(head,FULL,git=git))
    need(full.get("format")=="Permansson.PR113.FullRequiredWorkflowPreactivation.v1"
         and full.get("status") ==
             "SOURCE_STAGED_NONEXECUTABLE_AWAITING_COMPLETE_SECURITY_REVIEW"
         and full.get("original_workflow_count")==25 and
         full.get("proposed_final_workflow_count")==30 and
         full.get("independent_security_review") is False
         and full.get("owner_activation_authorized") is False
         and full.get("requires_main_PR_and_ordered_merge") is True,
         "full mandatory workflow source has unauthorized status")
    replacements=full.get("full_replacements")
    need(isinstance(replacements,list) and len(replacements)==2,
         "exact two replacement mandatory workflows required")
    old=full.get("old_workflows")
    need(isinstance(old,list) and len(old)==2
         and {x.get("path") for x in old} ==
             {".github/workflows/research-lean.yml",
              ".github/workflows/research-integrity.yml"},
         "original exact two workflow sources not bound")
    for x in old:
        need(x.get("git_blob_oid")==original_members[x["path"]]["git_blob_oid"],
             "old protected original source hash changed")
    plan=dict(original_members)
    for x in replacements:
        need(isinstance(x,dict) and
             set(x) == {"target","staged_source","git_blob_oid",
                        "installed","independent_reviewed"}
             and x.get("target") in {y["path"] for y in old}
             and x.get("installed") is False
             and x.get("independent_reviewed") is False,
             "unauthorized or installed mandatory replacement")
        data=raw(head,x["staged_source"],git=git)
        need(git_blob_oid(data)==x["git_blob_oid"] and
             data.startswith(b"name: ") and
             b"pull_request:\n" in data and
             b"push:\n" in data and
             b"pr113_historical_artifact_delivery.py" in data,
             "reviewed mandatory candidate source byte drift")
        plan[x["target"]]={
            "path":x["target"],"sha256":digest(data),
            "git_blob_oid":git_blob_oid(data),
            "origin":"REVIEW_PENDING_MANDATORY_REPLACEMENT",
            "staged_source":x["staged_source"],
        }
    future=json.loads(raw(head,OLD,git=git))
    proposals=future.get("proposals")
    need(isinstance(proposals,list) and len(proposals)==5
         and future.get("status") ==
           "SOURCE_STAGED_NONEXECUTABLE_PENDING_INDEPENDENT_SECURITY_REVIEW"
         and future.get("owner_authorized_activation") is False
         and future.get("independent_security_review") is False,
         "original staged five workflow approvals not pending")
    for row in proposals:
        dest=row["workflow_path"]
        need(dest not in plan and
             dest.startswith(".github/workflows/pr113-") and
             row.get("approved") is False and
             row.get("installed") is False,
             "unexpected original workflow collision or premature installation")
        source_bytes=raw(head,row["staged_source_path"],git=git)
        need(git_blob_oid(source_bytes)==row["git_blob_oid"],
             "future stage blob differs from original committed source")
        plan[dest]={
            "path":dest,"sha256":digest(source_bytes),
            "git_blob_oid":git_blob_oid(source_bytes),
            "origin":"REVIEW_PENDING_NEW_WORKFLOW",
            "staged_source":row["staged_source_path"],
        }
    need(len(plan)==30 and
         len([p for p in plan.values() if p["origin"]==
             "UNCHANGED_ORIGINAL_25"])==23,
         "virtual workflow source does not include 23+2+5 exact members")
    ordered=[plan[k] for k in sorted(plan)]
    material=json.dumps(ordered,sort_keys=True,separators=(",",":")).encode()
    r3=json.loads(raw(head,R3,git=git))
    need(r3.get("format")=="Permansson.PR113.UnapprovedRequiredGateTransition.v1"
         and len(r3.get("staged_replacements",[]))==2
         and r3.get("owner_activation_authorized") is False
         and r3.get("requires_independent_security_review") is True
         and r3.get("original_T_A2_unmodified") is True,
         "historical original A2 replacement source not reviewed")
    for replacement in r3["staged_replacements"]:
        stage=replacement.get("source")
        materialized=raw(head,stage,git=git)
        need(git_blob_oid(materialized)==replacement.get("git_blob_oid")
             and replacement.get("installed") is False
             and replacement.get("independent_reviewed") is False,
             "original A2/R3 exact source binding absent")
    return {
        "format":FORMAT,
        "status":"EXACT_30_SOURCE_ACTIVATION_PREVIEW_UNAPPROVED",
        "source_head":head,
        "historical_original_workflows":25,
        "historical_preserved_workflows":23,
        "review_pending_mandatory_replacements":2,
        "review_pending_additional_workflows":5,
        "proposed_total_workflows":30,
        "virtual_profile_sha256":digest(material),
        "original_25_plus_5_profile_sha256":original["profile_sha256"],
        "virtual_source_members":ordered,
        "additional_original_test_replacements":[
            {"path":row["target"],
             "source":row["source"],"git_blob_oid":row["git_blob_oid"]}
            for row in r3["staged_replacements"]
        ],
        "historical_T_not_modified":True,
        "historical_A2_not_modified":True,
        "active_workflow_set_modified":False,
        "requires_independent_security_review":True,
        "independent_security_review":False,
        "owner_activation_authorized":False,
        "merge_authorized":False,
        "mathematical_acceptance":False,
        "publication_authorized":False,
    }


def cli(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head",required=True)
    parser.add_argument("--output",required=True,type=Path)
    args=parser.parse_args(argv)
    try:
        out=args.output.absolute()
        need(not out.exists() and not out.is_relative_to(ROOT.resolve())
             and not any(p.is_symlink() for p in out.parents),
             "security review material must be detached and new")
        report=preview(args.head)
        out.parent.mkdir(parents=True,exist_ok=True)
        with out.open("x",encoding="utf-8") as f:
            json.dump(report,f,sort_keys=True,indent=2)
            f.write("\n")
        print(json.dumps({"status":report["status"],
                          "sha256":report["virtual_profile_sha256"],
                          "source_head":report["source_head"]},sort_keys=True))
        return 0
    except (TransitionError,OSError,TypeError,ValueError,KeyError) as exc:
        print("VIRTUAL HISTORICAL MIGRATION NOT REVIEWED:",exc,file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(cli())
