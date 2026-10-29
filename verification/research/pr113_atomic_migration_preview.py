"""Read-only virtual 30-workflow activation profile for independent review.

No branch, workflow, required check, Git object or authority record is edited.
The preactivation checkout MUST be the original active 25-workflow source.
The program replaces two of those only in an in-memory preview and adds five
explicit staged source blobs. Approval of these bytes must be obtained from an
actual authorized independent security reviewer; this artifact grants none.
"""
from __future__ import annotations
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

# Historical 25-SHA256 workflow authority is resolved lazily from the actual
# pinned Git source. Neither current v2 installed contract nor its namespace
# can supply (or impersonate) the immutable original 25-workflow allowlist.

ROOT = Path(__file__).resolve().parents[2]
OLD = "docs/operations/pr113_unapproved_workflows/manifest.json"
FULL = "docs/operations/pr113_required_gate_replacement_unapproved/full_workflow_manifest.json"
R3 = "docs/operations/pr113_required_gate_replacement_unapproved/manifest.json"
V2_CONTRACT = "docs/operations/pr113_required_gate_replacement_unapproved/workflow_contract_v2_manifest.json"
V2_SUITE = "docs/operations/pr113_required_gate_replacement_unapproved/test_workflow_v2_manifest.json"
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


def preview(head, *, git=git, old_audit=None):
    need(isinstance(head,str) and SHA.fullmatch(head) and
         git("rev-parse","HEAD")==head,
         "virtual activation must bind one real, original preactivation H")
    # Fail closed if someone reuses this PREACTIVATION reviewer on the actual
    # installed-30 tree, even if an injected old audit would claim otherwise.
    active=git("ls-tree","-r","--name-only",head,"--",".github/workflows")
    original_paths=active.splitlines()
    need(len(original_paths)==25
         and len(set(original_paths))==25
         and all(re.fullmatch(r"\.github/workflows/[A-Za-z0-9_.-]+\.ya?ml",p)
                 for p in original_paths),
         "virtual original 25-source preview cannot evaluate installed30")
    from pr113_successor_workflow_profile import (
        audit as authentic_old_audit, authenticated_historical_25,
    )
    if old_audit is None:
        old_audit=authentic_old_audit
    original=old_audit(head)
    need(original.get("status") ==
         "EXACT_25_PLUS_5_SOURCE_PROFILE_CANDIDATE_NOT_ACTIVATED" and
         original.get("original_workflow_count")==25 and
         original.get("successor_proposal_count")==5,
         "original 25+5 source review profile not valid")
    original_members={}
    historical_allowlist=authenticated_historical_25(head)
    need(set(original_paths) ==
         {".github/workflows/"+name for name in historical_allowlist},
         "original 25-workflow membership diverged from frozen Git history")
    for name,hash_value in sorted(historical_allowlist.items()):
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
    # A workflow's self-declared manifest SHA cannot stand in for the real
    # versioned artifact-delivery module's independently committed identity.
    delivery_path="verification/research/pr113_historical_artifact_delivery_v2.py"
    delivery=raw(head,delivery_path,git=git)
    need(git("rev-parse",head+":"+delivery_path)==git_blob_oid(delivery)
         and b'FORMAT = "Permansson.PR113.ExactHistoricalArtifactDelivery.v2"' in delivery
         and b"from pr113_required_dual_gate_v2 import actual_ci_event" in delivery,
         "v2 artifact delivery source absent, substituted or wired to v1 gate")
    # Direct reviewed job entry: v3; original T/A2 delivery+verification is
    # authenticated transitively from the genuine committed runtime source.
    runtime_path="verification/research/pr113_historical_runtime_v3.py"
    runtime=raw(head,runtime_path,git=git)
    need(git("rev-parse",head+":"+runtime_path)==git_blob_oid(runtime)
         and b"from pr113_historical_artifact_delivery_v2 import" in runtime
         and b"from pr113_required_dual_gate_v2 import verify" in runtime
         and b"independent_security_review_authenticated" in runtime,
         "v3 required gate's original reviewed T/A2 dependencies absent")
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
             data.count(b"pr113_historical_runtime_v3.py")==(
                 1 if x["target"].endswith("/research-lean.yml") else 2) and
             b"--producer-run-id" in data and
             b"--security-review-id" in data and
             (b"pr113_regression_diagnostics.py" in data
              if x["target"].endswith("/research-lean.yml")
              else b"--check-existing" in data) and
             b"pr113_historical_artifact_delivery_v2.py" not in data and
             b"pr113_historical_artifact_delivery.py" not in data,
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
    # The authorization surface also changes two canonical integrity Python
    # files. Count and hash those exact source replacements; a reviewed YAML
    # set without the matching CI-06/07 test suite cannot be activated.
    v2_contract=json.loads(raw(head,V2_CONTRACT,git=git))
    v2_tests=json.loads(raw(head,V2_SUITE,git=git))
    need(v2_contract.get("format") ==
             "Permansson.PR113.ReviewPendingVersionedWorkflowContract.v2"
         and v2_contract.get("status") ==
             "EXACT_30_WORKFLOW_GIT_BLOBS_SOURCE_STAGED_NOT_ACTIVE"
         and v2_contract.get("current_original_count")==25
         and v2_contract.get("proposed_active_count")==30
         and v2_contract.get("installed") is False
         and v2_contract.get("independent_security_review") is False
         and v2_contract.get("owner_activation_authorized") is False
         and v2_tests.get("format") ==
             "Permansson.PR113.VersionedWorkflowSuiteCandidate.v2"
         and v2_tests.get("installed") is False
         and v2_tests.get("independent_security_review") is False
         and v2_tests.get("owner_activation_authorized") is False
         and v2_tests.get("original_CI06_CI07_case_mapping_preserved") is True,
         "v2 source contract and mapped workflow tests missing/unreviewed")
    new_integrity = []
    for descriptor, destination, stage, oid in (
        (v2_contract,"verification/integrity/workflow_contract.py",
         "staged_source","staged_git_blob_oid"),
        (v2_tests,"verification/integrity/tests/test_workflow.py",
         "staged_test_source","staged_test_blob_oid"),
    ):
        need(descriptor.get("activation_target",
                            descriptor.get("target_test_path"))==destination,
             "reviewed v2 integrity tooling destination mismatch")
        original_oid=git("rev-parse",head+":"+destination)
        source_path=descriptor.get(stage)
        need(isinstance(source_path,str) and source_path.startswith(
                 "docs/operations/pr113_required_gate_replacement_unapproved/"),
             "reviewed v2 integrity source must remain staged")
        raw_source=raw(head,source_path,git=git)
        need(git_blob_oid(raw_source)==descriptor.get(oid) and
             git_blob_oid(raw_source)!=original_oid,
             "source-pinned v2 integrity verifier source not actually changed")
        new_integrity.append({
            "target":destination,
            "original_git_blob_oid":original_oid,
            "review_pending_git_blob_oid":git_blob_oid(raw_source),
            "staged_source":source_path,
        })
    need(len(new_integrity)==2 and
         len({x["target"] for x in new_integrity})==2,
         "precise two-file historical integrity contract transition missing")
    contract_bytes=raw(head,v2_contract["staged_source"],git=git)
    try:
        syntax=ast.parse(contract_bytes.decode("utf-8"))
        profile_node=next(
            n.value for n in syntax.body if isinstance(n,ast.Assign)
            and any(isinstance(x,ast.Name) and
                    x.id=="APPROVED_WORKFLOW_BLOBS" for x in n.targets))
        profile=ast.literal_eval(profile_node)
    except (SyntaxError,StopIteration,ValueError,UnicodeError) as exc:
        raise TransitionError("versioned workflow allowlist unparseable") from exc
    expected={Path(row["path"]).name:row["git_blob_oid"] for row in ordered}
    need(profile==expected and
         v2_contract.get("expected_workflow_git_blobs")==expected,
         "30-workflow v2 contract pins an unexpected source set")
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
        "review_pending_integrity_tooling_replacements":new_integrity,
        "versioned_workflow_allowlist_count":len(profile),
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
