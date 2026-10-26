"""PR113 fully detached 25->30 workflow candidate rehearsal. NOT activation.

Construct one disposable exact-source Git commit from a real current H. Install
ONLY the two reviewed workflow replacements, five reviewed additions, and
three exact versioned verification source replacements. Exercise both actual
H-like checkout and a true ordered [B113,C] synthetic commit with equal tree.
All worktrees are removed. No branch, ruleset, reviewer or required CI changed.

This is an engineering SOURCE rehearsal, not old-T archive restoration, full
A2 compiler execution, external reviewer acceptance, merge or publication.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from pr113_workflow_profile_v2 import (
    audit as workflow_audit, PREACTIVATION_HEAD, STAGE, PROPOSALS,
    FULL_MANIFEST, PROPOSAL_MANIFEST, CONTRACT,
)
from pr113_tooling_migration_v2 import audit as tooling_audit
from pr113_a2_successor_identity_v2 import audit as a2_audit, PR113_BASE

# Executable checkouts must remain free of untracked import bytecode.
sys.dont_write_bytecode = True

ROOT=Path(__file__).resolve().parents[2]
FORMAT="Permansson.PR113.DisposableSourceTransitionRehearsal.v1"
SHA=re.compile(r"^[0-9a-f]{40}$")
SOURCE_REPLACEMENTS={
    "verification/integrity/workflow_contract.py":CONTRACT,
    "verification/integrity/tests/test_workflow.py":
        STAGE+"test_workflow_v2.py",
    "verification/research/test_localized_prefix_compiler.py":
        STAGE+"test_localized_prefix_compiler.py",
}


class RehearsalError(ValueError):
    pass


def need(ok, reason):
    if not ok:
        raise RehearsalError(reason)


def run(repo, *args, input_bytes=None, seconds=180, author=False):
    cmd=["git","-C",str(repo)]
    if author:
        cmd+=["-c","user.name=PR113 Ephemeral Source Rehearsal",
              "-c","user.email=pr113-rehearsal@invalid.example",
              "-c","commit.gpgsign=false"]
    env=os.environ.copy()
    env["GIT_TERMINAL_PROMPT"]="0"
    env["GIT_AUTHOR_NAME"]="PR113 Ephemeral Source Rehearsal"
    env["GIT_AUTHOR_EMAIL"]="pr113-rehearsal@invalid.example"
    env["GIT_COMMITTER_NAME"]="PR113 Ephemeral Source Rehearsal"
    env["GIT_COMMITTER_EMAIL"]="pr113-rehearsal@invalid.example"
    try:
        cp=subprocess.run(cmd+list(args),input=input_bytes,
                          capture_output=True,env=env,timeout=seconds)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise RehearsalError("disposable Git operation unavailable") from exc
    if cp.returncode!=0:
        raise RehearsalError(
            "disposable Git operation failed "+
            repr(args[:4])+": "+cp.stderr.decode("utf-8","replace")[-1600:])
    return cp.stdout


def scalar(root,*args):
    return run(root,*args).decode("utf-8").strip()


def object_bytes(root,commit,path):
    need(isinstance(path,str) and path and
         not path.startswith("/") and "\\" not in path and
         ".." not in path.split("/"),
         "unsafe candidate Git path")
    raw=run(root,"show",commit+":"+path)
    oid=scalar(root,"rev-parse",commit+":"+path)
    computed=hashlib.sha1(
        b"blob "+str(len(raw)).encode("ascii")+b"\0"+raw).hexdigest()
    need(oid==computed,
         "source content and exact Git blob object disagree: "+path)
    return oid,raw


def safe_json(root,head,path):
    _,raw=object_bytes(root,head,path)
    try:
        data=json.loads(raw)
    except (UnicodeError,ValueError) as exc:
        raise RehearsalError("invalid exact committed staged manifest") from exc
    need(isinstance(data,dict),"candidate manifest must be JSON object")
    return data


def original_source(root,head):
    need(isinstance(head,str) and SHA.fullmatch(head),
         "actual target H must be an exact Git object ID")
    checked=scalar(root,"rev-parse","HEAD")
    need(scalar(root,"cat-file","-t",head)=="commit",
         "candidate H is not an actual Git commit")
    if checked!=head:
        need(scalar(root,"show","-s","--format=%P",checked).split()==
             [PR113_BASE,head],
             "source checkout must be exact H or real ordered [B113,H]")
        need(scalar(root,"rev-parse",checked+"^{tree}")==
             scalar(root,"rev-parse",head+"^{tree}"),
             "incoming synthetic source checkout differs from H tree")
    need(not run(root,"status","--porcelain=v1","--untracked-files=all"),
         "source repository is dirty before detached rehearsal")
    run(root,"merge-base","--is-ancestor",PREACTIVATION_HEAD,head)
    return checked


def planned_sources(root,head):
    full=safe_json(root,head,FULL_MANIFEST)
    other=safe_json(root,head,PROPOSAL_MANIFEST)
    required=full.get("full_replacements")
    added=other.get("proposals")
    need(isinstance(required,list) and len(required)==2
         and isinstance(added,list) and len(added)==5
         and full.get("independent_security_review") is False
         and full.get("owner_activation_authorized") is False
         and other.get("independent_security_review") is False
         and other.get("owner_authorized_activation") is False,
         "candidate source asks for premature installation or approval")
    mapping={}
    for row in required:
        need(row.get("installed") is False and
             row.get("independent_reviewed") is False,
             "replaced workflow has fabricated installation/review state")
        target=row.get("target")
        stage=row.get("staged_source")
        need(isinstance(target,str) and
             target.startswith(".github/workflows/") and
             isinstance(stage,str) and stage.startswith(STAGE)
             and target not in mapping,
             "invalid replacement workflow source")
        mapping[target]=(stage,row.get("git_blob_oid"))
    for row in added:
        need(row.get("installed") is False and
             row.get("approved") is False,
             "new workflow has fabricated installation/approval state")
        target=row.get("workflow_path")
        stage=row.get("staged_source_path")
        need(isinstance(target,str) and
             target.startswith(".github/workflows/pr113-") and
             isinstance(stage,str) and stage.startswith(PROPOSALS)
             and target not in mapping,
             "invalid addition workflow source")
        mapping[target]=(stage,row.get("git_blob_oid"))
    for destination,source in SOURCE_REPLACEMENTS.items():
        need(destination not in mapping,"candidate source destination collision")
        oid,_=object_bytes(root,head,source)
        mapping[destination]=(source,oid)
    need(len(mapping)==10,
         "disposable source requires exact seven workflows and three guards")
    for destination,(stage,oid) in mapping.items():
        actual,_=object_bytes(root,head,stage)
        need(oid==actual and SHA.fullmatch(oid) is not None,
             "candidate staged source has incorrect committed object ID")
    return mapping


def verify_target_worktree(worktree,reviewed_head):
    checked=scalar(worktree,"rev-parse","HEAD")
    need(not run(worktree,"status","--porcelain=v1","--untracked-files=all"),
         "candidate worktree unreviewed modification or untracked content")
    profile=workflow_audit(worktree,checked,phase="active")
    tooling=tooling_audit(worktree,checked,phase="active")
    identity=a2_audit(worktree,reviewed_head)
    need(profile["head_sha"]==checked and
         profile["current_reviewed_workflow_count"]==30 and
         profile["retained_historical_count"]==23 and
         profile["replacement_count"]==2 and
         profile["addition_count"]==5 and
         profile["independent_security_review"] is False and
         tooling["workflow_profile_sha256"]==
             profile["current_source_profile_sha256"] and
         identity["checked_sha"]==checked and
         identity["head_sha"]==reviewed_head and
         identity["head_tree_sha"]==scalar(worktree,"rev-parse",
                                          checked+"^{tree}") and
         identity["current_workflow_profile_sha256"]==
             profile["current_source_profile_sha256"] and
         identity["independent_security_review"] is False,
         "candidate historical and current-source profiles disagree")
    return profile,tooling,identity


def execute(head,output):
    """Run actual source-code verification; no mocked compiler/reviewer claims."""
    output=Path(output).absolute()
    need(not output.exists() and not output.is_symlink() and
         not output.is_relative_to(ROOT.resolve()) and
         not any(p.is_symlink() for p in output.parents),
         "rehearsal report must be a new external regular-file path")
    original_source(ROOT,head)
    pre=workflow_audit(ROOT,scalar(ROOT,"rev-parse","HEAD"),phase="staged")
    need(pre.get("historical_original_workflow_count")==25 and
         pre.get("current_reviewed_workflow_count")==30 and
         pre.get("versioned_source_phase")=="staged",
         "original source is not exact 25 plus virtual 30 staged proposal")
    sources=planned_sources(ROOT,head)
    report={}
    with tempfile.TemporaryDirectory(prefix="pr113-disposable-source-") as temp:
        worktree=Path(temp)/"checkout"
        need(not worktree.exists(),"temporary checkout destination occupied")
        run(ROOT,"worktree","add","--detach",str(worktree),head,seconds=180)
        try:
            need(len(list((worktree/".github/workflows").glob("*.yml")))==25,
                 "original disposable worktree is not exactly 25 workflows")
            for path,(stage,oid) in sorted(sources.items()):
                _,raw=object_bytes(ROOT,head,stage)
                dest=worktree/path
                need(not dest.is_symlink(),"symlinked target in disposable tree")
                dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes(raw)
                need(hashlib.sha1(
                    b"blob "+str(len(raw)).encode("ascii")+b"\0"+dest.read_bytes()
                    ).hexdigest()==oid,
                    "disposable source write did not match exact staged blob")
            run(worktree,"add","--",*sorted(sources))
            run(worktree,"commit","--no-gpg-sign",
                "-m","PR113 DISPOSABLE 30-source review rehearsal only",
                author=True,seconds=180)
            C=scalar(worktree,"rev-parse","HEAD")
            profile,tooling,identity=verify_target_worktree(worktree,C)
            tree=scalar(worktree,"rev-parse",C+"^{tree}")
            S=run(worktree,"commit-tree",tree,"-p",PR113_BASE,"-p",C,
                  input_bytes=b"PR113 DISPOSABLE ordered [B113,C] dry-run\n",
                  author=True).decode().strip()
            need(SHA.fullmatch(S) is not None and
                 scalar(worktree,"show","-s","--format=%P",S).split()==
                     [PR113_BASE,C] and
                 scalar(worktree,"rev-parse",S+"^{tree}")==tree,
                 "failed to form authentic detached ordered synthetic checkout")
            run(worktree,"checkout","--detach",S)
            synthetic_profile,synthetic_tooling,synthetic_identity=\
                verify_target_worktree(worktree,C)
            need(synthetic_profile["current_source_profile_sha256"]==
                     profile["current_source_profile_sha256"] and
                 synthetic_tooling["workflow_profile_sha256"]==
                     tooling["workflow_profile_sha256"] and
                 synthetic_identity["checked_sha"]==S and
                 synthetic_identity["head_sha"]==C,
                 "direct C and ordered S disagree on exact active30 source")
            # Even in the synthetic candidate checkout, changing one exact
            # source byte must not satisfy the reviewed profile contract.
            target=worktree/".github/workflows/research-lean.yml"
            original=target.read_bytes()
            try:
                target.write_bytes(original+b"\n# malicious unreviewed drift\n")
                rejected=False
                try:
                    workflow_audit(worktree,S,phase="active")
                except (OSError,ValueError):
                    rejected=True
                need(rejected,"corrupted synthetic workflow source was accepted")
            finally:
                target.write_bytes(original)
            need(not run(worktree,"status","--porcelain=v1","--untracked-files=all"),
                 "disposable workflow source was not restored after mutation")
            report={
                "format":FORMAT,
                "status":"DISPOSABLE_SOURCE_AND_ORDERED_SYNTHETIC_REHEARSED_UNREVIEWED",
                "actual_requested_head":head,
                "source_at_invocation":scalar(ROOT,"rev-parse","HEAD"),
                "original_25_workflow_anchor":PREACTIVATION_HEAD,
                "disposable_current_source_commit":C,
                "disposable_synthetic_source_commit":S,
                "disposable_git_tree":tree,
                "historical_original_workflow_count":25,
                "current_reviewed_workflow_count":30,
                "retained_workflow_count":23,
                "replacement_workflow_count":2,
                "addition_workflow_count":5,
                "guard_source_replacements":sorted(SOURCE_REPLACEMENTS),
                "profile_sha256":profile["current_source_profile_sha256"],
                "synthetic_profile_sha256":
                    synthetic_profile["current_source_profile_sha256"],
                "disposable_source_mutation_rejected":True,
                "original_T_archive_replay":"NOT_EXECUTED",
                "original_A2_compiler_replay":"NOT_EXECUTED",
                "source_bound_GitHub_producer_authenticated":False,
                "independent_security_review":False,
                "owner_activation_authorized":False,
                "all_required_CI_green":False,
                "mathematical_acceptance":False,
                "merged_main_sha":None,
                "owner_merge_authorized":False,
                "publication_authorized":False,
            }
        finally:
            run(ROOT,"worktree","remove","--force",str(worktree),seconds=180)
    need(not run(ROOT,"status","--porcelain=v1","--untracked-files=all"),
         "original checkout changed during detached source rehearsal")
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open("x",encoding="utf-8") as f:
        json.dump(report,f,sort_keys=True,indent=2)
        f.write("\n")
    return report


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head",required=True)
    parser.add_argument("--out",required=True,type=Path)
    args=parser.parse_args(argv)
    try:
        result=execute(args.head,args.out)
        print(json.dumps({"status":result["status"],
                          "candidate":result["disposable_current_source_commit"],
                          "original_source_unmodified":True},sort_keys=True))
        return 0
    except (OSError,ValueError,KeyError) as exc:
        print("PR113 DISPOSABLE WORKTREE REHEARSAL BLOCKED:",exc,file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())
