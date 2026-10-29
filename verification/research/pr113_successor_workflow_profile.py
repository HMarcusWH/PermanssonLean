"""Exact proposed 25+5 GitHub workflow profile: read-only and NOT activation.

A candidate source manifest is not independent security approval. This
preflight explicitly retains all 25 approved historical workflows byte-for-
byte and binds five proposed successor workflow source blobs to a versioned
review dossier. It never edits .github/workflows or relaxes historical T/A2.
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

# Direct invocation (python verification/research/pr113_successor_workflow_profile.py)
# otherwise includes only verification/research in sys.path, not the repository
# package root. Resolve the exact local checkout before import, then audit all
# 25 protected Git blobs against the original hashes as before.
ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from release_target import B113, T
# Do NOT import the current workflow contract: the independently staged v2
# replacement intentionally removes the historical APPROVED_WORKFLOWS symbol.
# The 25-source contract is instead parsed from its immutable actual Git blob.
HISTORICAL_25_HEAD = "5189f0c4a0db7535d57a9ff2a7aef6a3e76191b6"
HISTORICAL_CONTRACT = "verification/integrity/workflow_contract.py"
HISTORICAL_CONTRACT_BLOB = "f8fa8196a7a0e33d2f218faa0ba570c09aac9a3a"
MANIFEST = "docs/operations/pr113_unapproved_workflows/manifest.json"
FORMAT = "Permansson.PR113.SuccessorWorkflowProfile.v1"
PATH = re.compile(r"^\.github/workflows/[a-zA-Z0-9_.-]+\.ya?ml$")
STAGED_PREFIX = "docs/operations/pr113_unapproved_workflows/"
USES = re.compile(r"(?m)^\s+- uses: [A-Za-z0-9_.@/-]+@([a-f0-9]{40})\s*$")
SHA = re.compile(r"^[a-f0-9]{40}$")
PROPOSED = frozenset((
    "pr113-historical-migration-candidates.yml",
    "pr113-original-positive-controls-candidate.yml",
    "pr113-postseal-replay.yml",
    "pr113-source-controls-v3_1.yml",
    "pr113-preseal-fullscope.yml",
))


class ProfileError(ValueError):
    pass


def need(ok, reason):
    if not ok:
        raise ProfileError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def git_bytes(head, path=None, *, op=None):
    if op is not None:
        args=list(op)
    else:
        # One immutable historical Python source is the ONLY non-workflow
        # exception. Never borrow the same path from current H or another
        # commit, and never admit prefix lookalikes or Git revspec injection.
        need(type(head) is str and SHA.fullmatch(head) is not None and
             type(path) is str,
             "untrusted workflow source path")
        workflow_path=PATH.fullmatch(path) is not None
        staged_name=(path[len(STAGED_PREFIX):]
                     if path.startswith(STAGED_PREFIX) else "")
        staged_path=(bool(staged_name) and
                     re.fullmatch(r"[A-Za-z0-9_.-]+",staged_name) is not None)
        historical_contract_only=(
            head==HISTORICAL_25_HEAD and path==HISTORICAL_CONTRACT)
        need(workflow_path or staged_path or historical_contract_only,
             "untrusted workflow source path")
        args=["show",head+":"+path]
    try:
        proc=subprocess.run(["git",*args],cwd=ROOT,capture_output=True,
                            timeout=30,check=False)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise ProfileError("original Git source unavailable") from exc
    need(proc.returncode==0 and len(proc.stdout)<=4*1024*1024,
         "Git workflow source unavailable")
    return proc.stdout



def parse_historical_25_contract(source):
    """Read exactly the historical 25 SHA-256 pins; never execute old Python.

    The original source uses one named SHA-256 literal for the Research
    integrity workflow and 24 additional string literals. Every other AST
    expression and all duplicate names are rejected, rather than evaluated.
    """
    need(type(source) is bytes and 0<len(source)<=200_000,
         "invalid bounded historical integrity-contract source")
    try:
        parsed=ast.parse(source.decode("utf-8", "strict"),
                         filename=HISTORICAL_CONTRACT)
    except (UnicodeError,SyntaxError,ValueError) as exc:
        raise ProfileError("historical 25-source contract cannot be parsed") from exc
    relevant={}
    for stmt in parsed.body:
        if isinstance(stmt,ast.Assign):
            for target in stmt.targets:
                if isinstance(target,ast.Name) and target.id in (
                    "APPROVED_WORKFLOW_SHA256","APPROVED_WORKFLOWS"):
                    need(len(stmt.targets)==1 and target.id not in relevant,
                         "historical workflow binding duplicated or reassigned")
                    relevant[target.id]=stmt.value
        elif isinstance(stmt,(ast.AnnAssign,ast.AugAssign)):
            target=stmt.target
            if isinstance(target,ast.Name) and target.id in (
                "APPROVED_WORKFLOW_SHA256","APPROVED_WORKFLOWS"):
                raise ProfileError("historical workflow binding mutated")
    singleton=relevant.get("APPROVED_WORKFLOW_SHA256")
    need(isinstance(singleton,ast.Constant)
         and type(singleton.value) is str
         and re.fullmatch(r"[0-9a-f]{64}",singleton.value) is not None,
         "historical Research integrity SHA-256 constant unavailable")
    table=relevant.get("APPROVED_WORKFLOWS")
    need(isinstance(table,ast.Dict) and len(table.keys)==25,
         "historical 25-source SHA-256 allowlist not a literal dictionary")
    values={}
    for key,value in zip(table.keys,table.values):
        need(isinstance(key,ast.Constant) and type(key.value) is str
             and re.fullmatch(r"[A-Za-z0-9_.-]+\.ya?ml",key.value)
                 is not None
             and key.value not in values,
             "historical 25-workflow label absent, invalid, or duplicated")
        if isinstance(value,ast.Name):
            need(value.id=="APPROVED_WORKFLOW_SHA256",
                 "historical workflow digest depends on other Python code")
            hexdigest=singleton.value
        else:
            need(isinstance(value,ast.Constant) and type(value.value) is str,
                 "historical workflow digest not a fixed SHA-256 literal")
            hexdigest=value.value
        need(re.fullmatch(r"[0-9a-f]{64}",hexdigest) is not None,
             "historical workflow identity must be 64-digit SHA-256, not Git OID")
        values[key.value]=hexdigest
    need(len(values)==25 and
         values.get("research-integrity.yml")==singleton.value,
         "original 25-source historical manifest membership changed")
    return values


def authenticated_historical_25(head=None):
    """Authenticate the actual immutable historical Git tree and contract.

    A supplied head must descend from the frozen preactivation source.
    This loader is separate from installed integrity contracts: old 25 SHA256
    identities must never be substituted by successor 30 Git blob OIDs.
    """
    if head is not None:
        need(isinstance(head,str) and SHA.fullmatch(head),
             "noncanonical current source for historical profile")
        git_bytes(head,op=("merge-base","--is-ancestor",HISTORICAL_25_HEAD,head))
    raw=git_bytes(HISTORICAL_25_HEAD,HISTORICAL_CONTRACT)
    oid=git_bytes(HISTORICAL_25_HEAD,op=(
        "rev-parse",HISTORICAL_25_HEAD+":"+HISTORICAL_CONTRACT
    )).decode("ascii","strict").strip()
    need(oid==HISTORICAL_CONTRACT_BLOB and git_blob_oid(raw)==oid,
         "frozen 25-source integrity contract Git blob byte identity changed")
    approved=parse_historical_25_contract(raw)
    tree=git_bytes(HISTORICAL_25_HEAD,op=(
        "ls-tree","-r","-z",HISTORICAL_25_HEAD,"--",".github/workflows"
    ))
    need(tree.endswith(b"\0"),"historical workflow tree missing Git terminator")
    seen={}
    for record in tree[:-1].split(b"\0"):
        try:
            meta,path=record.split(b"\t",1)
            mode,kind,entry_oid=meta.decode("ascii").split()
            filename=path.decode("utf-8","strict")
        except (UnicodeError,ValueError) as exc:
            raise ProfileError("historical workflow Git tree record malformed") from exc
        need(mode=="100644" and kind=="blob"
             and re.fullmatch(r"[0-9a-f]{40}",entry_oid)
             and filename.startswith(".github/workflows/")
             and filename.count("/")==2,
             "frozen 25-source tree member or Git mode unexpected")
        name=filename.removeprefix(".github/workflows/")
        need(name in approved and name not in seen,
             "unexpected or duplicated original workflow Git entry")
        seen[name]=entry_oid
    need(set(seen)==set(approved) and len(seen)==25,
         "historical tree does not contain exactly original 25 workflows")
    for name,expected_digest in approved.items():
        path=".github/workflows/"+name
        content=git_bytes(HISTORICAL_25_HEAD,path)
        need(git_blob_oid(content)==seen[name]
             and digest(content)==expected_digest,
             "immutable historical workflow byte SHA-256 differs: "+name)
    return approved


def audit(head, *, read=None, tree=None, approved=None):
    need(isinstance(head,str) and SHA.fullmatch(head),
         "unknown candidate H identity")
    if read is None:
        read=lambda p:git_bytes(head,p)
    if tree is None:
        tree=lambda:git_bytes(head,op=(
            "ls-tree","-r","--name-only",head,"--",".github/workflows"))
    if approved is None:
        approved=authenticated_historical_25(head)
    need(isinstance(approved,dict) and len(approved)==25,
         "original 25 required workflow hash contract missing")
    active_paths={p.decode("utf-8") for p in tree().splitlines()}
    need(active_paths=={".github/workflows/"+name for name in approved},
         "approved active workflow set changed before security transition")
    active=[]
    for name,expected_sha in sorted(approved.items()):
        path=".github/workflows/"+name
        raw=read(path)
        need(digest(raw)==expected_sha,
             "original approved workflow bytes drifted: "+name)
        active.append({"path":path,"sha256":digest(raw)})
    try:
        manifest=json.loads(read(MANIFEST))
    except (ValueError,TypeError) as exc:
        raise ProfileError("source-staged workflow manifest invalid") from exc
    need(isinstance(manifest,dict) and
         manifest.get("format") ==
             "Permansson.PR113.UnreviewedWorkflowProposals.v1" and
         manifest.get("status") ==
             "SOURCE_STAGED_NONEXECUTABLE_PENDING_INDEPENDENT_SECURITY_REVIEW" and
         manifest.get("original_approved_workflow_count")==25 and
         manifest.get("historic_T")==T and
         manifest.get("base_B")==B113 and
         manifest.get("independent_security_review") is False and
         manifest.get("owner_authorized_activation") is False and
         manifest.get("mathematical_acceptance") is False and
         manifest.get("release_authorized") is False,
         "workflow source manifest silently changed historical authority")
    rows=manifest.get("proposals")
    need(isinstance(rows,list) and len(rows)==5,
         "exact five successor proposals not identified")
    proposed=[]
    for row in rows:
        need(isinstance(row,dict) and
             set(row)=={"workflow_path","staged_source_path",
                         "git_blob_oid","source_unchanged","approved","installed"},
             "invalid source-bound workflow review proposal")
        destination=row["workflow_path"]
        stage=row["staged_source_path"]
        name=Path(destination).name
        need(name in PROPOSED and
             destination==".github/workflows/"+name and
             stage==STAGED_PREFIX+name and
             destination not in active_paths and
             row["installed"] is False and row["approved"] is False and
             isinstance(row.get("git_blob_oid"),str) and
             SHA.fullmatch(row["git_blob_oid"]),
             "unknown/colliding or prematurely installed workflow")
        raw=read(stage)
        need(0<len(raw)<=1_000_000, "unbounded staged workflow source")
        try:
            source=raw.decode("utf-8")
        except UnicodeError as exc:
            raise ProfileError("non-UTF8 staged workflow source") from exc
        # Full source bytes have a Git blob OID supplied by the pinned manifest;
        # the candidate verifier computes its own SHA256 for the security review.
        oid=git_blob_oid(raw)
        need(oid==row["git_blob_oid"],
             "staged source edited without a new versioned workflow manifest")
        need(source.count("\npermissions:\n")==1 and
             "\n  contents: read\n" in source and
             "pull_request_target" not in source and
             not re.search(r"(?m)^\s+\S+:\s*write\s*$",source) and
             not re.search(r"(?m)^\s+- uses:\s+[^\n]*@(?:main|master|v[0-9])\s*$",source),
             "staged source broadens token permissions or uses mutable actions")
        unpinned=[l for l in source.splitlines()
                  if re.match(r"^\s+- uses:",l) and not USES.fullmatch(l)]
        need(not unpinned, "staged workflow contains unpinned third-party action")
        proposed.append({
            "path":destination,
            "staged_source":stage,
            "git_blob_oid":oid,
            "sha256":digest(raw),
        })
    need({Path(row["path"]).name for row in proposed}==PROPOSED,
         "duplicate/missing successor workflow")
    staged_controls=read(STAGED_PREFIX+"pr113-source-controls-v3_1.yml").decode("utf-8")
    observer=staged_controls.split("  original-legacy20:",1)
    need(len(observer)==2 and
         "  original-legacy20-replay:" in observer[1] and
         "pr113_legacy20_choice_delivery.py" in observer[1] and
         "review_comment_id:" in staged_controls and
         'if: github.event_name == \x27workflow_dispatch\x27' in staged_controls,
         "legacy observed/reviewer/replay stages not correctly separated")
    return {
        "format":FORMAT,
        "status":"EXACT_25_PLUS_5_SOURCE_PROFILE_CANDIDATE_NOT_ACTIVATED",
        "head_sha":head,
        "historical_T":T,
        "original_base":B113,
        "original_workflow_count":25,
        "successor_proposal_count":5,
        "proposed_future_workflow_count":30,
        "original_active_workflows":active,
        "review_pending_successors":proposed,
        "profile_sha256":digest(json.dumps(
            {"approved":active,"proposals":proposed},
            sort_keys=True,separators=(",",":")).encode()),
        "independent_security_review":False,
        "owner_activation_authorized":False,
        "active_profile_changed":False,
        "mathematical_acceptance":False,
        "publication_authorized":False,
        "next_required_action":"Independent security review of exact combined "
                               "profile and separate owner activation decision.",
    }


def git_blob_oid(raw):
    # Git's blob object hash includes the header and exact byte count.
    body=b"blob "+str(len(raw)).encode()+b"\0"+raw
    return hashlib.sha1(body).hexdigest()


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head",required=True)
    parser.add_argument("--out",type=Path,required=True)
    a=parser.parse_args(argv)
    try:
        output=a.out.absolute()
        need(not output.exists() and not output.is_symlink()
             and not output.is_relative_to(ROOT.resolve())
             and not any(p.is_symlink() for p in output.parents),
             "profile output must be a fresh detached audit")
        receipt=audit(a.head)
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open("x",encoding="utf-8") as stream:
            json.dump(receipt,stream,sort_keys=True,indent=2)
            stream.write("\n")
        print(json.dumps({k:receipt[k] for k in (
            "status","head_sha","original_workflow_count",
            "successor_proposal_count")},sort_keys=True))
        return 0
    except (ProfileError,OSError,ValueError,TypeError,KeyError) as exc:
        print("WORKFLOW PROFILE NOT ACCEPTED:",exc,file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())
