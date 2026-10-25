"""Exact proposed 25+5 GitHub workflow profile: read-only and NOT activation.

A candidate source manifest is not independent security approval. This
preflight explicitly retains all 25 approved historical workflows byte-for-
byte and binds five proposed successor workflow source blobs to a versioned
review dossier. It never edits .github/workflows or relaxes historical T/A2.
"""
from __future__ import annotations

import argparse
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
from verification.integrity.workflow_contract import APPROVED_WORKFLOWS
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
        need(isinstance(path,str) and
             (path.startswith(".github/workflows/") or
              path.startswith(STAGED_PREFIX)),
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


def audit(head, *, read=None, tree=None, approved=None):
    need(isinstance(head,str) and SHA.fullmatch(head),
         "unknown candidate H identity")
    if read is None:
        read=lambda p:git_bytes(head,p)
    if tree is None:
        tree=lambda:git_bytes(head,op=(
            "ls-tree","-r","--name-only",head,"--",".github/workflows"))
    if approved is None:
        approved=APPROVED_WORKFLOWS
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
