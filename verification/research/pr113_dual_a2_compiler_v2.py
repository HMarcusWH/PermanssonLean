"""Run BOTH real A2 paths with separately pinned active30 successor.

Historical A2 uses the untouched localized_prefix_gate on a separately
checked-out historical source (caller must name the real historical commit).
PR113 A2 uses the versioned exact-H/S successor checker on current source.
Both run pinned Lean, signature/axiom checks, positive control and all four
genuine semantic mutants; neither result grants security/mathematical review.
The old verifier remains in the original Research workflow until authorized.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import hashlib
import os
import re
import subprocess
import sys

import localized_prefix_gate as historical_gate
import pr113_a2_successor_compiler_v2 as successor_gate
import localized_prefix_support as frozen
import pr113_historical_a2_baseline_v1 as baseline

SHA40=re.compile(r"^[0-9a-f]{40}$")
FORMAT=baseline.DUAL_FORMAT
HISTORICAL_INTRODUCER="f71a76032b169aac7bfe0694aa715339a94d4e05"
HISTORICAL_GATE="verification/research/localized_prefix_gate.py"
HISTORICAL_SUPPORT="verification/research/localized_prefix_support.py"

class DualA2Error(ValueError):
    pass

def need(condition,message):
    if not condition:raise DualA2Error(message)

def real_source(root,head):
    original=Path(root)
    need(not original.is_symlink() and
         not any(p.is_symlink() for p in original.absolute().parents),
         "symlink source checkout not permitted")
    root=original.resolve(strict=True)
    need(root.is_dir() and SHA40.fullmatch(head) is not None and
         frozen.git_text(root,"rev-parse","HEAD")==head and
         Path(frozen.git_text(root,"rev-parse","--show-toplevel")).resolve()==root,
         "requested A2 source must be a genuine exact-head Git checkout")
    need(not frozen.git_bytes(
        root,"status","--porcelain=v1","--untracked-files=all"),
        "A2 source checkout contains tracked/untracked modifications")
    return root


def historical_command(historical_root, output, mode):
    """Launch the independently committed historical module, not H's import."""
    program=historical_root/HISTORICAL_GATE
    need(program.is_file() and not program.is_symlink(),
         "historical A2 executable is not a regular committed file")
    return [sys.executable,"-B",str(program),
            "--repo",str(historical_root),
            "--output",str(output),"--mode",mode]


def run_historical_verified(historical_root, commit, output, mode):
    """Execute the corrected positive baseline using its own untouched code."""
    need(commit == baseline.REPLAY_HEAD,
         "positive historical A2 requires corrected PR80 head, not introducer")
    baseline.verify_positive_source(historical_root)
    frozen.git_bytes(historical_root,"merge-base","--is-ancestor",
                     HISTORICAL_INTRODUCER,commit)
    historical_gate_blob=frozen.git_text(
        historical_root,"rev-parse",commit+":"+HISTORICAL_GATE)
    introduced_blob=frozen.git_text(
        historical_root,"rev-parse",HISTORICAL_INTRODUCER+":"+HISTORICAL_GATE)
    need(historical_gate_blob==introduced_blob,
         "historical A2 executor byte-drifted from original introducer")
    pinned={}
    for path in (HISTORICAL_GATE,HISTORICAL_SUPPORT):
        committed=frozen.git_text(
            historical_root,"rev-parse",commit+":"+path)
        source=historical_root/path
        need(source.is_file() and not source.is_symlink() and
             frozen.blob_sha(source.read_bytes())==committed,
             "historical A2 runtime source mismatched original Git object: "+path)
        pinned[path]=committed
    environment=os.environ.copy()
    for name in ("PYTHONPATH","PYTHONHOME"):
        environment.pop(name,None)
    environment["PYTHONDONTWRITEBYTECODE"]="1"
    command=historical_command(historical_root,output,mode)
    try:
        completed=subprocess.run(
            command,cwd=historical_root,env=environment,
            text=True,capture_output=True,timeout=5400)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise DualA2Error("original historical A2 runtime unavailable") from exc
    need(output.joinpath("receipt.json").is_file(),
         "historical runtime omitted its own original signed-source receipt")
    try:
        evidence=json.loads(output.joinpath("receipt.json").read_bytes())
    except (OSError,ValueError,UnicodeError) as exc:
        raise DualA2Error("historical runtime returned invalid original receipt") from exc
    # A compiler failure must expose the original label, exit and reason,
    # not masquerade as a source-authentication mismatch.
    baseline.require_runtime_success(completed.returncode, evidence)
    baseline.verify_receipt_source(evidence)
    baseline.verify_positive_source(historical_root)
    evidence["historical_runtime_provenance"]={
        "historical_checkout_sha":commit,
        "historical_tree_sha":baseline.REPLAY_TREE,
        "baseline_contract":baseline.FORMAT,
        "introduced_executable_sha":HISTORICAL_INTRODUCER,
        "original_runtime_git_blobs":pinned,
        "output_receipt_sha256":hashlib.sha256(
            output.joinpath("receipt.json").read_bytes()).hexdigest(),
        "imported_current_A2_gate":False,
        "independent_security_review":False,
    }
    return evidence

def validate_run(result,mode,mutations,names):
    need(isinstance(result,dict) and result.get("status")==mode and
         result.get("source_unchanged") is True and
         isinstance(result.get("declarations"),dict) and
         set(result["declarations"]) == set(names) and
         isinstance(result.get("mutations"),dict) and
         set(result["mutations"]) == set(mutations),
         "real A2 proof run did not complete all signatures/mutants")
    logs=result.get("commands")
    mandatory={"compiler_version","research_build","signatures_axioms",
               "positive_fixture",*(f"source_{i}" for i in range(1,5))}
    need(isinstance(logs,list) and all(
         isinstance(x,dict) and
         isinstance(x.get("label"),str) and
         type(x.get("returncode")) is int and
         x["returncode"] not in (-999,-998) and
         isinstance(x.get("log_sha256"),str) and
         re.fullmatch(r"[0-9a-f]{64}",x["log_sha256"]) is not None
         for x in logs),
         "A2 compilation log/diagnostic evidence incomplete")
    labels=[row["label"] for row in logs]
    need(len(set(labels))==len(labels) and
         set(labels)==mandatory|set(mutations)|
             ({"original_default_build"} if result.get("mode")=="full" else set()),
         "historical or successor A2 compiler duplicated/omitted a required leg")
    need(all(row["returncode"]==0 if row["label"] not in mutations
             else row["returncode"]!=0 for row in logs),
         "A2 positive source did not compile or false mutant unexpectedly compiled")
    need(all(isinstance(row,dict) and
             row.get("status")=="SEMANTICALLY_REJECTED" and
             isinstance(row.get("positive_source_sha256"),str) and
             isinstance(row.get("mutant_source_sha256"),str) and
             re.fullmatch(r"[0-9a-f]{64}",row["positive_source_sha256"]) and
             re.fullmatch(r"[0-9a-f]{64}",row["mutant_source_sha256"]) and
             row["positive_source_sha256"]!=row["mutant_source_sha256"]
             for row in result["mutations"].values()),
         "at least one A2 false semantic mutant was not source-bound rejected")
    return True

def execute(historical_source, historical_head, current_source, current_head,
            output, *, mode="focused"):
    need(mode in ("focused","full"),"unsupported real A2 execution mode")
    old=real_source(historical_source,historical_head)
    current=real_source(current_source,current_head)
    target=Path(output)
    need(not target.is_symlink(),"A2 evidence output cannot be symlinked")
    target=target.resolve()
    need(not target.exists() and
         not target.is_relative_to(old) and
         not target.is_relative_to(current) and
         not old.is_relative_to(target) and
         not current.is_relative_to(target),
         "A2 evidence must be a new detached directory")
    need(old != current and historical_head != current_head,
         "two different historical and PR113 source revisions required")
    target.mkdir(parents=True, exist_ok=False)
    historical=run_historical_verified(
        old,historical_head,target/"historical_original_A2",mode)
    validate_run(historical,
                 "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
                 historical_gate.MUTATIONS,historical_gate.DECLS)
    current_result=successor_gate.verify(
        current,target/"pr113_successor_A2",mode=mode)
    validate_run(current_result,
                 "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                 successor_gate.MUTATIONS,successor_gate.DECLS)
    need(isinstance(historical.get("historical_runtime_provenance"),dict) and
         historical["historical_runtime_provenance"].get(
             "imported_current_A2_gate") is False,
         "historical leg did not execute its own immutable source")
    need(current_result.get("independent_security_review") is False and
         current_result.get("historical_a2_verifier_replaced") is False and
         current_result.get("mathematical_acceptance") is False,
         "successor compiler fabricated independent review")
    output_data={
        "format":FORMAT,
        "status":"BOTH_ACTUAL_A2_COMPILER_PATHS_EXECUTED_UNREVIEWED",
        "historical_source_commit":historical_head,
        "historical_introducer_sha":baseline.INTRODUCER,
        "historical_tree_sha":baseline.REPLAY_TREE,
        "historical_runtime_provenance":historical["historical_runtime_provenance"],
        "current_source_commit":current_head,
        "historical_test_executed":True,
        "successor_test_executed":True,
        "historical_signatures":len(historical_gate.DECLS),
        "successor_signatures":len(successor_gate.DECLS),
        "current_reviewed_workflow_count":30,
        "historical_original_workflow_count":25,
        "historical_semantic_mutants":len(historical_gate.MUTATIONS),
        "successor_semantic_mutants":len(successor_gate.MUTATIONS),
        "original_verifier_modified":False,
        "independent_security_approval":False,
        "independent_mathematical_approval":False,
        "required_research_CI_accepted":False,
        "merged_main_sha":None,
        "full_release_approved":False,
    }
    (target/"unreviewed_dual_A2_candidate.json").write_text(
        json.dumps(output_data,sort_keys=True,indent=2)+"\n")
    return output_data

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--historical-source",required=True,type=Path)
    p.add_argument("--historical-head",required=True)
    p.add_argument("--current-source",required=True,type=Path)
    p.add_argument("--current-head",required=True)
    p.add_argument("--out",required=True,type=Path)
    p.add_argument("--mode",choices=("focused","full"),default="focused")
    a=p.parse_args(argv)
    try:
        print(json.dumps(execute(a.historical_source,a.historical_head,
                                 a.current_source,a.current_head,
                                 a.out,mode=a.mode),sort_keys=True))
        return 0
    except (DualA2Error,OSError,ValueError,KeyError) as exc:
        print("PR113 DUAL A2 VERIFICATION BLOCKED:",exc,file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
