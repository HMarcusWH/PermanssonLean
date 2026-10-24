"""Run BOTH real A2 proof paths without disabling historical verification.

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
import re
import sys

import localized_prefix_gate as historical_gate
import pr113_a2_successor_compiler as successor_gate
import localized_prefix_support as frozen

SHA40=re.compile(r"^[0-9a-f]{40}$")
FORMAT="Permansson.PR113.DualA2CompilerCandidate.v1"

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
    return root

def validate_run(result,mode,mutations,names):
    need(isinstance(result,dict) and result.get("status")==mode and
         result.get("source_unchanged") is True and
         isinstance(result.get("declarations"),dict) and
         set(result["declarations"]) == set(names) and
         isinstance(result.get("mutations"),dict) and
         set(result["mutations"]) == set(mutations),
         "real A2 proof run did not complete all signatures/mutants")
    logs=result.get("commands")
    need(isinstance(logs,list) and
         all(isinstance(x,dict) and
             type(x.get("returncode")) is int and
             isinstance(x.get("log_sha256"),str) and
             len(x["log_sha256"])==64
             for x in logs),
         "A2 compilation log/diagnostic evidence incomplete")
    labels={row["label"] for row in logs}
    need(set(mutations) <= labels and
         {"compiler_version","research_build","signatures_axioms",
          "positive_fixture"} <= labels,
         "historical or successor A2 compiler did not execute every required leg")
    need(all(row.get("status")=="SEMANTICALLY_REJECTED"
             for row in result["mutations"].values()),
         "at least one A2 false semantic mutant was accepted")
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
    historical=historical_gate.verify(
        old,target/"historical_original_A2",mode=mode)
    validate_run(historical,
                 "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
                 historical_gate.MUTATIONS,historical_gate.DECLS)
    current_result=successor_gate.verify(
        current,target/"pr113_successor_A2",mode=mode)
    validate_run(current_result,
                 "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
                 successor_gate.MUTATIONS,successor_gate.DECLS)
    need(current_result.get("independent_security_review") is False and
         current_result.get("historical_a2_verifier_replaced") is False and
         current_result.get("mathematical_acceptance") is False,
         "successor compiler fabricated independent review")
    output_data={
        "format":FORMAT,
        "status":"BOTH_ACTUAL_A2_COMPILER_PATHS_EXECUTED_UNREVIEWED",
        "historical_source_commit":historical_head,
        "current_source_commit":current_head,
        "historical_test_executed":True,
        "successor_test_executed":True,
        "historical_signatures":len(historical_gate.DECLS),
        "successor_signatures":len(successor_gate.DECLS),
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
