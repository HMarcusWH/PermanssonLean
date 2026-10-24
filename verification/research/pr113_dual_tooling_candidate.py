"""Dual historical T and current H tooling candidate; no security approval.

Run the ORIGINAL historical offline archive verifier from an unmodified real T
checkout, independently of the current H's workflow integrity suite. The
historical supplement is supplied from H but independently checked against
the immutable T package via pr113_tooling_migration.audit.

This is deliberately NOT wired into the required archive workflow before
owner authorization and an independent security review. Neither the original
T/C closure error nor original verifier is rewritten, skipped or relabelled.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from pr113_tooling_migration import T, audit as tooling_audit
import localized_prefix_support as git_source

FORMAT="Permansson.PR113.DualToolingCandidate.v1"
SHA40=re.compile(r"^[0-9a-f]{40}$")

class DualToolingError(ValueError):
    pass

def demand(value,message):
    if not value:raise DualToolingError(message)

def checkout(root,commit):
    raw=Path(root)
    demand(not raw.is_symlink() and
           not any(parent.is_symlink() for parent in raw.absolute().parents),
           "historical/current source may not have symlink ancestors")
    src=raw.resolve(strict=True)
    demand(src.is_dir() and SHA40.fullmatch(commit) is not None and
           git_source.git_text(src,"rev-parse","HEAD")==commit and
           Path(git_source.git_text(src,"rev-parse","--show-toplevel")).resolve()==src,
           "not a genuine exact-commit source checkout")
    demand(not git_source.git_bytes(
        src,"status","--porcelain=v1","--untracked-files=all"),
        "archival tooling checkout has unreviewed source changes")
    return src

def validate_dual_reports(historical, current, *, T_source, H_source):
    demand(isinstance(historical,dict) and
           historical.get("status")=="PASS" and
           historical.get("check")=="archive-reproducibility",
           "original T offline archive verifier did not PASS")
    details=historical.get("details")
    demand(isinstance(details,dict) and
           details.get("acceptance_scope")=="accepted_artifact_replay_only" and
           isinstance(details.get("isolation"),dict) and
           details["isolation"].get("network_isolation")=="ENFORCED" and
           details["isolation"].get("capabilities")=="all_zero",
           "original T offline restore omitted true network isolation")
    demand(isinstance(current,dict) and
           current.get("status")=="PASS" and
           current.get("suite")=="workflow" and
           current.get("execution_tracked_clean") is True and
           current.get("methods_run",0)>0,
           "current H workflow verifier did not execute complete suite")
    return {
        "format":FORMAT,
        "status":"DUAL_T_AND_H_EXECUTED_UNREVIEWED",
        "historical_T":T_source,"current_H":H_source,
        "original_T_archive_offline_restoration_passed":True,
        "current_H_workflow_test_suite_passed":True,
        "source_review_approval":False,
        "independent_security_review":False,
        "required_current_archive_CI_green":False,
        "mathematical_release_approved":False,
    }

def command(argv,cwd,limit=1800):
    try:
        result=subprocess.run(argv,cwd=cwd,timeout=limit,
                              capture_output=True,text=True)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise DualToolingError("isolated original verification unavailable") from exc
    if result.returncode!=0:
        raise DualToolingError("actual historical/current verifier exited "+
                               str(result.returncode)+": "+
                               (result.stdout+result.stderr)[-1800:])
    return result

def execute(historical_source,current_source,head,out):
    historical=checkout(historical_source,T)
    current=checkout(current_source,head)
    demand(historical!=current and head!=T,
           "separate genuine T and H checkouts mandatory")
    output=Path(out)
    demand(not output.is_symlink(),"output symlink forbidden")
    output=output.resolve()
    demand(not output.exists() and
           not output.is_relative_to(historical) and
           not output.is_relative_to(current),
           "archive evidence output must be new, detached and disjoint")
    proposal=tooling_audit(current,head)
    demand(proposal["status"]=="DRAFT_NEEDS_OWNER_AND_INDEPENDENT_SECURITY_REVIEW"
           and proposal["historical_archive_unchanged"] is True and
           len(proposal["changed_canonical_tooling"])==2,
           "T/H tooling changes are not the exactly reviewed two-file proposal")
    supplement=current/"archival/v0.2.0/supplement-1"
    demand(supplement.is_dir() and not supplement.is_symlink(),
           "actual immutable historical supplement missing")
    output.mkdir(parents=True,exist_ok=False)
    original_report=output/"original_T_archive.json"
    current_report=output/"current_H_workflow.json"
    # Never use a newer H interpreter for the old T archive.
    # Running under GitHub Actions without the historical identity binding is
    # unsafe: require an authorized separate isolated historical environment.
    demand(os.environ.get("GITHUB_ACTIONS")!="true",
           "cannot disguise standalone historical T replay as current GitHub CI")
    command([sys.executable,"-B","-m","verification.archive.offline_smoke",
             "--supplement",str(supplement),
             "--scratch",str(output/"historical_restore"),
             "--report",str(original_report)],historical)
    command([sys.executable,"-B","-m","verification.integrity.run_tests",
             "--suite","workflow","--report",str(current_report)],current)
    old=json.loads(original_report.read_bytes())
    new=json.loads(current_report.read_bytes())
    receipt=validate_dual_reports(old,new,T_source=T,H_source=head)
    receipt["historical_manifest_sha256"]=proposal["historical_manifest_sha256"]
    receipt["reviewed_25_workflow_inventory"]=proposal["current_workflow_file_count"]
    (output/"dual_tooling_unreviewed.json").write_text(
        json.dumps(receipt,sort_keys=True,indent=2)+"\n")
    return receipt

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--historical-T-source",required=True,type=Path)
    p.add_argument("--current-source",required=True,type=Path)
    p.add_argument("--head",required=True)
    p.add_argument("--output",required=True,type=Path)
    a=p.parse_args(argv)
    try:
        print(json.dumps(execute(a.historical_T_source,
                                 a.current_source,a.head,a.output),
                         sort_keys=True))
        return 0
    except (DualToolingError,OSError,ValueError,KeyError) as exc:
        print("PR113 T/H DUAL TOOLING BLOCKED:",exc,file=sys.stderr)
        return 2
if __name__=="__main__":
    raise SystemExit(main())
