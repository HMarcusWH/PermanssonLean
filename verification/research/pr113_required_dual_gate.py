"""Proposed mandatory historical verification adapter; INACTIVE until review.

Runs only from a genuine PR113 synthetic-merge required-check event. It
validates both original historical producer ZIPs and one real independently
approved, exact-H security review using the noncircular historical gate.
No local mode, no GitHub status overrides, no release or merge authority.

The two original required workflow definitions and the original A2 test are
not changed by this module. Installation requires separate security review
of the complete 25+5 workflow set and explicit owner activation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

import infrastructure_acceptance as historical

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.VersionedRequiredHistoricalGate.v1"
REPOSITORY = "HMarcusWH/PermanssonLean"
PR = 113
SHA = re.compile(r"^[0-9a-f]{40}$")
JOBS = {
    "research": "Research Lean",
    "archive-reproducibility": "Research integrity",
}


class RequiredGateError(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise RequiredGateError(message)


def actual_ci_event(*, env=None, git=None, event_data=None):
    """Bind the actual runner event and checkout, not text-supplied H/B/S."""
    env = os.environ if env is None else env
    need(env.get("GITHUB_ACTIONS") == "true"
         and env.get("GITHUB_REPOSITORY") == REPOSITORY
         and env.get("GITHUB_EVENT_NAME") == "pull_request"
         and env.get("GITHUB_REF") == "refs/pull/113/merge"
         and env.get("GITHUB_JOB") in JOBS
         and env.get("GITHUB_WORKFLOW") == JOBS[env["GITHUB_JOB"]],
         "must be an authentic PR113 original required-check runner event")
    synthetic = env.get("GITHUB_SHA")
    need(isinstance(synthetic, str) and SHA.fullmatch(synthetic),
         "real GitHub PR test-merge source SHA absent")
    try:
        run_id,attempt=int(env.get("GITHUB_RUN_ID", "")), int(
            env.get("GITHUB_RUN_ATTEMPT", ""))
    except (ValueError,TypeError) as exc:
        raise RequiredGateError("original GitHub run/attempt identity missing") from exc
    need(run_id > 0 and attempt > 0,
         "original required-check run identity not positive")
    if event_data is None:
        path=Path(env.get("GITHUB_EVENT_PATH", ""))
        need(path.is_file() and not path.is_symlink() and
             0 < path.stat().st_size <= 8*1024*1024,
             "original runner event JSON not available")
        event_data=path.read_bytes()
    need(type(event_data) is bytes and
         0 < len(event_data) <= 8*1024*1024,
         "original event bytes absent or oversized")
    try:
        event=json.loads(event_data)
    except (ValueError,TypeError) as exc:
        raise RequiredGateError("invalid GitHub required-check event JSON") from exc
    pr=event.get("pull_request") if isinstance(event,dict) else None
    need(isinstance(pr,dict) and
         event.get("number")==PR and
         (event.get("repository") or {}).get("full_name")==REPOSITORY and
         (pr.get("base") or {}).get("ref")=="main" and
         (pr.get("base") or {}).get("repo",{}).get("full_name")==REPOSITORY and
         (pr.get("head") or {}).get("repo",{}).get("full_name")==REPOSITORY,
         "PR event is not source-bound to this repository's main")
    base=(pr.get("base") or {}).get("sha")
    head=(pr.get("head") or {}).get("sha")
    need(isinstance(base,str) and SHA.fullmatch(base) and
         isinstance(head,str) and SHA.fullmatch(head) and head!=base,
         "missing authentic PR original head/base identity")
    if git is None:
        def git(*args):
            try:
                return subprocess.check_output(["git",*args],cwd=ROOT,
                         stderr=subprocess.DEVNULL,text=True,timeout=20).strip()
            except (OSError,subprocess.CalledProcessError,
                    subprocess.TimeoutExpired) as exc:
                raise RequiredGateError("original Git checkout unavailable") from exc
    need(git("rev-parse","HEAD")==synthetic,
         "runner's actual checkout is not the genuine GitHub test merge")
    return {
        "original_base_sha":base, "head_sha":head,
        "synthetic_sha":synthetic,"github_run_id":run_id,
        "github_run_attempt":attempt,"github_job":env["GITHUB_JOB"],
        "event_sha256":hashlib.sha256(event_data).hexdigest(),
    }


def verify(input_envelope, t_zip, a2_zip, *, env=None, git=None,
           event_data=None, historical_gate=None):
    # Authentic merged-main pushes require an independent ordered B/H/M check,
    # not a forged replay of the draft-only PR test-merge source binding.
    env = os.environ if env is None else env
    if env.get("GITHUB_EVENT_NAME") == "push":
        from pr113_historical_postmerge import verify as verify_main
        if historical_gate is not None:
            raise RequiredGateError("fake premerge acceptance cannot run on main")
        # An omitted Git adapter means the real authenticated Git reader,
        # not an explicit None that would disable postmerge source checking.
        if git is None:
            return verify_main(input_envelope,t_zip,a2_zip,env=env,
                               event_bytes=event_data)
        return verify_main(input_envelope,t_zip,a2_zip,env=env,
                           git=git,event_bytes=event_data)
    context=actual_ci_event(env=env,git=git,event_data=event_data)
    need(isinstance(input_envelope,dict)
         and isinstance(input_envelope.get("target"),dict)
         and input_envelope["target"].get("base_sha")==
             context["original_base_sha"]
         and input_envelope["target"].get("head_sha")==context["head_sha"]
         and input_envelope["target"].get("synthetic_sha")==
             context["synthetic_sha"],
         "runtime target does not match actual GitHub PR H/B/S")
    if historical_gate is None:
        historical_gate=historical.check_historical_only
    source=historical_gate(input_envelope,t_zip,a2_zip)
    need(isinstance(source,dict) and
         source.get("status") ==
             "HISTORICAL_T_AND_A2_GENUINE_WITH_INDEPENDENT_SECURITY_REVIEW"
         and source.get("source_head")==context["head_sha"]
         and source.get("historical_source_and_security_review_authenticated")
             is True
         and source.get("required_ci_successful")==0
         and source.get("merge_authorized") is False
         and source.get("publication_authorized") is False
         and source.get("independent_mathematical_review") is False,
         "historical dual-check acceptance is incomplete or asserts release")
    return {
        "format":FORMAT,
        "status":"REQUIRED_HISTORICAL_SOURCE_AND_SECURITY_REVIEW_VERIFIED",
        "head_sha":context["head_sha"],
        "original_base_sha":context["original_base_sha"],
        "synthetic_sha":context["synthetic_sha"],
        "github_run_id":context["github_run_id"],
        "github_run_attempt":context["github_run_attempt"],
        "github_job":context["github_job"],
        "event_sha256":context["event_sha256"],
        "original_T_provenance":source["genuine_artifacts"]["T"],
        "original_A2_provenance":source["genuine_artifacts"]["A2"],
        "original_T_checks":source["T_execution"],
        "original_A2_checks":source["A2_execution"],
        "independent_security_review_authenticated":True,
        "all_required_CI_accepted":False,
        "mathematical_acceptance":False,
        "owner_merge_authorized":False,
        "publication_authorized":False,
    }


def cli(argv=None):
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--evidence",type=Path,required=True)
    ap.add_argument("--historical-T-zip",type=Path,required=True)
    ap.add_argument("--historical-A2-zip",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    args=ap.parse_args(argv)
    try:
        output=args.out.absolute()
        need(not output.exists() and
             not any(x.is_symlink() for x in (output,*output.parents)) and
             not output.is_relative_to(ROOT.resolve()),
             "required historical receipt must be new and detached")
        envelope=args.evidence.read_bytes()
        need(0 < len(envelope) <= 64*1024,
             "original detached historical evidence too large")
        zips=[]
        for path in (args.historical_T_zip,args.historical_A2_zip):
            need(path.is_file() and not path.is_symlink() and
                 0 < path.stat().st_size <= 256*1024*1024,
                 "historical original ZIP absent or unbounded")
            zips.append(path.read_bytes())
        result=verify(json.loads(envelope),*zips)
        output.parent.mkdir(parents=True,exist_ok=True)
        with output.open("x",encoding="utf-8") as writer:
            json.dump(result,writer,sort_keys=True,indent=2)
            writer.write("\n")
        print(json.dumps({"status":result["status"],"head_sha":result["head_sha"]}))
        return 0
    except (RequiredGateError,historical.InfrastructureError,OSError,TypeError,
            ValueError,KeyError) as exc:
        print("HISTORICAL REQUIRED GATE NOT ACCEPTED:",exc,file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(cli())
