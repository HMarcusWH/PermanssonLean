"""Discover exact-H original 4+9+8 producer ZIPs AFTER they have run.

Original GitHub job/run/check/artifact IDs cannot be committed before source
freeze H: those IDs only exist after CI executes at H. This stage constructs a
DETACHED runtime catalog, authenticates actual successful GitHub producer
checks, downloads original ZIP bytes and records their immutable digests.

This never changes H, accepts mathematical claims or grants a security review.
A failed/pending/old-head latest producer blocks the whole collection.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import urllib.error
import urllib.request
from urllib.parse import urlsplit

from final_closure_authenticate import live, paginate, AuthenticationError
from final_closure_candidate_artifact_auth import KINDS
from final_closure_complete_lean_evidence import ROOT, git_head

FORMAT="Permansson.PR113.ExternalProducerCatalog.v1"
REPO="HMarcusWH/PermanssonLean"
HEAD=re.compile(r"^[a-f0-9]{40}$")
RUN_URL=re.compile(r"^https://github.com/HMarcusWH/PermanssonLean/actions/runs/([0-9]+)(?:/job/([0-9]+))?$")
MAX_ZIP=64*1024*1024
MAX_TOTAL=256*1024*1024


class DiscoveryError(ValueError):
    pass


def require(ok,reason):
    if not ok:raise DiscoveryError(reason)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def classify_latest(checks, head):
    """Choose latest check ID per original job; never borrow stale green."""
    require(isinstance(head,str) and HEAD.fullmatch(head) and
            isinstance(checks,list), "exact real H/check list required")
    required={(kind,i) for kind,spec in KINDS.items()
              for i in range(spec["count"])}
    latest={}
    for check in checks:
        if not isinstance(check,dict) or check.get("head_sha")!=head:
            continue
        if (check.get("app") or {}).get("slug")!="github-actions":
            continue
        name=check.get("name")
        for kind,shard in required:
            if name!=KINDS[kind]["job"]+f" ({shard})":continue
            id_=check.get("id")
            require(type(id_) is int and id_>0, "missing authentic check-run ID")
            key=kind,shard
            if key not in latest or id_>latest[key]["id"]:
                latest[key]=check
    require(set(latest)==required, "missing full 4+9+8 exact-H producing checks")
    for key,check in latest.items():
        require(check.get("status")=="completed" and
                check.get("conclusion")=="success",
                "latest original producing check not successful: "+
                str(key))
    return latest


def validate_run_job_artifact(*, head, kind, shard, check,
                              run, jobs, artifacts,
                              branch="research/final-mathematical-closure"):
    """Authentic completed run, latest attempt/job, and correct artifact."""
    spec=KINDS[kind]
    require(isinstance(run,dict) and isinstance(jobs,list) and
            isinstance(artifacts,list) and isinstance(check,dict),
            "source GitHub producer API metadata unavailable")
    link=check.get("details_url")
    match=RUN_URL.fullmatch(link) if isinstance(link,str) else None
    require(match is not None, "GitHub check is missing original run URL")
    run_id=int(match.group(1))
    # The immutable original 4+9+8 workflows have narrow push path filters,
    # but all three also expose manual workflow_dispatch. After exact source
    # freeze they must be reproducible at the SAME H without editing a
    # workflow or manufacturing a triggering source commit. Both event types
    # still require original head/branch/workflow/job/attempt/artifact binding.
    require(run.get("id")==run_id and
            run.get("head_sha")==head and
            run.get("head_branch")==branch and
            run.get("event") in ("push","workflow_dispatch") and
            run.get("status")=="completed" and
            run.get("conclusion")=="success" and
            type(run.get("run_attempt")) is int and run["run_attempt"]>0 and
            (run.get("path")==spec["workflow"] or
             str(run.get("path","")).endswith("/"+spec["workflow"])),
            "original producer run not successful at this exact H")
    same=[job for job in jobs if isinstance(job,dict) and
          job.get("name")==spec["job"]+f" ({shard})" and
          job.get("head_sha")==head and
          job.get("run_id")==run_id and
          job.get("run_attempt")==run["run_attempt"] and
          job.get("status")=="completed" and
          job.get("conclusion")=="success" and
          str(job.get("check_run_url","")).endswith(
              "/check-runs/"+str(check["id"]))]
    require(len(same)==1, "source attempt/job/check aliasing or missing")
    producer=same[0]
    if match.group(2) is not None:
        require(int(match.group(2))==producer.get("id"),
                "check details links to a different original job")
    named=[a for a in artifacts if isinstance(a,dict) and
           a.get("name")==spec["artifact"]+str(shard) and
           a.get("expired") is False and
           (a.get("workflow_run") or {}).get("id")==run_id and
           (a.get("workflow_run") or {}).get("head_sha")==head]
    require(len(named)==1, "original artifact missing/duplicated or expired")
    artifact=named[0]
    stamps=[producer.get("started_at"),artifact.get("created_at"),
            producer.get("completed_at")]
    require(all(isinstance(x,str) and
                re.fullmatch(r"\d\d\d\d-\d\d-\d\dT\d\d:\d\d:\d\dZ",x)
                for x in stamps) and stamps[0]<=stamps[1]<=stamps[2],
            "original artifact not produced by current successful job attempt")
    require(type(artifact.get("id")) is int and artifact["id"]>0 and
            isinstance(artifact.get("digest"),str) and
            re.fullmatch(r"sha256:[0-9a-f]{64}",artifact["digest"]),
            "GitHub original artifact digest unavailable")
    return {
        "kind":kind,"shard":shard,"run_id":run_id,
        "run_attempt":run["run_attempt"],
        "job_id":producer["id"],
        "check_run_id":check["id"],
        "artifact_id":artifact["id"],
        "artifact_name":artifact["name"],
        "artifact_sha256":artifact["digest"][7:],
    }


def original_artifact_zip(artifact_id):
    """Download exact GitHub ZIP through the bounded all-hop source policy."""
    from pr113_boundary_io import github_artifact_zip
    token = os.environ.get("GITHUB_TOKEN")
    try:
        return github_artifact_zip(REPO, artifact_id, token, max_bytes=MAX_ZIP)
    except (OSError, ValueError) as exc:
        raise DiscoveryError("authentic original ZIP delivery unavailable") from exc


def collect(head, output, *, checks=None, lookup=live,
            paginate_source=paginate, download=original_artifact_zip):
    require(isinstance(head,str) and HEAD.fullmatch(head)
            and git_head()==head,
            "original 21 producer collection requires exact committed source")
    from pr113_boundary_io import detached_destination
    out=detached_destination(output, ROOT)
    require(not ROOT.resolve().is_relative_to(out),
            "original 21 producer input must not encompass source")
    from pr113_producer_target_v3 import authenticated_producer_branch
    # Genuine workflow execution is mandatory outside explicit test injection.
    branch=(authenticated_producer_branch(head)
            if checks is None else "research/final-mathematical-closure")
    candidates=classify_latest(
        paginate_source("/commits/"+head+"/check-runs",key="check_runs")
        if checks is None else checks,head)
    run_cache={}
    records=[]
    provenance=[]
    inputs={}
    total=0
    for kind,shard in sorted(candidates):
        check=candidates[(kind,shard)]
        url=check.get("details_url","")
        m=RUN_URL.fullmatch(url)
        require(m is not None, "original check-run has no source run ID")
        rid=int(m.group(1))
        if rid not in run_cache:
            run_cache[rid]=(
                lookup("/actions/runs/"+str(rid)),
                paginate_source("/actions/runs/"+str(rid)+"/jobs",key="jobs"),
                paginate_source("/actions/runs/"+str(rid)+"/artifacts",key="artifacts"),
            )
        run,jobs,artifacts=run_cache[rid]
        info=validate_run_job_artifact(
            head=head,kind=kind,shard=shard,
            check=check,run=run,jobs=jobs,artifacts=artifacts,
            branch=branch)
        raw=download(info["artifact_id"])
        total+=len(raw)
        require(total<=MAX_TOTAL and sha(raw)==info["artifact_sha256"],
                "original GH producer ZIP differed from authoritative digest")
        filename=str(info["artifact_id"])+".zip"
        require(filename not in inputs, "duplicate original artifact")
        inputs[filename]=raw
        records.append({
            "kind":kind,"shard":shard,"run_id":info["run_id"],
            "artifact_id":info["artifact_id"],"zip_file":filename,
        })
        provenance.append(info)
    require(len(records)==21 and len(inputs)==21,
            "full original 4+9+8 source artifact set not completed")
    # No output until ALL required original jobs and ZIPs authenticate.
    out.mkdir(parents=True,exist_ok=False)
    for name,raw in sorted(inputs.items()):
        (out/name).write_bytes(raw)
    manifest={"format":FORMAT,"head_sha":head,
              "artifacts":records}
    (out/"original21_catalog.json").write_text(
        json.dumps(manifest,sort_keys=True,indent=2)+"\n")
    (out/"source_execution_provenance.json").write_text(
        json.dumps({
            "format":"Permansson.PR113.RuntimeOriginal21Provenance.v1",
            "status":"ORIGINAL_21_GITHUB_PRODUCERS_PRESENT_UNREVIEWED",
            "source_head":head,"original_ci_sources":21,
            "actual_run_job_check_artifact_identities":provenance,
            "independent_case_review":False,
            "independent_claim_review":False,
            "publication_authorized":False,
        },sort_keys=True,indent=2)+"\n")
    return manifest


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args(argv)
    try:
        result=collect(a.head,a.out)
        print(json.dumps({"status":"ORIGINAL_21_RUNTIME_CATALOG_UNREVIEWED",
                          "artifacts":len(result["artifacts"])}))
        return 0
    except (DiscoveryError, AuthenticationError,ValueError,
            OSError,KeyError,TypeError) as exc:
        print("PR113 ORIGINAL21 LIVE CATALOG BLOCKED:",exc,file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
