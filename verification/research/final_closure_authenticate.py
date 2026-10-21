"""Independent GitHub/Git-object authentication for final mathematical release.

Never promote an arbitrary JSON flag, SHA-shaped string, reviewer name or
self-reported CI event. No network or missing objects -> strict rejection.
Offline draft/audit modes never use this module.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import re
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "https://api.github.com/repos/HMarcusWH/PermanssonLean"
BASE = "17c315f7df7abf457eb94d393bd526d46da6f6f4"
SHA = re.compile(r"^[0-9a-f]{40}$")
REQUIRED = frozenset((
    "research", "build", "frozen-source-preservation",
    "multiagent-protocols", "approx-quotient",
    "release-export-integrity", "archive-reproducibility",
))


class AuthenticationError(ValueError):
    pass


def demand(ok, message):
    if not ok:
        raise AuthenticationError(message)


def git(*args):
    try:
        return subprocess.check_output(["git", *args], cwd=ROOT,
                text=True, stderr=subprocess.DEVNULL, timeout=20).strip()
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise AuthenticationError("missing authentic Git object: " + " ".join(args)) from exc


def live(path):
    """Only literal GitHub repo endpoints constructed by this module."""
    headers = {"User-Agent": "Permansson-Closure-Acceptance/1",
               "Accept": "application/vnd.github+json"}
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = "Bearer " + token
    req = urllib.request.Request(PREFIX+path, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=20) as response:
            return json.load(response)
    except Exception as exc:
        raise AuthenticationError("live GitHub authentication unavailable: " + path) from exc


def verify_source(receipts):
    b,h,s,m = (receipts.get(x) for x in
                ("base_sha","head_sha","synthetic_sha","merged_main_sha"))
    for name,value in zip("BHSM",(b,h,s,m)):
        demand(isinstance(value,str) and SHA.fullmatch(value),
               "missing real "+name+" SHA")
        demand(git("cat-file","-t",value)=="commit",name+" is not a Git commit")
    demand(b==BASE,"wrong original branch base")
    demand(git("show","-s","--format=%P",s).split()==[b,h],
           "synthetic Git parents differ from original B/H")
    demand(git("rev-parse",s+"^{tree}")==git("rev-parse",m+"^{tree}"),
           "synthetic and merged final trees differ")
    git("merge-base","--is-ancestor",b,m)
    git("merge-base","--is-ancestor",h,m)
    pr=live("/pulls/113")
    demand(pr.get("number")==113 and pr.get("merged") is True,
           "the PR must be truly merged for final acceptance")
    demand(pr["base"]["sha"]==b and pr["head"]["sha"]==h
           and pr.get("merge_commit_sha")==m,
           "live GitHub PR B/H/M differs from claimed receipts")
    runs=live("/commits/"+h+"/check-runs?per_page=100")["check_runs"]
    accepted={x["name"]:x for x in runs if
              x.get("head_sha")==h and x.get("conclusion")=="success"
              and x.get("status")=="completed"}
    demand(REQUIRED <= accepted.keys(),"missing genuine source-bound CI checks")
    given=receipts.get("source_bound_ci",[])
    demand(isinstance(given,list),"CI receipts must be source-bound entries")
    for name in REQUIRED:
        cert=accepted[name]
        demand(any(isinstance(x,dict) and x.get("name")==name
                   and x.get("id")==cert.get("id") and x.get("head_sha")==h
                   for x in given),
               "not a live source-bound CI receipt: "+name)
    approvals=live("/pulls/113/reviews?per_page=100")
    author=(pr.get("user") or {}).get("login")
    reviewer_ids={x.get("id") for x in approvals if
                  x.get("state")=="APPROVED" and x.get("commit_id")==h
                  and x.get("submitted_at") and x.get("user")
                  and x["user"].get("login")!=author}
    reviews=receipts.get("independent_source_reviews",[])
    demand(bool(reviewer_ids) and isinstance(reviews,list) and
           any(isinstance(x,dict) and x.get("id") in reviewer_ids
               for x in reviews),
           "independent reviewer approval on exact H not authenticated")
    return {"B":b,"H":h,"S":s,"M":m,"reviewer_ids":reviewer_ids}
