"""Execute exactly 11 claim-owned positive and false Lean controls.

Authoritative mathematical interpretation requires independent reviewers.
Selections and submitted append-only false source files MUST be explicitly
chosen; this script never invents a false statement or substitutes a
case-specific mutant for a claim-only obligation. It executes real named
unittest methods and pinned Lean 4.34.0, retaining original exact-H bytes.
Its outputs have NO producing GitHub check identity and NO accepted claims.
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

from final_closure_mutation_evidence import (
    ROOT, committed_file_bytes, git_head, lean_result,
    pinned_lean_version, verify_negative, seal_logs,
    MutationEvidenceError,
)
from final_closure_positive_route_candidate import source_method
from final_closure_case_receipts import INVALID_DIAGNOSTICS
from final_closure_producer_v2_bridge import SHA40

FORMAT = "Permansson.PR113.ClaimControlsCandidate.v1"
SELECTION = "Permansson.PR113.ClaimControlSelection.v1"
CLAIMS = frozenset(("Q1","Q2","Q3","M1","M2","M3",
                    "N1","N2","N3","D8","D9"))
MAX_LOG_BYTES = 4*1024*1024


class ClaimControlError(ValueError):
    pass


def demand(ok, msg):
    if not ok:raise ClaimControlError(msg)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def selection_map(payload, claims):
    require_keys = {
        "claim_id","proof_source_path","positive_test_path",
        "positive_test_class","positive_test_method",
        "negative_test_path","negative_test_class","negative_test_method",
    }
    demand(isinstance(payload,dict) and payload.get("format")==SELECTION and
           isinstance(payload.get("claims"),list) and
           isinstance(claims,dict) and set(claims)==CLAIMS,
           "all eleven exact-source claim selections required")
    result={}
    for row in payload["claims"]:
        demand(isinstance(row,dict) and set(row)==require_keys,
               "unknown/forged claim control selection keys")
        cid=row["claim_id"]
        demand(cid in claims and cid not in result,
               "missing, duplicated or foreign mathematical claim")
        proof_path=row["proof_source_path"]
        demand(isinstance(proof_path,str) and
               any(s.get("path")==proof_path for s in
                   claims[cid].get("declarations",[])),
               "claim selected a foreign original Lean provider")
        candidates=claims[cid].get("test_source_candidates",[])
        demand(all(row[k] in candidates for k in
                   ("positive_test_path","negative_test_path")) and
               row["positive_test_method"] != row["negative_test_method"],
               "claim uses wrong selected source or reused one test method")
        result[cid]=row
    demand(set(result)==CLAIMS,
           "at least one original new claim has no positive/negative selection")
    return result


def named_method(head,path,cls,method):
    return source_method(head,path,cls,method)


def run_test(path, cls, method):
    environment=os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"]="1"
    environment["PYTHONPATH"]=(str(ROOT/"verification/research") +
                                os.pathsep + str(ROOT) +
                                os.pathsep + environment.get("PYTHONPATH",""))
    qualified=Path(path).stem+"."+cls+"."+method
    try:
        result=subprocess.run(
            [sys.executable,"-B","-m","unittest",qualified,"-v"],
            cwd=ROOT,env=environment,capture_output=True,timeout=900)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise ClaimControlError("named claim test was unavailable") from exc
    demand(result.returncode==0 and
           b"Ran 1 test" in result.stderr and b"OK" in result.stderr and
           b"skipped=" not in result.stderr and
           b"expected failures=" not in result.stderr and
           len(result.stdout)+len(result.stderr) <= MAX_LOG_BYTES,
           "named claim test failed or did not execute exactly one method")
    return result


def execute(head, selections, mutant_root, output):
    demand(isinstance(head,str) and SHA40.fullmatch(head) and
           git_head()==head,"claim controls must use current genuine exact H")
    select=Path(selections)
    mutants=Path(mutant_root)
    target=Path(output)
    demand(select.is_file() and not select.is_symlink() and
           not select.resolve().is_relative_to(ROOT.resolve()) and
           mutants.is_dir() and not mutants.is_symlink() and
           not mutants.resolve().is_relative_to(ROOT.resolve()) and
           not target.is_symlink() and not target.resolve().exists() and
           not target.resolve().is_relative_to(ROOT.resolve()),
           "claim selection, original mutants and output must be disjoint external paths")
    canonical=ROOT/"research/paper_closures/post_merge_112/claim_declaration_map.json"
    manifest=json.loads(committed_file_bytes(head,canonical,root=ROOT))
    names={row["claim_id"]:row for row in manifest["claims"]}
    chosen=selection_map(json.loads(select.read_bytes()),names)
    version=pinned_lean_version(head)
    target=target.resolve()
    target.mkdir(parents=True,exist_ok=False)
    executed=[]
    for cid,row in sorted(chosen.items()):
        original_path=row["proof_source_path"]
        original=committed_file_bytes(head,ROOT/original_path,root=ROOT)
        mutant_file=mutants/(cid+".lean")
        demand(mutant_file.is_file() and not mutant_file.is_symlink() and
               mutant_file.resolve().parent==mutants.resolve(),
               "exact claim mutant source was not provided: "+cid)
        altered=mutant_file.read_bytes()
        demand(len(altered)>len(original) and altered.startswith(original) and
               len(altered)<=MAX_LOG_BYTES and
               b"\r" not in altered,
               "claim mutant was not append-only to genuine original Lean source")
        append=altered[len(original):].decode("utf-8")
        demand(not re.search(
            r"(?mi)^\s*(?:import|axiom|constant|opaque|set_option)\b",append)
            and not re.search(r"(?i)\b(?:sorry|sorryAx|admit)\b",append),
            "claim false assertion changed imports, axiom, options or admissions")
        positive_test=named_method(
            head,row["positive_test_path"],row["positive_test_class"],
            row["positive_test_method"])
        negative_test=named_method(
            head,row["negative_test_path"],row["negative_test_class"],
            row["negative_test_method"])
        positive_test_result=run_test(
            row["positive_test_path"],row["positive_test_class"],
            row["positive_test_method"])
        negative_test_result=run_test(
            row["negative_test_path"],row["negative_test_class"],
            row["negative_test_method"])
        lean_positive=lean_result(ROOT/original_path)
        lean_negative=lean_result(mutant_file)
        verify_negative(lean_positive,lean_negative,original,altered)
        demand(committed_file_bytes(head,ROOT/original_path,root=ROOT)==original
               and committed_file_bytes(head,ROOT/row["positive_test_path"],root=ROOT)
                  ==positive_test and
               committed_file_bytes(head,ROOT/row["negative_test_path"],root=ROOT)
                  ==negative_test and mutant_file.read_bytes()==altered,
               "claim source/test or false assertion changed during execution")
        path=target/cid
        path.mkdir()
        member={
            "original.lean":original,
            "appended_false.lean":altered,
            "positive_lean.log":(lean_positive.stdout+"\n"+lean_positive.stderr).encode(),
            "negative_lean.log":(lean_negative.stdout+"\n"+lean_negative.stderr).encode(),
            "positive_test.stdout":positive_test_result.stdout,
            "positive_test.stderr":positive_test_result.stderr,
            "negative_test.stdout":negative_test_result.stdout,
            "negative_test.stderr":negative_test_result.stderr,
        }
        for name,raw in member.items():
            demand(len(raw)<=MAX_LOG_BYTES,
                   "captured original claim diagnostic exceeded bound")
            (path/name).write_bytes(raw)
        record={
            "format":"Permansson.PR113.ClaimOnlyControlCandidate.v1",
            "status":"LEAN_POSITIVE_AND_FALSE_MUTANT_EXECUTED_UNREVIEWED",
            "claim_id":cid,"case_ids":[],"claim_ids":[cid],
            "head_sha":head,"original_lean_source_path":original_path,
            "positive_test_path":row["positive_test_path"],
            "positive_test_name":row["positive_test_method"],
            "negative_test_path":row["negative_test_path"],
            "negative_test_name":row["negative_test_method"],
            "lean_version":version,
            "lean_positive_exit_code":lean_positive.returncode,
            "lean_negative_exit_code":lean_negative.returncode,
            "source_test_hashes":{
                "positive":sha(positive_test),"negative":sha(negative_test)},
            "retained_member_sha256":{name:sha(raw) for name,raw in member.items()},
            "actual_ci_check_run_id":None,
            "independent_mathematical_review":False,
            "accepted_claim":False,
            "scientific_release_approved":False,
        }
        (path/"unreviewed_claim_control.json").write_text(
            json.dumps(record,sort_keys=True,indent=2)+"\n")
        executed.append(record)
    demand(len(executed)==11,"not all eleven claim false mutants ran")
    summary={
        "format":FORMAT,
        "status":"ALL_ELEVEN_EXECUTED_UNREVIEWED_NO_CI_ATTRIBUTION",
        "source_head":head,"actual_new_claims_executed":11,
        "claim_controls":executed,
        "actual_producing_ci_check_run_id":None,
        "independent_claim_reviews":0,
        "mathematical_release_approved":False,
    }
    (target/"unreviewed_11_claim_control_summary.json").write_text(
        json.dumps(summary,sort_keys=True,indent=2)+"\n")
    return summary


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--selection",required=True,type=Path)
    p.add_argument("--mutants-root",required=True,type=Path)
    p.add_argument("--out",required=True,type=Path)
    a=p.parse_args(argv)
    try:
        report=execute(a.head,a.selection,a.mutants_root,a.out)
    except (ClaimControlError,MutationEvidenceError,OSError,ValueError,
            KeyError,TypeError,UnicodeError) as exc:
        print("PR113 CLAIM CONTROL EXECUTION BLOCKED:",exc,file=sys.stderr)
        return 2
    print(json.dumps({"status":report["status"],
                      "claims":report["actual_new_claims_executed"]}))
    return 0

if __name__=="__main__":
    raise SystemExit(main())
