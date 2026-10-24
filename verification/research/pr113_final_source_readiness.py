"""Read-only PR113 exact-H candidate readiness; never authorizes merge/release.

Requires all 12 genuine required CI contexts, every real 4+9+8 producing ZIP,
259 source types, individually owned positive/negative controls for all
45 original criteria AND 11 claims, and authentic B/H/S topology. Test
registration or legacy Python observations cannot replace source-positive/
negative execution. Reviewer approvals remain a distinct later gate.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from final_closure_authenticate import BASE, REQUIRED, authenticated_checks, git
from final_closure_case_receipts import (
    FORMAT_V3, load_detached_bundle, authenticate_v3_sources, EvidenceError)
from final_closure_schema import validate_overlay
from final_closure_complete_lean_evidence import ROOT

CLAIMS=frozenset(("Q1","Q2","Q3","M1","M2","M3","N1","N2","N3","D8","D9"))

class ReadinessError(ValueError):
    pass

def demand(ok,message):
    if not ok:raise ReadinessError(message)

def candidate_coverage(overlay,original_ids):
    demand(isinstance(overlay,dict) and overlay.get("format")==FORMAT_V3 and
           isinstance(original_ids,set) and len(original_ids)==45,
           "original strict-v3/45-case source inventory unavailable")
    proofs=overlay.get("compiler_axiom_receipts",[])
    plus=overlay.get("positive_test_receipts",[])
    minus=overlay.get("semantic_negative_receipts",[])
    producers=overlay.get("producer_artifacts",[])
    demand(len(proofs)==259 and
           len({r.get("id") for r in proofs})==259 and
           len(producers)==21 and
           len({r.get("artifact_id") for r in producers})==21,
           "missing 259 exact theorem owners or 21 authentic producer entries")
    proof_owners={k for row in proofs for k in row.get("case_ids",[])}
    claim_owners={k for row in proofs for k in row.get("claim_ids",[])}
    demand(proof_owners==original_ids and claim_owners==CLAIMS,
           "canonical 45 original/11 claim theorem source coverage incomplete")
    pp={k for row in plus for k in row.get("case_ids",[])}
    pm={k for row in minus for k in row.get("case_ids",[])}
    cp={k for row in plus for k in row.get("claim_ids",[])}
    cm={k for row in minus for k in row.get("claim_ids",[])}
    missing_cases=sorted(original_ids - (pp & pm))
    missing_claims=sorted(CLAIMS - (cp & cm))
    demand(not (pp|pm)-original_ids and not (cp|cm)-CLAIMS,
           "foreign case/claim controls were inserted")
    return {
        "format":"Permansson.PR113.ReadinessGapAnalysis.v1",
        "source_proofs":259,"producer_shards":21,
        "cases_with_positive_negative_controls":len(original_ids)-len(missing_cases),
        "claims_with_positive_negative_controls":len(CLAIMS)-len(missing_claims),
        "missing_original_case_controls":missing_cases,
        "missing_new_claim_controls":missing_claims,
        "candidate_controls_complete":not missing_cases and not missing_claims,
        "independent_case_reviews":0,
        "independent_claim_reviews":0,
        "merge_authorized":False,"mathematical_release_approved":False,
    }

def inspect(head,synthetic,source_receipts,source_zip):
    demand(git("rev-parse","HEAD")==head and
           git("rev-parse","main")==BASE and
           git("show","-s","--format=%P",synthetic).split()==[BASE,head] and
           git("rev-parse",synthetic+"^{tree}")==
           git("rev-parse",head+"^{tree}"),
           "B/H/S identities do not bind exact frozen source tree")
    receipts=json.loads(Path(source_receipts).read_bytes())
    validate_overlay(receipts)
    demand(receipts.get("head_sha")==head and
           receipts.get("phase")=="premerge_review" and
           receipts.get("merged_main_sha") is None and
           not receipts.get("case_decisions") and
           not receipts.get("claim_decisions"),
           "premerge readiness cannot contain fake M or self-awarded reviews")
    checks=authenticated_checks(head)
    demand(set(checks)>=set(REQUIRED) and
           all(any(row.get("name")==name and
                   row.get("head_sha")==head and
                   row.get("id")==checks[name]["id"]
                   for row in receipts["source_bound_ci"])
               for name in REQUIRED),
           "required exact-H CI incomplete, stale or forged")
    members=load_detached_bundle(
        source_zip,receipts["evidence_bundle_sha256"])
    producer=authenticate_v3_sources(receipts,head,members)
    demand(producer.get("producer_count")==21,
           "complete original ZIP provenance unavailable")
    original=json.loads((ROOT/"research/paper_closures/post_merge_112/"
                         "acceptance_decisions.json").read_bytes())
    ids={row["case_id"] for row in original["cases"]}
    report=candidate_coverage(receipts,ids)
    demand(report["candidate_controls_complete"],
           "unreviewed source candidate still lacks case/claim positive-negative "+
           "controls: "+json.dumps({
               "cases":report["missing_original_case_controls"],
               "claims":report["missing_new_claim_controls"]},sort_keys=True))
    return {
        **report,"source_head":head,"synthetic_sha":synthetic,
        "status":"COMPLETE_SOURCE_EVIDENCE_UNREVIEWED_NOT_ACCEPTED",
        "exact_head_required_ci":12,
        "actual_github_producer_shards":21,
        "merge_authorized":False,"scholarly_review_approved":False,
    }

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--synthetic",required=True)
    p.add_argument("--receipts",type=Path,required=True)
    p.add_argument("--bundle",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args(argv)
    try:
        out=Path(a.out)
        demand(not out.exists() and not out.is_symlink() and
               not out.resolve().is_relative_to(ROOT.resolve()),
               "readiness output must be new and detached")
        verdict=inspect(a.head,a.synthetic,a.receipts,a.bundle)
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(verdict,sort_keys=True,indent=2)+"\n")
        print(json.dumps(verdict,sort_keys=True))
        return 0
    except (ReadinessError,EvidenceError,OSError,KeyError,ValueError) as exc:
        print("PR113 EXACT-H READINESS BLOCKED:",exc,file=sys.stderr)
        return 2
if __name__=="__main__":
    raise SystemExit(main())
