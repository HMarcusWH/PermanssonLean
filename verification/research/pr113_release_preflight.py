"""PR113 detached B/H/T baseline snapshot, deliberately NOT a release gate.

A stable engineering preflight for the original 45 obligations, 11 claim IDs,
259 complete source-owner compiler targets, preserved T tooling and original
A2 proof blobs. Both underlying archived verifiers must still run and obtain
genuine independent security authorization before their successor integration.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from final_closure_complete_lean_evidence import ROOT, required_inventory
from final_closure_authenticate import BASE, git
from final_closure_case_receipts import digest
from pr113_tooling_migration import audit as tooling_audit
from pr113_a2_successor_identity import audit as a2_audit

CLAIMS = frozenset(("Q1","Q2","Q3","M1","M2","M3","N1","N2","N3","D8","D9"))

class BaselineError(ValueError):
    pass

def need(ok, message):
    if not ok:
        raise BaselineError(message)

def frozen_scope(case_ledger, claim_map, records):
    cases=case_ledger.get("cases") if isinstance(case_ledger,dict) else None
    claims=claim_map.get("claims") if isinstance(claim_map,dict) else None
    need(isinstance(cases,list) and len(cases)==45 and
         len({c.get("case_id") for c in cases if isinstance(c,dict)})==45,
         "original acceptance cases were removed, duplicated or altered")
    need(isinstance(claims,list) and len(claims)==11 and
         {c.get("claim_id") for c in claims if isinstance(c,dict)}==CLAIMS,
         "eleven mathematical claim owners were replaced")
    need(isinstance(records,list) and len(records)==259 and
         len({(r.get("path"),r.get("declaration")) for r in records
              if isinstance(r,dict)})==259,
         "canonical 259 theorem owner inventory incomplete")
    owners={c for r in records for c in r.get("case_ids",[])}
    cids={c for r in records for c in r.get("claim_ids",[])}
    need(owners=={c["case_id"] for c in cases} and cids==CLAIMS,
         "proof inventory lost original case/claim ownership")
    return {
        "original_case_count":45,
        "original_case_ids":sorted(c["case_id"] for c in cases),
        "claim_count":11,"claim_ids":sorted(CLAIMS),
        "compiler_target_count":259,
        "distinct_proof_declarations":259,
    }

def baseline(head, outfile):
    output=Path(outfile)
    need(not output.is_symlink(), "baseline output cannot be symlinked")
    output=output.resolve()
    root=ROOT.resolve()
    need(not output.exists() and not output.is_relative_to(root) and
         not root.is_relative_to(output),
         "baseline must be a new source-external output")
    need(git("rev-parse","HEAD")==head and
         git("cat-file","-t",head)=="commit" and
         git("cat-file","-t",BASE)=="commit",
         "no authentic exact-H and B Git commits")
    original=json.loads((root/"research/paper_closures/post_merge_112/"
                         "acceptance_decisions.json").read_bytes())
    claim=json.loads((root/"research/paper_closures/post_merge_112/"
                      "claim_declaration_map.json").read_bytes())
    inventory=required_inventory()
    scoped=frozen_scope(original,claim,inventory)
    historic=tooling_audit(root,head)
    a2=a2_audit(root,head)
    need(historic["status"]=="DRAFT_NEEDS_OWNER_AND_INDEPENDENT_SECURITY_REVIEW"
         and historic["historical_archive_unchanged"] is True
         and a2["status"]=="SOURCE_IDENTITY_CANDIDATE_NEEDS_INDEPENDENT_SECURITY_REVIEW"
         and a2["successor_delta"]["accepted_a2_proof_blobs"]==4,
         "original T or A2 source preservation was weakened")
    policy=json.loads((root/"research/paper_closures/post_merge_112/"
                       "reviewer_authority.json").read_bytes())
    report={
        "format":"Permansson.PR113.ExactSourceBaseline.v1",
        "status":"SOURCE_IDENTITY_ONLY_ALL_APPROVALS_PENDING",
        "B":BASE,"H":head,
        "B_tree":git("rev-parse",BASE+"^{tree}"),
        "H_tree":git("rev-parse",head+"^{tree}"),
        "original_acceptance_sha256":digest(json.dumps(
            original,sort_keys=True,separators=(",",":")).encode()),
        "claim_owner_sha256":digest(json.dumps(
            claim,sort_keys=True,separators=(",",":")).encode()),
        **scoped,
        "historical_tooling_diff":historic["changed_canonical_tooling"],
        "historical_archive_source_unchanged":True,
        "A2_historical_proof_blobs":4,
        "A2_original_verifier_untouched":True,
        "original_security_review":False,
        "T2_independent_security_review":False,
        "A2_independent_security_review":False,
        "reviewer_authority_status":policy.get("status"),
        "independent_case_reviews_authenticated":0,
        "independent_claim_reviews_authenticated":0,
        "real_M":None,"paper_release_approved":False,
    }
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open("x",encoding="utf-8") as writer:
        writer.write(json.dumps(report,sort_keys=True,indent=2)+"\n")
    return report

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--output",type=Path,required=True)
    a=p.parse_args(argv)
    try:
        r=baseline(a.head,a.output)
        print(json.dumps({"status":r["status"],"H":r["H"],
                          "proof_count":r["compiler_target_count"]}))
        return 0
    except (BaselineError,ValueError,KeyError,OSError) as exc:
        print("PR113 BASELINE BLOCKED:",exc,file=sys.stderr)
        return 2
if __name__=="__main__":
    raise SystemExit(main())
