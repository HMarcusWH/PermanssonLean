"""Extra PR113 source-control CI producer authentication, versioned v3.1.

The original 4+9+8 producing artifact set stays mandatory and unchanged.
New 45 positive case, 20 legacy negative and 11 claim true/false *pairs*
must each be traceable to the exact real CI job, check, downloaded artifact
and retained ZIP member bytes. This module NEVER grants security approval,
independent mathematical review, or publication. It does not install any
new GitHub workflow; reviewed owner/workflow mappings must be supplied by
a distinct authorized security process before a candidate can be checked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from pathlib import PurePosixPath
import re

from final_closure_authenticate import live, paginate
from final_closure_producer_bytes import inspect_zip, ProducerBytesError
from pr113_reviewed_producer_branch_v3 import (
    authentic_branch, ProducerBranchError,
)
from pr113_boundary_io import strict_json_object

FORMAT = "Permansson.PR113.ControlProducerExtension.v3.1"
INDEX_FORMAT = "Permansson.PR113.AdditionalControlProducerIndex.v1"
RESULT_FORMAT = "Permansson.PR113.ControlCIAuthenticationCandidate.v3.1"
ORIGINAL_FORMAT = "Permansson.PR113.ProducerBytesRevalidated.v1"
KINDS = ("original_positive", "legacy_negative", "claim_pair")
STATUS = {
    "original_positive": "SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED",
    "legacy_negative": "SOURCE_APPENDED_REPLAYED_UNREVIEWED_NOT_CI_ATTRIBUTED",
    "claim_pair": "LEAN_POSITIVE_AND_FALSE_MUTANT_EXECUTED_UNREVIEWED",
}
SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
BRANCH = "research/final-mathematical-closure"


class ControlProducerError(ValueError):
    pass


def need(ok, why):
    if not ok:
        raise ControlProducerError(why)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def expected_controls(original_case_ids, legacy_case_ids, claim_ids):
    """Original 45/20/11 owners are derived from original source inventories."""
    cases, legacy, claims = set(original_case_ids), set(legacy_case_ids), set(claim_ids)
    need(len(cases) == 45 and len(legacy) == 20 and legacy <= cases and
         len(claims) == 11 and len(claim_ids) == 11,
         "source-control owner inventory is not the immutable 45/20/11 scope")
    return {
        ("original_positive", cid) for cid in cases
    } | {
        ("legacy_negative", cid) for cid in legacy
    } | {
        ("claim_pair", cid) for cid in claims
    }


def candidate_registry(payload, head, expected):
    """Validate v3.1 shape before contacting GitHub. No synthetic approvals."""
    need(isinstance(payload, dict) and
         payload.get("format") == FORMAT and
         payload.get("head_sha") == head and
         isinstance(head, str) and SHA40.fullmatch(head) and
         isinstance(payload.get("original_21_producer_bundle_sha256"), str) and
         SHA256.fullmatch(payload["original_21_producer_bundle_sha256"]) and
         payload.get("original_producing_artifact_count") == 21 and
         payload.get("source_controls_accepted") is False and
         payload.get("independent_security_review") is False and
         payload.get("mathematical_approval") is False and
         payload.get("merged_main_sha") is None,
         "additional CI producer registry claims an unauthorized acceptance")
    jobs = payload.get("producers")
    need(isinstance(jobs, list) and jobs,
         "no exact H producing jobs registered")
    all_owners, artifacts = set(), set()
    for item in jobs:
        need(isinstance(item, dict) and set(item) == {
            "run_id","run_attempt","job_id","check_run_id","artifact_id",
            "artifact_name","artifact_sha256","workflow_path","job_name",
            "owner_index_member","owner_index_sha256","owners"},
            "malformed v3.1 job/check/artifact owner definition")
        for name in ("run_id","run_attempt","job_id","check_run_id","artifact_id"):
            need(type(item[name]) is int and item[name] > 0,
                 "untyped or forged producing identity: "+name)
        for name in ("artifact_sha256","owner_index_sha256"):
            need(isinstance(item[name],str) and SHA256.fullmatch(item[name]),
                 "untyped original producer SHA256")
        for name in ("artifact_name","workflow_path","job_name",
                     "owner_index_member"):
            need(isinstance(item[name],str) and item[name],
                 "producer missing required canonical name")
        need(item["workflow_path"].startswith(".github/workflows/") and
             item["workflow_path"].endswith((".yml",".yaml")) and
             ".." not in PurePosixPath(item["workflow_path"]).parts,
             "new producer workflow path escaped reviewed inventory")
        need(item["artifact_id"] not in artifacts,
             "artifact/check ownership cannot be duplicated")
        artifacts.add(item["artifact_id"])
        owned = item["owners"]
        need(isinstance(owned, list) and owned and
             all(isinstance(owner, dict) and
                 set(owner) == {"kind","owner_id","receipt_member","receipt_sha256"}
                 for owner in owned),
             "owner entries missing original member digests")
        for owner in owned:
            key = (owner["kind"],owner["owner_id"])
            need(key in expected and key not in all_owners and
                 isinstance(owner["receipt_member"],str) and
                 owner["receipt_member"] and
                 not owner["receipt_member"].startswith("/") and
                 ".." not in PurePosixPath(owner["receipt_member"]).parts and
                 isinstance(owner["receipt_sha256"],str) and
                 SHA256.fullmatch(owner["receipt_sha256"]),
                 "missing/duplicated/foreign control or noncanonical receipt")
            all_owners.add(key)
    need(all_owners == expected,
         "the complete 45/20/11 source-control owner partition is absent")
    return jobs


def authenticated_extra_controls(head, payload, zip_bytes, *,
                                 original_producers, original_bundle_sha256,
                                 expected, reviewed_workflow_blobs):
    """Reopen exact original GitHub producer ZIPs, no approval promotion.

    The reviewed workflow OIDs must be authenticated separately. A caller
    supplying an arbitrary OID does NOT grant the caller review authority;
    this method only reports source-attributed candidate bytes.
    """
    need(isinstance(original_producers, dict) and
         original_producers.get("format") == ORIGINAL_FORMAT and
         original_producers.get("status") ==
             "REAL_PRODUCING_BYTES_UNREVIEWED" and
         original_producers.get("head_sha") == head and
         original_producers.get("producer_count") == 21 and
         isinstance(original_bundle_sha256,str) and
         SHA256.fullmatch(original_bundle_sha256) and
         payload.get("original_21_producer_bundle_sha256") ==
             original_bundle_sha256,
         "original 21 producing artifact requirements were not authenticated")
    producers = candidate_registry(payload, head, expected)
    need(isinstance(zip_bytes, dict) and
         set(zip_bytes) == {x["artifact_id"] for x in producers},
         "missing/extra original new-control ZIP bytes")
    need(isinstance(reviewed_workflow_blobs,dict) and
         set(reviewed_workflow_blobs) ==
             {x["workflow_path"] for x in producers} and
         all(isinstance(v,str) and SHA40.fullmatch(v)
             for v in reviewed_workflow_blobs.values()),
         "new producer workflows have not been independently source-profiled")
    results, total = {}, 0
    verified_branch = None
    for job in producers:
        path = job["workflow_path"]
        # Real H must contain the reviewed producing workflow object; a
        # made-up filepath or current-only unpublished workflow will fail.
        source = live("/contents/"+path+"?ref="+head)
        need(isinstance(source,dict) and
             source.get("type") == "file" and
             source.get("sha") == reviewed_workflow_blobs[path],
             "actual GitHub H workflow object does not equal reviewed source")
        run = live("/actions/runs/"+str(job["run_id"]))
        if verified_branch is None:
            try:
                verified_branch = authentic_branch(
                    head, run.get("head_branch"), live=live)
            except ProducerBranchError as exc:
                raise ControlProducerError(
                    "current original-control producing branch not independently bound"
                ) from exc
        need(run.get("id") == job["run_id"] and
             run.get("head_sha") == head and
             run.get("head_branch") == verified_branch and
             run.get("run_attempt") == job["run_attempt"] and
             run.get("status") == "completed" and
             run.get("conclusion") == "success" and
             run.get("event") in ("push","workflow_dispatch") and
             (run.get("path") == path or
              str(run.get("path","")).endswith("/"+path)),
             "control producer run is not a genuine exact-H workflow")
        jobs = paginate("/actions/runs/"+str(job["run_id"])+"/jobs",key="jobs")
        match = [j for j in jobs if j.get("id") == job["job_id"] and
                 j.get("name") == job["job_name"]]
        need(len(match) == 1 and
             match[0].get("run_id") == job["run_id"] and
             match[0].get("run_attempt") == job["run_attempt"] and
             match[0].get("head_sha") == head and
             match[0].get("status") == "completed" and
             match[0].get("conclusion") == "success" and
             str(match[0].get("check_run_url","")).endswith(
                 "/check-runs/"+str(job["check_run_id"])),
             "case/claim control source borrowed unrelated producing CI job")
        check = live("/check-runs/"+str(job["check_run_id"]))
        need(check.get("id") == job["check_run_id"] and
             check.get("head_sha") == head and
             check.get("name") == job["job_name"] and
             check.get("status") == "completed" and
             check.get("conclusion") == "success" and
             (check.get("app") or {}).get("slug") == "github-actions",
             "actual source control producing check did not pass")
        artifact = live("/actions/artifacts/"+str(job["artifact_id"]))
        need(artifact.get("id") == job["artifact_id"] and
             artifact.get("name") == job["artifact_name"] and
             artifact.get("expired") is False and
             (artifact.get("workflow_run") or {}).get("id") == job["run_id"] and
             (artifact.get("workflow_run") or {}).get("head_sha") == head and
             artifact.get("digest") == "sha256:"+job["artifact_sha256"],
             "GitHub authoritative control ZIP SHA or producing run mismatch")
        raw = zip_bytes[job["artifact_id"]]
        need(type(raw) is bytes and sha(raw) == job["artifact_sha256"],
             "downloaded control ZIP was not the original producing artifact")
        total += len(raw)
        need(total <= 256*1024*1024,
             "aggregate new controls exceeded bounded ZIP budget")
        try:
            members = inspect_zip(raw)
        except ProducerBytesError as exc:
            raise ControlProducerError("unsafe producer ZIP member") from exc
        index_raw = members.get(job["owner_index_member"])
        need(index_raw is not None and
             sha(index_raw) == job["owner_index_sha256"],
             "original new-control producer ownership index missing/changed")
        try:
            index = strict_json_object(index_raw)
        except (ValueError,TypeError,UnicodeError) as exc:
            raise ControlProducerError("bad original new-control CI owner index") from exc
        need(index.get("format") == INDEX_FORMAT and
             index.get("head_sha") == head and
             index.get("github_run_id") == job["run_id"] and
             index.get("github_run_attempt") == job["run_attempt"] and
             index.get("accepted_cases") == 0 and
             index.get("accepted_claims") == 0 and
             index.get("independent_review") is False and
             index.get("owners") == job["owners"],
             "producing source falsely promoted acceptance or changed owner list")
        for owner in job["owners"]:
            record = members.get(owner["receipt_member"])
            need(record is not None and sha(record) == owner["receipt_sha256"],
                 "true owner record absent from retained producing CI ZIP")
            try:
                actual = strict_json_object(record)
            except (ValueError,TypeError,UnicodeError) as exc:
                raise ControlProducerError("malformed source control receipt") from exc
            need(actual.get("status") == STATUS[owner["kind"]] and
                 actual.get("head_sha") == head and
                 actual.get("case_id" if owner["kind"] != "claim_pair"
                            else "claim_id") == owner["owner_id"] and
                 actual.get("accepted_claim") is not True and
                 actual.get("independent_case_review") is not True and
                 actual.get("independent_mathematical_review") is not True and
                 actual.get("scientific_release_approved") is False,
                 "producer did not retain genuine unreviewed owner receipt")
            results[(owner["kind"],owner["owner_id"])] = {
                "artifact_id":job["artifact_id"],
                "check_run_id":job["check_run_id"],
                "receipt_member":owner["receipt_member"],
                "receipt_sha256":owner["receipt_sha256"],
                "source_status":"GITHUB_PRODUCED_NOT_INDEPENDENTLY_REVIEWED",
            }
    need(set(results) == expected,
         "one or more real source control CI owners disappeared")
    return {
        "format":RESULT_FORMAT,
        "status":"ALL_ADDITIONAL_CONTROLS_SOURCE_ATTRIBUTED_UNREVIEWED",
        "head_sha":head,
        "original_21_producing_artifacts_still_required":21,
        "additional_producing_artifacts":len(producers),
        "original_case_positives":45,
        "legacy_case_negatives":20,
        "claim_positive_negative_pairs":11,
        "source_owned_controls":[
            {"kind":kind,"owner_id":owner,**details}
            for (kind,owner),details in sorted(results.items())
        ],
        "schema_security_approved":False,
        "accepted_cases":0,"accepted_claims":0,
        "independent_mathematical_review":False,
        "full_release_approved":False,
    }


def assemble_review_pending(head, original_v3_receipts, original_v3_zip,
                            additional_contract_file, additional_zip_directory,
                            proposed_reviewed_workflow_blobs, output):
    """No local JSON can independently approve a workflow or mathematical claim.

    GH check ownership is revalidated live on both original and additional
    producers. The reviewed workflow OIDs argument supplies *candidate* source
    objects only. Actual security signoff remains external to this process.
    """
    from final_closure_authenticate import git
    from final_closure_case_receipts import (
        ROOT, load_detached_bundle, authenticate_v3_sources,
    )
    from final_closure_schema import validate_overlay
    from final_closure_legacy_semantic_evidence import original_case_map
    from final_closure_producer_v2_bridge import verified_producer_index

    need(git("rev-parse","HEAD")==head,
         "control extension must execute in its exact original H checkout")
    source_root=ROOT.resolve()
    def external(path, *, directory=False):
        given=Path(path)
        need(not given.is_symlink() and not any(
             p.is_symlink() for p in given.absolute().parents),
             "source/control evidence cannot use symlinked inputs")
        value=given.resolve(strict=True)
        need(not value.is_relative_to(source_root) and
             not source_root.is_relative_to(value) and
             (value.is_dir() if directory else value.is_file()),
             "original control evidence must be external to Git source")
        return value
    original_json=external(original_v3_receipts)
    original_zip=external(original_v3_zip)
    manifest_path=external(additional_contract_file)
    zip_dir=external(additional_zip_directory,directory=True)
    workflow_blobs_path=external(proposed_reviewed_workflow_blobs)
    out=Path(output)
    need(not out.is_symlink(),"detached output cannot be symlinked")
    out=out.resolve()
    need(not out.exists() and not out.is_relative_to(source_root) and
         not out.is_relative_to(zip_dir),
         "new control provenance output must be separate and fresh")
    original=strict_json_object(original_json.read_bytes(), max_bytes=8*1024*1024)
    validate_overlay(original)
    need(original.get("head_sha")==head and
         original.get("format")=="Permansson.FinalClosureDetachedReceipts.v3",
         "missing original strict v3 21-producer receipt")
    original_members=load_detached_bundle(
        original_zip,original["evidence_bundle_sha256"])
    from_original=authenticate_v3_sources(original,head,original_members)
    byid, legacy=original_case_map(head)
    claims=strict_json_object((source_root/"research/paper_closures/post_merge_112/"
                       "claim_declaration_map.json").read_bytes())
    expected=expected_controls(byid.keys(),legacy,
                               [x["claim_id"] for x in claims["claims"]])
    contract=strict_json_object(manifest_path.read_bytes())
    rows=candidate_registry(contract,head,expected)
    files={}
    for row in rows:
        candidate=zip_dir/(str(row["artifact_id"])+".zip")
        need(candidate.is_file() and not candidate.is_symlink() and
             candidate.resolve().parent==zip_dir,
             "original extra control ZIP not found by immutable artifact ID")
        files[row["artifact_id"]]=candidate.read_bytes()
    reviewed=strict_json_object(workflow_blobs_path.read_bytes())
    result=authenticated_extra_controls(
        head,contract,files,original_producers=from_original,
        original_bundle_sha256=original["evidence_bundle_sha256"],
        expected=expected,reviewed_workflow_blobs=reviewed)
    need(result["accepted_cases"]==0 and result["accepted_claims"]==0 and
         result["schema_security_approved"] is False and
         result["independent_mathematical_review"] is False,
         "additional source CI candidate cannot manufacture approval")
    # A genuine GitHub check and original ZIP digest are necessary but not
    # sufficient: the ZIP must actually contain source-positive test/Lean logs,
    # 20 appended-source semantic negatives and 11 claim true/false pairs.
    # This is still an execution-evidence candidate, NEVER review or approval.
    from pr113_v31_execution_integrity import (
        exact_source, validate_executed_controls,
    )
    real_controls = validate_executed_controls(
        head, contract, files, source=exact_source(head, source_root),
        original_producers=from_original)
    need(real_controls["source_owner_count"] == 76 and
         real_controls["claim_positive_negative_directions"] == 22 and
         real_controls["canonical_routes_bound"] is True and
         real_controls["legacy_original_captures_bound"] is True and
         real_controls["independent_review"] is False and
         real_controls["mathematical_acceptance"] is False,
         "actual 76 original source-control execution bytes not authenticated")
    result["actual_execution_member_validation"] = real_controls

    out.parent.mkdir(parents=True,exist_ok=True)
    with out.open("x",encoding="utf-8") as writer:
        writer.write(json.dumps(result,sort_keys=True,indent=2)+"\n")
    return result


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head",required=True)
    parser.add_argument("--original-v3-receipts",required=True,type=Path)
    parser.add_argument("--original-v3-zip",required=True,type=Path)
    parser.add_argument("--additional-contract",required=True,type=Path)
    parser.add_argument("--additional-zips",required=True,type=Path)
    parser.add_argument("--reviewed-workflow-blob-candidates",
                        required=True,type=Path)
    parser.add_argument("--output",required=True,type=Path)
    options=parser.parse_args(argv)
    try:
        output=assemble_review_pending(
            options.head,options.original_v3_receipts,
            options.original_v3_zip,options.additional_contract,
            options.additional_zips,
            options.reviewed_workflow_blob_candidates,options.output)
    except (ControlProducerError,OSError,ValueError,TypeError,KeyError) as exc:
        print("ADDITIONAL SOURCE CONTROL PRODUCER AUTHENTICATION BLOCKED:",
              exc,file=sys.stderr)
        return 2
    print(json.dumps({"format":output["format"],
                      "status":output["status"],
                      "additional_owners":len(output["source_owned_controls"]),
                      "original_required_producers":21},sort_keys=True))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
