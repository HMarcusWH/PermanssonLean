"""Batch execute twenty *real*, source-appended A2/legacy Lean replays.

The eight old legacy shard ZIPs retain test/compiler observations; these are
not canonical append-only proof controls. A reviewer/operator must explicitly
supply the selected historical method, genuine observed false input and correct
original theorem provider per case. This program verifies those source choices
against original frozen case criteria and runs the existing actual Lean
legacy_replay.replay for each case. It never attaches arbitrary CI check IDs,
case decisions, scholarly approvals or release eligibility.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
import tempfile

from final_closure_complete_lean_evidence import ROOT, git_head
from final_closure_mutation_evidence import committed_file_bytes
from final_closure_legacy_semantic_evidence import original_case_map
from final_closure_producer_v2_bridge import verified_producer_index
from final_closure_producer_bytes import authenticate
from final_closure_legacy_replay import replay as actual_replay
from final_closure_authenticate import AuthenticationError

FORMAT="Permansson.PR113.LegacyBatchAppendOnlyCandidate.v1"
TEST=re.compile(r"^test_[A-Za-z0-9_]+$")
EVENT=re.compile(r"^[A-Za-z0-9_-]+$")


class LegacyBatchError(ValueError):
    pass

def require(ok,why):
    if not ok:raise LegacyBatchError(why)

def parse_mapping(data, expected):
    require(isinstance(data,dict) and
            data.get("format")=="Permansson.PR113.LegacyReplaySelection.v1"
            and isinstance(data.get("cases"),list) and
            isinstance(expected,set) and len(expected)==20,
            "twenty original legacy case selections required")
    records={}
    keys={"case_id","test_index","test_method","original_provider",
          "observation_id","producing_artifact_id"}
    for row in data["cases"]:
        require(isinstance(row,dict) and set(row)==keys,
                "untypeable selected legacy provider/method/observation")
        cid=row["case_id"]
        require(cid in expected and cid not in records and
                type(row["test_index"]) is int and row["test_index"]>=0 and
                type(row["producing_artifact_id"]) is int and
                row["producing_artifact_id"]>0 and
                type(row["test_method"]) is str and
                TEST.fullmatch(row["test_method"]) and
                type(row["observation_id"]) is str and
                EVENT.fullmatch(row["observation_id"]) and
                type(row["original_provider"]) is str and
                row["original_provider"].startswith("PermanssonResearch/") and
                row["original_provider"].endswith(".lean") and
                ".." not in Path(row["original_provider"]).parts,
                "unknown, duplicated or unsafe source-negative replay selection")
        records[cid]=row
    require(set(records)==expected,
            "selected legacy provider map misses original acceptance criteria")
    return records

def external_directory(path):
    raw=Path(path)
    require(not raw.is_symlink(),"symlinked legacy artifact path not allowed")
    result=raw.resolve(strict=True)
    require(result.is_dir() and
            not result.is_relative_to(ROOT.resolve()) and
            not ROOT.resolve().is_relative_to(result),
            "all evidence inputs must be source-external directories")
    return result

def replay_twenty(head, catalog_root, producer_zip_root, mapping_path, out):
    require(git_head()==head,"replays cannot borrow a historical source head")
    catalog=external_directory(catalog_root)
    producers=external_directory(producer_zip_root)
    mapping_file=Path(mapping_path)
    require(mapping_file.is_file() and not mapping_file.is_symlink() and
            not mapping_file.resolve().is_relative_to(ROOT.resolve()),
            "explicit legacy provider selection must be detached")
    target=Path(out)
    require(not target.is_symlink(),"symlink output forbidden")
    target=target.resolve()
    require(not target.exists() and
            not target.is_relative_to(ROOT.resolve()) and
            not target.is_relative_to(catalog) and
            not target.is_relative_to(producers),
            "replay output must be fresh and separate")
    byid, legacy=original_case_map(head)
    legacy_ids=set(legacy)
    chosen=parse_mapping(json.loads(mapping_file.read_bytes()),legacy_ids)
    report=json.loads(
        (catalog/"unreviewed_producer_catalog.json").read_bytes())
    require(report.get("head_sha")==head and
            report.get("producing_artifact_count")==21,
            "original authenticated producer index unavailable")
    attests=report["producer_artifact_checks"]
    indexed=verified_producer_index(head,attests)
    raw={}
    for row in attests:
        path=producers/(str(row["artifact_id"])+".zip")
        require(path.is_file() and not path.is_symlink(),
                "missing original GitHub producer ZIP")
        data=path.read_bytes()
        from hashlib import sha256
        require(sha256(data).hexdigest()==row["artifact_sha256"],
                "producer ZIP changed since authenticated GitHub artifact")
        raw[row["artifact_id"]]=data
    authentic=authenticate(head,attests,raw)
    require(authentic["producer_count"]==21,
            "21 original compiler/append/legacy source jobs not authenticated")
    legacy_artifacts={p["artifact_id"]:(kind,shard,p)
                      for (kind,shard),p in indexed.items() if kind=="legacy"}
    for row in chosen.values():
        require(row["producing_artifact_id"] in legacy_artifacts,
                "legacy replay borrowed append/compiler producing artifact")
    target.mkdir(parents=True,exist_ok=False)
    completed={}
    for cid in sorted(chosen):
        row=chosen[cid]
        member=authentic["producers"][row["producing_artifact_id"]]["members"]
        prefix=f'{cid}/test-{row["test_index"]:02d}/'
        manifest_key=prefix+"unreviewed_test_manifest.json"
        require(manifest_key in member,
                "selected named historical test capture is missing")
        original_manifest=json.loads(member[manifest_key])
        require(original_manifest.get("case_id")==cid and
                row["test_method"] in original_manifest.get("selected_methods",[])
                and original_manifest.get("status")==
                    "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED",
                "selected legacy test is not an actually observed source method")
        with tempfile.TemporaryDirectory(prefix="pr113-legacy-source-") as td:
            input_dir=Path(td)/"original_capture"
            input_dir.mkdir()
            for name,data in member.items():
                if name.startswith(prefix):
                    suffix=name[len(prefix):]
                    require(suffix and ".." not in Path(suffix).parts,
                            "unsafe legacy source capture input")
                    file=input_dir/suffix
                    file.parent.mkdir(parents=True,exist_ok=True)
                    file.write_bytes(data)
            result=actual_replay(
                head,case_id=cid,method=row["test_method"],
                provider=row["original_provider"],
                observation_id=row["observation_id"],
                test_output=input_dir,
                output=target/cid)
        require(result.get("format")==
                "Permansson.LegacyAppendOnlyReplayCandidate.v1" and
                result.get("status")==
                "REPLAYED_APPEND_ONLY_UNREVIEWED_UNATTRIBUTED" and
                result.get("head_sha")==head and
                result.get("case_id")==cid and
                result.get("ci_check_run_id") is None and
                result.get("independent_review") is False and
                result.get("mathematical_acceptance") is False,
                "actual original theorem replay failed to prove its source scope")
        completed[cid]={
            "case_id":cid,
            "original_legacy_producing_artifact_id":row["producing_artifact_id"],
            "original_legacy_check_run_id_provenance_only":
                legacy_artifacts[row["producing_artifact_id"]][2]["actual_check_run_id"],
            "replay_bundle_sha256":result["detached_bundle_sha256"],
            "new_replay_producer_check_run_id":None,
            "status":"SOURCE_APPENDED_REPLAYED_UNREVIEWED_NOT_CI_ATTRIBUTED",
        }
    require(len(completed)==20,"not all original twenty cases replayed")
    summary={
        "format":FORMAT,
        "status":"TWENTY_REAL_LEAN_REPLAYS_UNREVIEWED_NOT_CI_BOUND",
        "source_head":head,"replayed_case_count":20,
        "replays":[completed[cid] for cid in sorted(completed)],
        "new_source_bound_CI_acceptance":False,
        "independent_case_reviews":0,
        "independent_claim_reviews":0,
        "mathematical_release_approved":False,
    }
    (target/"unreviewed_batch_replays.json").write_text(
        json.dumps(summary,sort_keys=True,indent=2)+"\n")
    return summary

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--catalog-dir",required=True,type=Path)
    p.add_argument("--producer-zips",required=True,type=Path)
    p.add_argument("--selection",required=True,type=Path)
    p.add_argument("--out",required=True,type=Path)
    a=p.parse_args(argv)
    try:
        result=replay_twenty(a.head,a.catalog_dir,a.producer_zips,
                             a.selection,a.out)
        print(json.dumps({"status":result["status"],
                          "cases":result["replayed_case_count"]}))
        return 0
    except (LegacyBatchError,ValueError,KeyError,OSError) as exc:
        print("LEGACY 20 REPLAY BLOCKED:",exc,file=sys.stderr)
        return 2
if __name__=="__main__":
    raise SystemExit(main())
