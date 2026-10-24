"""Resolve legacy runtime compiler events *after* original exact-H CI.

The frozen source can contain a case -> named negative-test -> theorem-provider
intent, but CANNOT contain run/artifact/event IDs that only materialize after
frozen-H GitHub jobs. This adapter authenticates all original 21 GitHub ZIPs,
enumerates actual intended semantic-negative compiler events, and accepts only
an explicit detached 20-case event decision. No semantic reviewer is forged.

Relevance of a false statement to the case remains an independent mathematical
review obligation. A rejected parser/unknown identifier/timeout is NOT an
acceptable semantic negative.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

from final_closure_complete_lean_evidence import ROOT, git_head
from final_closure_legacy_semantic_evidence import original_case_map
from final_closure_producer_bytes import authenticate
from final_closure_producer_v2_bridge import verified_producer_index
from pr113_v31_execution_integrity import exact_source, source_clean_negative

FORMAT_INTENT="Permansson.PR113.Legacy20StaticSourceIntent.v1"
FORMAT_DECISION="Permansson.PR113.Legacy20DetachedEventDecision.v1"
FORMAT_SELECTION="Permansson.PR113.LegacyReplaySelection.v1"
FORMAT_REPORT="Permansson.PR113.Legacy20ObservedEventsCandidate.v1"
EVENT=re.compile(r"^event-[0-9]+-[0-9]{6}$")
TEST=re.compile(r"^test_[A-Za-z0-9_]+$")
SHA40=re.compile(r"^[a-f0-9]{40}$")


class RuntimeLegacyError(ValueError):
    pass

def require(ok,reason):
    if not ok:raise RuntimeLegacyError(reason)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def committed_selection(head, path):
    """Only static, criterion-selected source intent can precede source H."""
    path=Path(path).absolute()
    require(not path.is_symlink() and
            path.is_relative_to(ROOT.resolve()) and
            path.as_posix().endswith(
                "/research/paper_closures/post_merge_112/legacy20_source_intent_v31.json"),
            "pre-freeze legacy route intent must be source-controlled")
    source=exact_source(head,ROOT)
    rel=path.relative_to(ROOT.resolve()).as_posix()
    raw=source.blob(rel)
    require(path.is_file() and path.read_bytes()==raw,
            "working source intent differs from exact-H Git blob")
    return json.loads(raw), source

def parse_intent(payload, head, source):
    byid,legacy=original_case_map(head)
    required=set(legacy)
    require(isinstance(payload,dict) and
            payload.get("format")==FORMAT_INTENT and
            payload.get("source_head_binding")=="ACTUAL_CI_HEAD_AT_RUN" and
            payload.get("review_status")=="REQUIRES_INDEPENDENT_MATHEMATICAL_REVIEW" and
            isinstance(payload.get("cases"),list) and
            len(payload["cases"])==20 and len(required)==20,
            "static 20-case legacy intent malformed or claims acceptance")
    mapped={}
    for record in payload["cases"]:
        require(isinstance(record,dict) and
                set(record)=={"case_id","test_path","test_method","original_provider"},
                "invalid pre-freeze legacy selection keys")
        cid=record["case_id"]
        require(cid in required and cid not in mapped and
                isinstance(record["test_path"],str) and
                isinstance(record["test_method"],str) and
                TEST.fullmatch(record["test_method"]) and
                isinstance(record["original_provider"],str),
                "legacy static intent missing/duplicates original case")
        criteria=byid[cid]
        require(any(isinstance(m,dict) and
                    m.get("role")=="SEMANTIC_NEGATIVE" and
                    m.get("path")==record["test_path"] and
                    m.get("method")==record["test_method"]
                    for m in criteria.get("test_method_candidates",())),
                "original legacy negative test does not belong to case")
        provider=record["original_provider"]
        require(provider.startswith("PermanssonResearch/") and
                provider.endswith(".lean") and
                ".." not in PurePosixPath(provider).parts and
                provider in {x.get("path") for x in
                             (criteria.get("historical_proof_declarations",())+
                              criteria.get("new_claim_source_candidates",()))
                             if isinstance(x,dict)},
                "legacy provider not owned by original criterion")
        source.blob(provider); source.blob(record["test_path"])
        mapped[cid]=record
    require(set(mapped)==required, "original 20-case legacy intent incomplete")
    return mapped

def original21(catalog_dir, zips_dir, head):
    catalog=Path(catalog_dir).absolute()
    directory=Path(zips_dir).absolute()
    require(catalog.is_dir() and directory.is_dir() and
            all(not p.is_symlink() for p in (
                catalog,directory,*catalog.parents,*directory.parents)) and
            not catalog.is_relative_to(ROOT.resolve()) and
            not directory.is_relative_to(ROOT.resolve()),
            "legacy 21 original producing inputs must be detached")
    raw=(catalog/"unreviewed_producer_catalog.json").read_bytes()
    require(0<len(raw)<=4*1024*1024,
            "full original producer provenance unavailable")
    summary=json.loads(raw)
    rows=summary.get("producer_artifact_checks")
    require(summary.get("head_sha")==head and
            summary.get("producing_artifact_count")==21 and
            isinstance(rows,list) and len(rows)==21,
            "authentic latest H original 21 producers not available")
    indexed=verified_producer_index(head,rows)
    zips={}
    for row in rows:
        aid=row.get("artifact_id")
        require(type(aid) is int and aid>0, "missing original GH artifact ID")
        p=directory/(str(aid)+".zip")
        require(p.is_file() and not p.is_symlink() and
                p.stat().st_size<=64*1024*1024,
                "original GH source ZIP not available")
        raw=p.read_bytes()
        require(sha(raw)==row.get("artifact_sha256"),
                "downloaded original producer ZIP digest changed")
        zips[aid]=raw
    auth=authenticate(head,rows,zips)
    require(auth.get("producer_count")==21 and
            auth.get("head_sha")==head,
            "original 21 source producers not authenticated")
    legacy_artifacts={
        x["artifact_id"] for (kind,shard),x in indexed.items()
        if kind=="legacy"
    }
    require(len(legacy_artifacts)==8,
            "missing full 8-shard original historical legacy observations")
    return auth,legacy_artifacts

def enumerate_events(head,intents,source,originals,legacy_artifacts):
    result={}
    for cid in sorted(intents):
        target=intents[cid]
        method=target["test_method"]
        test_source=source.blob(target["test_path"])
        expected_hash=sha(test_source)
        options=[]
        for aid in sorted(legacy_artifacts):
            members=originals["producers"][aid]["members"]
            prefix=cid+"/"
            manifests=[
                (name,data) for name,data in members.items()
                if name.startswith(prefix+"test-") and
                name.endswith("/unreviewed_test_manifest.json")
            ]
            for name,raw in manifests:
                record=json.loads(raw)
                if (record.get("case_id")!=cid or
                    record.get("test_file")!=target["test_path"] or
                    record.get("source_test_sha256")!=expected_hash or
                    method not in record.get("selected_methods",()) or
                    record.get("test_exit_code")!=0 or
                    record.get("status")!="EXECUTED_UNREVIEWED_NOT_AUTHENTICATED"):
                    continue
                base=name[:-len("unreviewed_test_manifest.json")]
                m=re.fullmatch(re.escape(cid)+r"/test-([0-9]{2})/",base)
                require(m is not None, "legacy captured test index malformed")
                test_index=int(m.group(1))
                for obs_path,meta_raw in members.items():
                    if (not obs_path.startswith(base+"raw_compiler/") or
                        not obs_path.endswith("/observation.json")):
                        continue
                    evt=obs_path[len(base+"raw_compiler/"):-len("/observation.json")]
                    if not EVENT.fullmatch(evt):
                        continue
                    o=json.loads(meta_raw)
                    if (o.get("format")!="Permansson.LegacyLeanCompilerObservation.v1" or
                        o.get("case_id_unverified")!=cid or
                        o.get("selected_method_unverified")!=method or
                        o.get("status")!="RAW_UNREVIEWED" or
                        type(o.get("returncode")) is not int or
                        o["returncode"]==0):
                        continue
                    false=members.get(base+"raw_compiler/"+evt+"/source.lean")
                    stderr=members.get(base+"raw_compiler/"+evt+"/stderr.log")
                    if not isinstance(false,bytes) or not isinstance(stderr,bytes):
                        continue
                    if sha(false)!=o.get("source_sha256") or sha(stderr)!=o.get("stderr_sha256"):
                        continue
                    try:
                        source_clean_negative(stderr)
                    except ValueError:
                        continue
                    options.append({
                        "case_id":cid,"test_index":test_index,
                        "test_method":method,
                        "original_provider":target["original_provider"],
                        "observation_id":evt,
                        "producing_artifact_id":aid,
                        "observation_sha256":sha(meta_raw),
                        "false_input_sha256":sha(false),
                        "unreviewed":True,
                    })
        unique={(r["test_index"],r["observation_id"],
                 r["producing_artifact_id"]) for r in options}
        require(len(unique)==len(options),
                "duplicate historical capture identity across source artifacts")
        result[cid]=sorted(options,key=lambda x:(
            x["producing_artifact_id"],x["test_index"],x["observation_id"]))
    return result

def decision_to_selection(head, candidates, raw):
    require(isinstance(raw,dict) and
            raw.get("format")==FORMAT_DECISION and
            raw.get("head_sha")==head and
            raw.get("status")=="DETACHED_EVENT_CHOICES_UNREVIEWED" and
            raw.get("independent_case_review") is False and
            raw.get("mathematical_acceptance") is False and
            isinstance(raw.get("cases"),list) and
            len(raw["cases"])==20,
            "legacy detached reviewer event choices incomplete or self-approved")
    chosen={}
    for row in raw["cases"]:
        require(isinstance(row,dict) and
                set(row)=={"case_id","test_index","observation_id",
                           "producing_artifact_id"},
                "legacy runtime event selection contains unsupported keys")
        cid=row["case_id"]
        require(cid in candidates and cid not in chosen,
                "duplicate or foreign legacy runtime choice")
        matched=[x for x in candidates[cid]
                 if all(x.get(k)==v for k,v in row.items())]
        require(len(matched)==1,
                "legacy runtime choice was not a genuine observed semantic source")
        selected=matched[0]
        chosen[cid]={key:selected[key] for key in (
            "case_id","test_index","test_method","original_provider",
            "observation_id","producing_artifact_id")}
    require(set(chosen)==set(candidates),
            "legacy source runtime selection does not cover 20 cases")
    return {
        "format":FORMAT_SELECTION,"cases":[chosen[cid] for cid in sorted(chosen)],
    }

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--intent",required=True,type=Path)
    p.add_argument("--catalog-dir",required=True,type=Path)
    p.add_argument("--producer-zips",required=True,type=Path)
    p.add_argument("--detached-event-choice",type=Path)
    p.add_argument("--out",required=True,type=Path)
    a=p.parse_args(argv)
    try:
        require(isinstance(a.head,str) and SHA40.fullmatch(a.head) and
                git_head()==a.head,
                "must use genuine current exact H Git source")
        dest=a.out.absolute()
        require(not dest.exists() and
                not dest.is_relative_to(ROOT.resolve()) and
                not any(p.is_symlink() for p in (dest,*dest.parents)),
                "legacy event choices output must be fresh and external")
        source_intent,source=committed_selection(a.head,a.intent)
        intents=parse_intent(source_intent,a.head,source)
        original,legacies=original21(a.catalog_dir,a.producer_zips,a.head)
        options=enumerate_events(a.head,intents,source,original,legacies)
        report={
            "format":FORMAT_REPORT,
            "status":"ACTUAL_CAPTURE_OPTIONS_UNREVIEWED" if
                all(options.values()) else "INCOMPLETE_ORIGINAL_CAPTURE_OPTIONS",
            "source_head":a.head,
            "original_legacy_case_count":20,
            "cases":[{"case_id":cid,"options":options[cid]}
                     for cid in sorted(options)],
            "all_cases_have_candidates":all(bool(options[cid]) for cid in options),
            "independent_case_review":False,
            "mathematical_acceptance":False,
            "source_commit_changed":False,
        }
        # Every report is nonauthoritative; even one synthetic choice is banned.
        dest.mkdir(parents=True)
        (dest/"unreviewed_legacy20_candidates.json").write_text(
            json.dumps(report,sort_keys=True,indent=2)+"\n")
        if a.detached_event_choice is not None:
            external=a.detached_event_choice.absolute()
            require(external.is_file() and not external.is_symlink() and
                    not external.is_relative_to(ROOT.resolve()) and
                    external.stat().st_size<=1024*1024,
                    "runtime event choice must be a detached bounded original input")
            selection=decision_to_selection(
                a.head,options,json.loads(external.read_bytes()))
            (dest/"legacy20_runtime_selection.json").write_text(
                json.dumps(selection,sort_keys=True,indent=2)+"\n")
        return 0 if all(options.values()) else 2
    except (RuntimeLegacyError,ValueError,TypeError,OSError,KeyError) as exc:
        print("PR113 LEGACY20 REAL EVENT CHOICE BLOCKED:",exc,file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())
