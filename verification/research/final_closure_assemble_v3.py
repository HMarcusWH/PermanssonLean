"""Assemble an UNREVIEWED, producer-authenticated v3 source candidate.

Input: a completed exact-H 21-shard catalog created by
final_closure_producer_catalog.py, its original ZIPs saved as <artifact-id>.zip,
a real B/H synthetic merge S, and twelve successful exact-H checks.

This does NOT manufacture missing twenty legacy append-only replays, positive
method-route proofs, eleven claim negative controls, any case/claim decision,
any GitHub reviewer, historical security authorization or scholarly release.
Only bytes actually present in the original authenticated producing ZIPs may
be entered as proof/test evidence. Never mutate old v2 receipt generation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import zipfile

from final_closure_authenticate import (
    BASE, REQUIRED, authenticated_checks, git, AuthenticationError)
from final_closure_case_receipts import (
    ROOT, FORMAT_V3, digest, EvidenceError, parse_target_axioms)
from final_closure_schema import validate_overlay
from final_closure_producer_bytes import authenticate, original_member
from final_closure_producer_v2_bridge import verified_producer_index
from final_closure_review_dossier import extracted_case_refs
from final_closure_mutation_evidence import committed_file_bytes
from closure_elaborated_type import compiled_type_record, elaborated_type_sha256


class AssemblyError(ValueError):
    pass


def require(condition, reason):
    if not condition:
        raise AssemblyError(reason)


def load_json(path):
    return json.loads(Path(path).read_bytes())


def check_external(path, *, folder=False):
    value = Path(path)
    require(not value.is_symlink(), "symlinked producer evidence forbidden")
    value = value.resolve(strict=True)
    root = ROOT.resolve()
    require(not value.is_relative_to(root) and
            not root.is_relative_to(value),
            "candidate evidence must be external to source checkout")
    require(value.is_dir() if folder else value.is_file(),
            "missing producing evidence input")
    return value


def exact_source_bytes(head, relative):
    path = ROOT / relative
    return committed_file_bytes(head, path, root=ROOT)


def pack_member(members, name, raw):
    require(type(name) is str and type(raw) is bytes and
            name not in members and
            not name.startswith("/") and ".." not in Path(name).parts and
            "\\" not in name and
            len(raw) <= 4*1024*1024, "unsafe or duplicated detached member")
    members[name] = raw


def proof_row(head, source, producer, raw_log, outer):
    """Full elaborated Lean type, not a truncated lexical statement header."""
    idx = source.get("inventory_index")
    require(type(idx) is int and 0 <= idx < 259 and
            source.get("id") == f"all:{idx:04d}" and
            source.get("head_sha") == head and
            source.get("compiler_result") == "PASS" and
            source.get("compiler_check") == "research" and
            source.get("check_run_id") is None,
            "invalid 259-target source theorem row")
    decl = source["declaration"]
    require(digest(raw_log) == source["axiom_log_sha256"] and
            digest(exact_source_bytes(head, source["path"])) ==
            source["source_sha256"],
            "compiler theorem source/log differs from exact H")
    compiled = compiled_type_record(raw_log.decode("utf-8"), decl)
    elaborated = elaborated_type_sha256(compiled)
    require(elaborated == source["elaborated_type_sha256"] and
            parse_target_axioms(raw_log.decode("utf-8"), decl) ==
            source["transitive_axioms"], "Lean type/axiom witness mismatch")
    # v3 statement_sha256 is explicitly the complete kernel-elaborated type
    # representation hash. It is never a guessed lexical declaration header.
    keys = ("id", "head_sha", "path", "declaration", "source_sha256",
            "transitive_axioms", "compiler_result", "axiom_log_sha256",
            "case_ids", "claim_ids", "elaborated_type_sha256",
            "declaration_kind", "universe_params_repr")
    row = {key: source[key] for key in keys}
    row.update({
        "statement_sha256": elaborated,
        "compiler_check": "pr113-compiler-shard",
        "check_run_id": producer["actual_check_run_id"],
        "axiom_log_member": outer,
        "producer_artifact_id": producer["artifact_id"],
        "producer_member_bindings": [{
            "outer_member": outer,
            "source_member": source["axiom_log_member"]}],
    })
    return row


def append_case_rows(head, case, producer, original_members, result_members):
    """Preserve source-owned false mutants and their *actual* positive logs."""
    candidate = json.loads(original_members[case+"/unreviewed_candidate.json"])
    source = candidate["mutation_record"]
    require(candidate.get("case_id") == case and
            candidate.get("source_head") == head and
            source.get("head_sha") == head and
            source.get("case_ids") == [case] and
            source.get("check_run_id") is None and
            source.get("outcome") == "REJECTED_SEMANTIC" and
            candidate.get("independent_review") is False,
            "case is not an unreviewed source-executed mutation")
    require(digest(exact_source_bytes(head, source["test_path"])) ==
            source["source_sha256"], "original named test source does not match H")
    controls = source["positive_control"]
    names = (source["log_member"], controls["log_member"],
             source["mutant_source_member"],
             source["original_lean_source_member"])
    paths = {}
    for name in set(names):
        member = case+"/source_logs/"+name
        require(member in original_members, "source-generated diagnostic missing")
        outer = "append/"+member
        raw = original_members[member]
        pack_member(result_members, outer, raw)
        paths[name] = (outer, member)
    for key, name in (("log_sha256", source["log_member"]),
                      ("mutant_source_sha256", source["mutant_source_member"]),
                      ("original_lean_source_sha256",
                       source["original_lean_source_member"])):
        require(digest(result_members[paths[name][0]]) == source[key],
                "original positive/negative/source digest mismatch")
    require(digest(result_members[paths[controls["log_member"]][0]]) ==
            controls["log_sha256"], "positive control bytes are not preserved")
    require(digest(exact_source_bytes(head, source["original_lean_source_path"])) ==
            source["original_lean_source_sha256"],
            "true original source changed at H")
    def links(used):
        return [{"outer_member":paths[name][0],
                 "source_member":paths[name][1]}
                for name in sorted(set(used))]
    base = {key:source[key] for key in (
        "head_sha","test_path","test_name","source_sha256","case_ids","claim_ids")}
    base.update(check_run_id=producer["actual_check_run_id"],
                producer_artifact_id=producer["artifact_id"])
    positive = {
        **base, "id":"positive:"+source["id"],
        "positive_control":dict(controls, log_member=paths[controls["log_member"]][0]),
        "outcome":"PASS", "compiler_exit_code":0,
        "log_member":paths[controls["log_member"]][0],
        "log_sha256":controls["log_sha256"],
        "producer_member_bindings":links([controls["log_member"]]),
    }
    negative = {
        **base, "id":"negative:"+source["id"],
        "positive_control":dict(controls, log_member=paths[controls["log_member"]][0]),
        "outcome":"REJECTED_SEMANTIC",
        "compiler_exit_code":source["compiler_exit_code"],
        "log_member":paths[source["log_member"]][0],
        "log_sha256":source["log_sha256"],
        "mutant_source_member":paths[source["mutant_source_member"]][0],
        "mutant_source_sha256":source["mutant_source_sha256"],
        "original_lean_source_member":paths[source["original_lean_source_member"]][0],
        "original_lean_source_sha256":source["original_lean_source_sha256"],
        "original_lean_source_path":source["original_lean_source_path"],
        "producer_member_bindings":links(names),
    }
    return positive, negative


def assemble(head, synthetic, catalog_dir, artifacts_dir, output):
    catalog_dir = check_external(catalog_dir, folder=True)
    artifacts_dir = check_external(artifacts_dir, folder=True)
    output = Path(output).resolve()
    require(not output.exists() and
            not output.is_relative_to(ROOT.resolve()) and
            not output.is_relative_to(catalog_dir) and
            not output.is_relative_to(artifacts_dir),
            "v3 output must be new and external to source/producer inputs")
    require(git("rev-parse","HEAD") == head and
            git("show","-s","--format=%P",synthetic).split() == [BASE,head] and
            git("rev-parse",synthetic+"^{tree}") ==
            git("rev-parse",head+"^{tree}"),
            "H or genuine ordered B/H source tree differs")
    report = load_json(catalog_dir/"unreviewed_producer_catalog.json")
    dossier = load_json(catalog_dir/"unreviewed_source_review_dossier.json")
    compiled = load_json(catalog_dir/"compiler/complete_compiler_candidate.json")
    require(report.get("head_sha") == head and
            report.get("producing_artifact_count") == 21 and
            dossier.get("head_sha") == head and
            dossier.get("status") ==
            "UNREVIEWED_AUTHENTICATED_PRODUCERS_SCOPE_PENDING" and
            compiled.get("head_sha") == head and
            compiled.get("proof_count") == 259 and
            len(compiled.get("compiler_axiom_receipts", [])) == 259,
            "complete original 21/259 source review dossier missing")
    producers = report["producer_artifact_checks"]
    indexed = verified_producer_index(head, producers)
    original_zip = {}
    members = {}
    for row in producers:
        artifact = row["artifact_id"]
        name = artifacts_dir/(str(artifact)+".zip")
        require(name.is_file() and not name.is_symlink(),
                "missing original producing ZIP ID "+str(artifact))
        raw = name.read_bytes()
        require(digest(raw) == row["artifact_sha256"],
                "producing ZIP differs from GitHub digest")
        original_zip[artifact] = raw
        pack_member(members, "producer/"+str(artifact)+".zip", raw)
    verified = authenticate(head, producers, original_zip)
    require(verified["producer_count"] == 21 and
            verified["status"] == "REAL_PRODUCING_BYTES_UNREVIEWED",
            "21 producers not independently authenticated")
    proof_receipts = []
    for row in compiled["compiler_axiom_receipts"]:
        idx = row["inventory_index"]
        producer = indexed[("compiler", idx % 4)]
        name = row["axiom_log_member"]
        outer = "compiler/"+name
        raw = verified["producers"][producer["artifact_id"]]["members"].get(name)
        require(raw is not None, "original compiler shard log unavailable")
        pack_member(members, outer, raw)
        proof_receipts.append(proof_row(head, row, producer, raw, outer))
    require(len(proof_receipts) == 259 and
            {p["id"] for p in proof_receipts} ==
            {f"all:{i:04d}" for i in range(259)},
            "incomplete exact 259 source theorem receipts")
    positives, negatives = [], []
    cases = {}
    for (kind, shard), row in indexed.items():
        if kind not in ("append","legacy"):
            continue
        raw = verified["producers"][row["artifact_id"]]["members"]
        extracted = extracted_case_refs(kind, raw, head, row)
        require(not cases.keys() & extracted.keys(),
                "duplicated original case across semantic producers")
        cases.update(extracted)
        if kind == "append":
            for cid in sorted(extracted):
                pos, neg = append_case_rows(head, cid, row, raw, members)
                positives.append(pos)
                negatives.append(neg)
    legacy = sorted(cid for cid,v in cases.items() if v["route"] == "legacy")
    require(len(cases) == 45 and len(legacy) == 20 and
            len(positives) == len(negatives) == 25,
            "wrong 25+20 original-source candidate partition")
    checks = authenticated_checks(head)
    require(set(REQUIRED) <= set(checks),
            "not all twelve source CI checks genuinely green")
    stamped = [dict(row, evidence_zip_member="producer/"+str(row["artifact_id"])+".zip")
               for row in producers]
    overlay = {
        "format":FORMAT_V3, "phase":"premerge_review",
        "base_sha":BASE, "head_sha":head, "synthetic_sha":synthetic,
        "merged_main_sha":None, "evidence_bundle_sha256":None,
        "source_bound_ci":[
            {"name":name,"id":checks[name]["id"],"head_sha":head}
            for name in sorted(REQUIRED)],
        "producer_artifacts":stamped,
        "compiler_axiom_receipts":proof_receipts,
        "positive_test_receipts":positives,
        "semantic_negative_receipts":negatives,
        "case_decisions":[], "claim_decisions":[],
        "independent_source_reviews":[],
        "trusted_axioms":["Classical.choice","Quot.sound","propext"],
    }
    output.mkdir(parents=True, exist_ok=False)
    bundle = output/"unreviewed_evidence.zip"
    with zipfile.ZipFile(bundle,"w") as z:
        for name,body in sorted(members.items()):
            info = zipfile.ZipInfo(name,(1980,1,1,0,0,0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info,body,compress_type=zipfile.ZIP_DEFLATED,
                       compresslevel=9)
    overlay["evidence_bundle_sha256"] = digest(bundle.read_bytes())
    validate_overlay(overlay)
    (output/"unreviewed_v3_receipts.json").write_text(
        json.dumps(overlay,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    gaps = {
        "format":"Permansson.PR113.V3CandidateGaps.v1",
        "status":"UNREVIEWED_INCOMPLETE_NOT_FULL_ACCEPTANCE",
        "head_sha":head, "producers_authenticated":21,
        "compiler_proofs_source_bound":259,
        "append_cases_with_positive_negative_controls":25,
        "legacy_cases_requiring_source_appended_replay":legacy,
        "claims_requiring_individual_positive_negative_controls":
            ["Q1","Q2","Q3","M1","M2","M3","N1","N2","N3","D8","D9"],
        "original_positive_route_review_required":45,
        "independent_case_reviews":0, "independent_claim_reviews":0,
        "mathematical_release_approved":False,
    }
    (output/"remaining_work.json").write_text(
        json.dumps(gaps,sort_keys=True,indent=2)+"\n")
    return gaps


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--synthetic",required=True)
    p.add_argument("--catalog-dir",type=Path,required=True)
    p.add_argument("--producer-zips",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args(argv)
    try:
        result=assemble(args.head,args.synthetic,args.catalog_dir,
                        args.producer_zips,args.output)
    except (AssemblyError,AuthenticationError,EvidenceError,ValueError,OSError,
            KeyError,zipfile.BadZipFile) as exc:
        print("V3 CANDIDATE ASSEMBLY BLOCKED:",exc,file=sys.stderr)
        return 2
    print(json.dumps(result,sort_keys=True))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
