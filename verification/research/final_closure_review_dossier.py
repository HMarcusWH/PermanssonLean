"""Fail-closed review dossier for complete, authenticated PR113 producer artifacts.

Every output is an UNREVIEWED candidate, not a v2 receipt or scope decision.
The live producing-job and artifact SHA-256 verification MUST happen in the
caller, final_closure_producer_catalog.collect, before using these helpers.
No author-written JSON or synthetic check ID becomes mathematical acceptance.
"""
from __future__ import annotations

import hashlib
import json
import re

SHA40 = re.compile(r"^[0-9a-f]{40}$")
CLAIMS = {"Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2", "N3", "D8", "D9"}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class ReviewDossierError(ValueError):
    pass


def need(value, message):
    if not value:
        raise ReviewDossierError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def extracted_case_refs(kind, members, head, producer):
    """Validate preserved candidate inputs without certifying their semantics."""
    def get(name):
        need(isinstance(name, str) and name in members,
             "raw source/diagnostic member missing: " + str(name))
        return members[name]

    def doc(name):
        try:
            parsed = json.loads(get(name))
        except (ValueError, TypeError) as exc:
            raise ReviewDossierError("invalid candidate JSON: " + name) from exc
        need(isinstance(parsed, dict), "candidate JSON is not an object")
        return parsed

    need(kind in ("append", "legacy") and producer.get("head_sha") == head and
         producer.get("status") == "CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED" and
         producer.get("independent_review") is False and
         type(producer.get("actual_check_run_id")) is int,
         "no real unreviewed producer attestation")
    manifest = doc("unreviewed_shard_manifest.json")
    result = {}
    if kind == "append":
        need(manifest.get("head") == head and manifest.get("status") ==
             "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED_RECEIPT" and
             manifest.get("ci_check_run_id") is None and
             manifest.get("independent_review") is False,
             "append candidate identity/status invalid")
        for cid in manifest.get("case_ids", []):
            need(isinstance(cid, str) and cid not in result,
                 "duplicate or invalid append case")
            record = doc(cid + "/unreviewed_candidate.json")
            proof = record.get("mutation_record")
            need(isinstance(proof, dict) and record.get("case_id") == cid and
                 record.get("source_head") == head and
                 record.get("ci_check_run_id") is None and
                 record.get("independent_review") is False and
                 proof.get("head_sha") == head and
                 proof.get("case_ids") == [cid] and
                 proof.get("outcome") == "REJECTED_SEMANTIC" and
                 proof.get("check_run_id") is None,
                 "append candidate forged, stale or not rejected")
            prefix = cid + "/source_logs/"
            original = get(prefix + proof["original_lean_source_member"])
            mutated = get(prefix + proof["mutant_source_member"])
            negative = get(prefix + proof["log_member"])
            positive_record = proof["positive_control"]
            positive = get(prefix + positive_record["log_member"])
            need(mutated.startswith(original) and len(mutated) > len(original) and
                 digest(original) == proof["original_lean_source_sha256"] and
                 digest(mutated) == proof["mutant_source_sha256"] and
                 digest(negative) == proof["log_sha256"] and
                 digest(positive) == positive_record["log_sha256"] and
                 positive_record.get("compiled") is True and
                 positive_record.get("exit_code") == 0 and
                 positive_record.get("lean_toolchain") == "4.34.0",
                 "true/false source bytes or compiler logs not retained")
            appended = mutated[len(original):].decode("utf-8")
            need(not re.search(
                    r"(?mi)^\s*(?:import|axiom|constant|opaque|set_option)\b",
                    appended) and not re.search(
                    r"(?i)\b(?:sorry|sorryAx|admit)\b", appended),
                 "false source changes imports, axioms or admissions")
            need(digest(get(cid + "/semantic_candidate_logs.zip")) ==
                 record.get("detached_bundle_sha256"),
                 "retained nested mutation ZIP digest mismatch")
            result[cid] = {
                "route": "append",
                "selected_semantic_methods": [proof["test_name"]],
                "test_path": proof["test_path"],
                "original_source_path": proof["original_lean_source_path"],
                "original_source_sha256": digest(original),
                "positive_log_sha256": digest(positive),
                "negative_log_sha256": digest(negative),
                "producing_artifact_id": producer["artifact_id"],
                "actual_producing_check_run_id_provenance_only":
                    producer["actual_check_run_id"],
                "independent_criterion_review": "NOT_RECEIVED",
                "accepted_semantic_negative": False,
            }
    else:
        need(manifest.get("source_head") == head and manifest.get("status") ==
             "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED" and
             manifest.get("ci_check_run_id") is None and
             manifest.get("independent_review") is False,
             "legacy candidate identity/status invalid")
        case_rows = manifest.get("case_reports")
        need(isinstance(case_rows, list) and
             [x.get("case_id") for x in case_rows if isinstance(x, dict)] ==
             manifest.get("case_ids"), "legacy case coverage differs from manifest")
        for case in case_rows:
            cid = case["case_id"]
            need(cid not in result, "duplicate legacy case")
            methods = []
            events = []
            for i, item in enumerate(case.get("tests", [])):
                prefix = f"{cid}/test-{i:02d}/"
                row = doc(prefix + "unreviewed_test_manifest.json")
                need(row == item and row.get("case_id") == cid and
                     row.get("status") ==
                     "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED" and
                     row.get("test_exit_code") == 0 and
                     row.get("ci_check_run_id") is None and
                     row.get("independent_review") is False and
                     not row.get("semantic_methods_missing_candidate"),
                     "legacy named method not executed or missing semantic diagnostic")
                need(digest(get(prefix + "test_stdout.log")) ==
                     row["stdout_sha256"] and
                     digest(get(prefix + "test_stderr.log")) ==
                     row["stderr_sha256"], "legacy unittest log hash mismatch")
                methods += row["selected_methods"]
                actually_observed = set()
                for event in row["compiler_events"]:
                    loc = prefix + "raw_compiler/" + event["observation_id"] + "/"
                    need(digest(get(loc + "observation.json")) ==
                         event["raw_metadata_sha256"],
                         "legacy compiler observation metadata changed")
                    if event.get("source_retained"):
                        need(digest(get(loc + "source.lean")) ==
                             event["source_sha256"],
                             "legacy original Lean source observation changed")
                    if event.get("possible_semantic_diagnostic"):
                        need(event.get("method_attribution_ambiguous") is False
                             and event.get("method_observed_unverified")
                                 in row["selected_methods"],
                             "class-level legacy diagnostic borrowed as a method")
                        method = event["method_observed_unverified"]
                        actually_observed.add(method)
                        events.append({
                            "method": method,
                            "observation_id": event["observation_id"],
                            "source_sha256": event["source_sha256"],
                            "original_provider_candidates_unreviewed":
                                event.get("original_provider_candidates_unreviewed", []),
                        })
                need(actually_observed == set(row["selected_methods"]),
                     "no individually attributable legacy diagnostic: " + cid)
            need(methods and len(methods) == len(set(methods)),
                 "missing/duplicate selected legacy methods")
            result[cid] = {
                "route": "legacy",
                "selected_semantic_methods": sorted(methods),
                "retained_semantic_events": events,
                "source_appended_replay_required": True,
                "producing_artifact_id": producer["artifact_id"],
                "actual_producing_check_run_id_provenance_only":
                    producer["actual_check_run_id"],
                "independent_criterion_review": "NOT_RECEIVED",
                "accepted_semantic_negative": False,
            }
    return result


def make_dossier(head, tree, original, claim_map, compiler, candidate_cases,
                producers):
    """Bind every canonical criterion to review references, never approvals."""
    need(isinstance(head, str) and SHA40.fullmatch(head) and
         isinstance(tree, str) and SHA40.fullmatch(tree),
         "bad reviewed source/tree identity")
    origins = original.get("cases") if isinstance(original, dict) else None
    claims = claim_map.get("claims") if isinstance(claim_map, dict) else None
    proofs = compiler.get("compiler_axiom_receipts") if isinstance(compiler, dict) else None
    need(isinstance(origins, list) and len(origins) == 45 and
         isinstance(claims, list) and len(claims) == 11 and
         isinstance(proofs, list) and len(proofs) == 259,
         "45/11/259 theorem acceptance graph is incomplete")
    case_ids = {x.get("case_id") for x in origins}
    claim_ids = {x.get("claim_id") for x in claims}
    need(len(case_ids) == 45 and claim_ids == CLAIMS and
         isinstance(candidate_cases, dict) and set(candidate_cases) == case_ids,
         "missing or substituted canonical cases/claims")
    need(sum(x.get("route") == "append" for x in candidate_cases.values()) == 25
         and sum(x.get("route") == "legacy" for x in candidate_cases.values()) == 20,
         "original 25+20 case partition changed")
    need(isinstance(producers, list) and len(producers) == 21 and
         len({p.get("artifact_id") for p in producers}) == 21 and
         all(p.get("status") == "CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED"
             and p.get("head_sha") == head
             and type(p.get("actual_check_run_id")) is int
             and p.get("independent_review") is False
             and p.get("mathematical_acceptance") is False
             for p in producers), "actual exact-H producing artifacts unavailable")
    seen = set()
    for row in proofs:
        key = (row.get("path"), row.get("declaration"))
        need(key not in seen and row.get("head_sha") == head
             and row.get("compiler_result") == "PASS"
             and row.get("check_run_id") is None
             and set(row.get("transitive_axioms", [])) <= AXIOMS,
             "invalid borrowed theorem or axiom list")
        seen.add(key)
    need({c for r in proofs for c in r.get("case_ids", [])} == case_ids and
         {c for r in proofs for c in r.get("claim_ids", [])} == claim_ids,
         "uncovered case or claim owners")
    docket = []
    for item in sorted(origins, key=lambda x: x["case_id"]):
        cid = item["case_id"]
        applicable = [p for p in proofs if cid in p.get("case_ids", [])]
        requirements = item.get("historical_proof_declarations")
        need(isinstance(requirements, list) and requirements
             and all(any(p["path"] == req.get("path") and
                         (p["declaration"] == req.get("name") or
                          p["declaration"].endswith("." + req.get("name", "")))
                         for p in applicable) for req in requirements),
             "original selected theorem not compiled for: " + cid)
        routes = item.get("test_method_candidates", [])
        candidate = candidate_cases[cid]
        methods = candidate.get("selected_semantic_methods")
        need(isinstance(methods, list) and bool(methods)
             and len(set(methods)) == len(methods)
             and all(any(r.get("role") == "SEMANTIC_NEGATIVE"
                         and r.get("method") == method for r in routes)
                     for method in methods),
             "case semantic negative not registered to original wording: " + cid)
        docket.append({
            "case_id": cid,
            "original_required_expected_result":
                item.get("required_expected_result"),
            "current_candidate_decision": item.get("current_candidate_decision"),
            "historical_remaining_obligations": item.get("remaining_obligations", []),
            "source_theorem_receipts": [
                {k: p[k] for k in ("id", "path", "declaration",
                                  "elaborated_type_sha256", "axiom_log_sha256")}
                for p in applicable],
            "registered_positive_methods": [
                x for x in routes if x.get("role") in ("COMPILER_SOURCE", "EXACT_CHECK")],
            "registered_negative_methods": [
                x for x in routes if x.get("role") == "SEMANTIC_NEGATIVE"],
            "producing_negative_candidate": candidate,
            "semantic_scope_review_required": True,
            "accepted_case_decision": None,
        })
    claim_docket = []
    for item in sorted(claims, key=lambda x: x["claim_id"]):
        cid = item["claim_id"]
        applicable = [p for p in proofs if cid in p.get("claim_ids", [])]
        required = item.get("declarations")
        need(isinstance(required, list) and bool(required)
             and all(any(p["path"] == x.get("path")
                         and p["declaration"] == x.get("declaration")
                         for p in applicable) for x in required),
             "original claim support missing: " + cid)
        claim_docket.append({
            "claim_id": cid, "registered_declarations": required,
            "test_source_candidates": item.get("test_source_candidates", []),
            "compiler_receipt_ids": [p["id"] for p in applicable],
            "original_case_links": item.get("original_case_links", []),
            "positive_negative_claim_receipts": "NOT_ASSEMBLED",
            "independent_review": "NOT_RECEIVED",
            "accepted_claim_decision": None,
        })
    return {
        "format": "Permansson.PR113.SourceReviewDossierCandidate.v1",
        "status": "UNREVIEWED_AUTHENTICATED_PRODUCERS_SCOPE_PENDING",
        "head_sha": head, "tree_sha": tree,
        "case_count": 45, "claim_count": 11, "compiler_target_count": 259,
        "producer_count": 21,
        "case_dockets": docket, "claim_dockets": claim_docket,
        "accepted_case_count": 0, "accepted_claim_count": 0,
        "independent_review": False, "required_ci_accepted": False,
        "postmerge_source": None, "release_approved": False,
    }
