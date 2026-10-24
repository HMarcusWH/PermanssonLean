"""Reconcile 45 original criteria + 11 claims against exact Git-committed source.

This is a *discovery and implementation-gap ledger*, not a Lean proof or
independent case/claim review. Header/name presence and AST test discovery
can never turn PARTIAL into COMPLETE. A separate true Lean type/axiom +
semantic test receipt and independent reviewer decision are required.
"""
from __future__ import annotations
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
MAP_ROOT = "research/paper_closures/post_merge_112/"
CASE_MAP = MAP_ROOT + "acceptance_case_source_map.json"
CLAIM_MAP = MAP_ROOT + "claim_declaration_map.json"
ORIGINAL = MAP_ROOT + "acceptance_decisions.json"
INVENTORY = MAP_ROOT + "claim_inventory.json"
SHA40 = re.compile(r"^[a-f0-9]{40}$")
CLAIM_IDS = frozenset((
    "Q1","Q2","Q3","M1","M2","M3","N1","N2","N3","D8","D9"
))


class MatrixError(ValueError):
    pass


def check(ok, why):
    if not ok:
        raise MatrixError(why)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def committed(head, path):
    check(isinstance(path, str) and not path.startswith("/")
          and ".." not in Path(path).parts
          and (path.startswith("research/paper_closures/post_merge_112/")
               or path.startswith("verification/research/")
               or path.startswith("PermanssonResearch/")),
          "unrecognized source path for implementation reconciliation")
    try:
        result = subprocess.run(["git", "show", head + ":" + path],
                                cwd=ROOT, capture_output=True,
                                timeout=30, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise MatrixError("exact Git object fetch unavailable") from exc
    check(result.returncode == 0 and len(result.stdout) <= 4*1024*1024,
          "no actual source blob at H: " + path)
    return result.stdout


def strict_json(raw):
    check(type(raw) is bytes and len(raw) > 0, "empty JSON source")
    try:
        obj = json.loads(raw)
    except (ValueError, UnicodeError) as exc:
        raise MatrixError("malformed JSON source") from exc
    check(isinstance(obj, dict), "object required")
    return obj


def index_exact(rows, key, expected):
    check(isinstance(rows, list) and len(rows) == len(expected),
          "historical original set/cardinality changed")
    out = {}
    for r in rows:
        check(isinstance(r, dict) and
              isinstance(r.get(key), str) and
              r[key] not in out,
              "duplicate or malformed original criterion")
        out[r[key]] = r
    check(set(out) == set(expected), "old criteria/claims silently changed")
    return out


def method_candidates(routes, read):
    rows = []
    for route in routes:
        check(isinstance(route, dict), "invalid original test route record")
        path, name = route.get("path"), route.get("method")
        check(isinstance(path, str) and
              path.startswith("verification/research/") and
              path.endswith(".py") and
              isinstance(name, str) and name.startswith("test_"),
              "test method does not have an original explicit source route")
        status = "MISSING_SOURCE_OR_METHOD"
        digest = None
        try:
            raw = read(path)
            digest = sha(raw)
            tree = ast.parse(raw.decode("utf-8"))
            funcs = [n for n in ast.walk(tree)
                     if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
                     and n.name == name]
            if len(funcs) == 1:
                status = "DISCOVERED_UNREVIEWED"
            elif len(funcs) > 1:
                status = "AMBIGUOUS_UNREVIEWED"
        except (OSError, MatrixError, KeyError, SyntaxError, UnicodeError):
            pass
        rows.append({
            "path": path, "method": name, "role": route.get("role"),
            "source_sha256": digest, "source_status": status,
            "semantic_relevance_review": "NOT_YET_ACCEPTED",
            "actual_execution_provenance": None,
        })
    return rows


def proof_candidates(proofs, read, *, claim=False):
    result = []
    check(isinstance(proofs, list), "source proof list is malformed")
    for item in proofs:
        check(isinstance(item, dict), "invalid theorem provider")
        path = item.get("path")
        name = item.get("declaration") if claim else item.get("name")
        check(isinstance(path, str) and
              path.startswith("PermanssonResearch/") and
              path.endswith(".lean") and
              isinstance(name, str) and len(name) > 0,
              "invalid original theorem provider")
        digest = None
        status = "MISSING_SOURCE"
        try:
            digest = sha(read(path))
            status = "SOURCE_PRESENT__COMPILED_TYPE_UNCHECKED"
        except (OSError, MatrixError, KeyError):
            pass
        result.append({
            "path": path, "declaration": name, "source_sha256": digest,
            "candidate_status": status,
            "full_elaborated_type_sha256": None,
            "transitive_axiom_receipt": None,
            "independent_statement_review": False,
        })
    return result


def produce(head, read=None):
    check(isinstance(head, str) and SHA40.fullmatch(head),
          "source H not exact 40-character Git identifier")
    if read is None:
        read = lambda p: committed(head, p)
    case_map = strict_json(read(CASE_MAP))
    claim_map = strict_json(read(CLAIM_MAP))
    original = strict_json(read(ORIGINAL))
    inventory = strict_json(read(INVENTORY))
    cids = {c.get("case_id") for c in original.get("cases", [])
            if isinstance(c, dict)}
    check(len(cids) == 45 and None not in cids and
          case_map.get("original_cases") == 45 and
          case_map.get("new_closure_owners") == 11 and
          claim_map.get("count") == 11 and
          original.get("full45_accepted") is False,
          "frozen acceptance requirements or historical decision changed")
    by_case = index_exact(case_map.get("cases"), "case_id", cids)
    historical = index_exact(original.get("cases"), "case_id", cids)
    by_claim = index_exact(claim_map.get("claims"), "claim_id", CLAIM_IDS)
    frozen_claims = index_exact(inventory.get("claims"), "id", CLAIM_IDS)
    cases = []
    for cid, case in sorted(by_case.items()):
        old = historical[cid]
        check(case.get("required_expected_result") ==
              old.get("required_expected_result"),
              "original criterion wording drift: " + cid)
        proofs = proof_candidates(case.get("historical_proof_declarations"), read)
        tests = method_candidates(case.get("test_method_candidates", []), read)
        missing = (not proofs or not tests or
                   any(r["candidate_status"] == "MISSING_SOURCE" for r in proofs) or
                   any(r["source_status"] != "DISCOVERED_UNREVIEWED" for r in tests))
        cases.append({
            "case_id": cid,
            "requirement": case["required_expected_result"],
            "historical_contract_ids": case.get("historical_contract_ids", []),
            "historical_decision": old["decision"],
            "source_theorem_candidates": proofs,
            "candidate_tests": tests,
            "stated_remaining_obligations": case.get("remaining_obligations", []),
            "implementation_state": "MISSING" if missing else "PARTIAL",
            "independent_case_acceptance": "PENDING",
        })
    claims = []
    for cid, claim in sorted(by_claim.items()):
        check(frozen_claims[cid].get("accepted") is False and
              claim.get("accepted") is False,
              "claim inventory/history pretends acceptance")
        proofs = proof_candidates(claim.get("declarations"), read, claim=True)
        paths = claim.get("test_source_candidates", [])
        tests = []
        for path in paths:
            check(isinstance(path, str) and
                  path.startswith("verification/research/") and
                  path.endswith(".py"), "foreign claim test source")
            try:
                raw = read(path)
                tests.append({"path": path, "sha256": sha(raw),
                              "status": "SOURCE_PRESENT_UNREVIEWED"})
            except (OSError, MatrixError):
                tests.append({"path": path, "sha256": None,
                              "status": "MISSING_SOURCE"})
        missing = (not proofs or not tests or
                   any(p["candidate_status"] == "MISSING_SOURCE" for p in proofs)
                   or any(t["status"] == "MISSING_SOURCE" for t in tests))
        claims.append({
            "claim_id": cid, "draft_title": frozen_claims[cid].get("title"),
            "original_case_links": claim.get("original_case_links", []),
            "source_theorem_candidates": proofs,
            "candidate_test_files": tests,
            "scope_exclusions": claim.get("scope_exclusions", []),
            "implementation_state": "MISSING" if missing else "PARTIAL",
            "independent_claim_acceptance": "PENDING",
        })
    return {
        "format": "Permansson.PR113.ImplementationCandidateMatrix.v1",
        "status": "SOURCE_DISCOVERY_ONLY_NOT_LEAN_OR_INDEPENDENT_ACCEPTANCE",
        "audited_head": head,
        "original_case_count": 45, "new_claim_count": 11,
        "cases": cases, "claims": claims,
        "case_source_missing": [
            x["case_id"] for x in cases if x["implementation_state"] == "MISSING"],
        "claim_source_missing": [
            x["claim_id"] for x in claims if x["implementation_state"] == "MISSING"],
        "unconditionally_implemented": 0,
        "independently_accepted_cases": 0,
        "independently_accepted_claims": 0,
        "mathematical_certification": False,
        "publication_authorized": False,
    }


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head", required=True)
    p.add_argument("--out", type=Path, required=True)
    args=p.parse_args(argv)
    try:
        target=args.out.absolute()
        check(not target.exists() and not target.is_symlink() and
              not target.is_relative_to(ROOT.resolve()) and
              not any(p.is_symlink() for p in target.parents),
              "source report must be detached and not overwrite previous evidence")
        report=produce(args.head)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("x",encoding="utf-8") as file:
            json.dump(report,file,sort_keys=True,indent=2)
            file.write("\n")
        print(json.dumps({
            "status":report["status"],
            "cases":report["original_case_count"],
            "claims":report["new_claim_count"],
            "missing_case_sources":len(report["case_source_missing"]),
            "missing_claim_sources":len(report["claim_source_missing"]),
        },sort_keys=True))
        return 0
    except (MatrixError, OSError, TypeError, ValueError) as exc:
        print("IMPLEMENTATION MATRIX BLOCKED:",exc,file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())
