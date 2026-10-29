"""Survey exact-H positive-route and claim-test candidates (P1-06/P1-08).

Reads ONLY the committed exact-H case/claim maps and the committed test and
Lean source blobs they name. It enumerates every original-case positive
route and every claim's test/Lean candidates, checks by AST that a named
test method is defined in exactly one class, and flags each choice that a
reviewer must still make. It writes a detached UNREVIEWED JSON/Markdown
survey, never a selection: method discovery is NOT mathematical relevance,
and no negative Lean statement is ever invented here.
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

from pr113_v31_execution_integrity import (
    CASE_MAP, CLAIM_MAP, CLAIMS, ExactSource, LEAN_PATH, POSITIVE_ROLES,
    RealControlError, TEST_METHOD, TEST_PATH, git_blob_reader, json_bytes,
)

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.SelectionCandidateSurvey.v1"
JSON_NAME = "selection_candidate_survey.json"
MARKDOWN_NAME = "selection_candidate_survey.md"
CASE_COUNT = 45
CASE_ID = re.compile(r"^[A-Za-z][A-Za-z0-9_-]{1,30}$")
ROLES = frozenset(POSITIVE_ROLES) | {"SEMANTIC_NEGATIVE", "SCOPE_BOUNDARY"}
SHA40 = re.compile(r"^[0-9a-f]{40}$")


class SurveyError(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise SurveyError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def committed(source, path):
    """Committed exact-H bytes, or None when the path is absent at H."""
    try:
        return source.blob(path)
    except RealControlError:
        return None


def parsed(raw, path):
    try:
        return ast.parse(raw.decode("utf-8"), filename=path)
    except (ValueError, UnicodeError, SyntaxError) as exc:
        raise SurveyError("exact-H test source is not parseable: " +
                          path) from exc


def defining_classes(tree, method):
    return sorted(
        node.name for node in tree.body if isinstance(node, ast.ClassDef) and
        any(isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef)) and
            inner.name == method for inner in node.body))


def test_methods(tree):
    return {
        node.name: sorted(
            inner.name for inner in node.body
            if isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef)) and
            TEST_METHOD.fullmatch(inner.name))
        for node in tree.body if isinstance(node, ast.ClassDef)
    }


def route_record(source, route):
    path, method = route["path"], route["method"]
    raw = committed(source, path)
    record = {"path": path, "method": method, "role": route["role"],
              "test_source_sha256": None, "defining_classes": []}
    if raw is None:
        record["status"] = "ABSENT_TEST_SOURCE"
        return record
    classes = defining_classes(parsed(raw, path), method)
    record["test_source_sha256"] = sha(raw)
    record["defining_classes"] = classes
    record["status"] = ("ELIGIBLE_UNREVIEWED" if len(classes) == 1 else
                        "ABSENT_METHOD" if not classes else "AMBIGUOUS_CLASS")
    return record


def provider_records(source, rows, *, name_key):
    need(isinstance(rows, list) and rows,
         "owner declares no Lean provider")
    by_path = {}
    for row in rows:
        need(isinstance(row, dict) and isinstance(row.get("path"), str) and
             LEAN_PATH.fullmatch(row["path"]) is not None and
             ".." not in row["path"].split("/") and
             isinstance(row.get(name_key), str) and row[name_key],
             "foreign or malformed Lean provider declaration")
        by_path.setdefault(row["path"], set()).add(row[name_key])
    records = []
    for path in sorted(by_path):
        raw = committed(source, path)
        records.append({
            "path": path,
            "declarations": sorted(by_path[path]),
            "present_at_head": raw is not None,
            "source_sha256": None if raw is None else sha(raw),
        })
    return records


def survey_case(source, case):
    cid = case.get("case_id")
    routes = case.get("test_method_candidates")
    need(isinstance(cid, str) and CASE_ID.fullmatch(cid) and
         isinstance(routes, list), "malformed original case owner")
    seen = set()
    for route in routes:
        need(isinstance(route, dict) and
             isinstance(route.get("path"), str) and
             TEST_PATH.fullmatch(route["path"]) is not None and
             isinstance(route.get("method"), str) and
             TEST_METHOD.fullmatch(route["method"]) is not None and
             route.get("role") in ROLES,
             "malformed or foreign test route for case " + cid)
        key = (route["path"], route["method"], route["role"])
        need(key not in seen, "duplicate test route for case " + cid)
        seen.add(key)
    ordered = sorted(routes, key=lambda r: (r["path"], r["method"], r["role"]))
    positive = [route_record(source, r) for r in ordered
                if r["role"] in POSITIVE_ROLES]
    negative = [route_record(source, r) for r in ordered
                if r["role"] == "SEMANTIC_NEGATIVE"]
    providers = provider_records(
        source, case.get("historical_proof_declarations"), name_key="name")
    eligible = [r for r in positive if r["status"] == "ELIGIBLE_UNREVIEWED"]
    present = [p for p in providers if p["present_at_head"]]
    flags = set()
    if len(eligible) > 1:
        flags.add("MULTIPLE_ELIGIBLE_POSITIVE_ROUTES")
    if not eligible:
        flags.add("NO_ELIGIBLE_POSITIVE_ROUTE")
    if any(r["status"] != "ELIGIBLE_UNREVIEWED" for r in positive):
        flags.add("INELIGIBLE_POSITIVE_ROUTE_PRESENT")
    if len(present) > 1:
        flags.add("MULTIPLE_LEAN_PROVIDERS")
    if not present:
        flags.add("NO_LEAN_PROVIDER_AT_HEAD")
    if len({(r["path"], r["method"]) for r in negative}) > 1:
        flags.add("MULTIPLE_SEMANTIC_NEGATIVE_ROUTES")
    choices = ["confirm the chosen positive route tests this case's original "
               "criterion (discovery is not relevance)"]
    if len(eligible) > 1:
        choices.append("choose one of %d eligible positive routes" %
                       len(eligible))
    if len(present) > 1:
        choices.append("choose the Lean provider among %d present at H" %
                       len(present))
    if not eligible or not present:
        choices.append("supply a missing positive route or Lean provider; "
                       "this case cannot be selected yet")
    return {
        "case_id": cid,
        "eligible_positive_route_count": len(eligible),
        "positive_routes": positive,
        "semantic_negative_routes": negative,
        "scope_boundary_route_count": sum(
            r["role"] == "SCOPE_BOUNDARY" for r in routes),
        "lean_providers": providers,
        "flags": sorted(flags),
        "coverage_complete": bool(eligible and present),
        "reviewer_choices": choices,
    }


def survey_claim(source, claim, case_ids):
    cid = claim.get("claim_id")
    tests = claim.get("test_source_candidates")
    links = claim.get("original_case_links")
    need(cid in CLAIMS and isinstance(tests, list) and tests and
         len(set(tests)) == len(tests) and isinstance(links, list) and
         all(isinstance(x, str) and x in case_ids for x in links),
         "malformed claim owner or foreign original case link")
    providers = provider_records(
        source, claim.get("declarations"), name_key="declaration")
    need(claim.get("primary_path") in {p["path"] for p in providers},
         "claim primary provider is foreign to its declarations: " + cid)
    sources = []
    for path in sorted(tests):
        need(isinstance(path, str) and TEST_PATH.fullmatch(path) is not None,
             "foreign or malformed claim test source: " + cid)
        raw = committed(source, path)
        methods = {} if raw is None else test_methods(parsed(raw, path))
        sources.append({
            "path": path, "present_at_head": raw is not None,
            "test_source_sha256": None if raw is None else sha(raw),
            "test_methods_by_class": methods,
            "test_method_count": sum(len(m) for m in methods.values()),
        })
    present = [p for p in providers if p["present_at_head"]]
    available = sum(s["test_method_count"] for s in sources)
    flags = {"POSITIVE_AND_NEGATIVE_TEST_METHODS_REQUIRE_REVIEW",
             "FALSE_LEAN_STATEMENT_NOT_PROVIDED"}
    if len(present) > 1:
        flags.add("MULTIPLE_LEAN_PROVIDERS")
    if not present:
        flags.add("NO_LEAN_PROVIDER_AT_HEAD")
    if len(sources) == 1:
        flags.add("SINGLE_TEST_SOURCE")
    if not all(s["present_at_head"] for s in sources):
        flags.add("TEST_SOURCE_ABSENT_AT_HEAD")
    if available < 2:
        flags.add("FEWER_THAN_TWO_TEST_METHODS")
    return {
        "claim_id": cid,
        "original_case_links": sorted(links),
        "lean_providers": providers,
        "test_sources": sources,
        "negative_lean_statement": None,
        "negative_lean_statement_status":
            "NOT_PROVIDED_REVIEWER_MUST_AUTHOR_CRITERION_RELEVANT_FALSE_STATEMENT",
        "flags": sorted(flags),
        "coverage_complete": bool(present and available >= 2),
        "reviewer_choices": [
            "choose the Lean provider supporting this claim"
            if len(present) > 1 else
            "confirm the single Lean provider supports this claim",
            "choose distinct positive and negative test class/method from "
            "%d discovered test methods" % available,
            "author a claim-specific false Lean statement appended to the "
            "original provider (no import/axiom/sorry change)",
        ],
    }


def build_survey(head, case_raw, claim_raw, read):
    """Return the deterministic UNREVIEWED survey or fail closed."""
    need(isinstance(head, str) and SHA40.fullmatch(head) is not None,
         "exact 40-hex source head required")
    case_map, claim_map = json_bytes(case_raw), json_bytes(claim_raw)
    try:
        source = ExactSource(head, case_map, claim_map, read)
    except RealControlError as exc:
        raise SurveyError(str(exc)) from exc
    cases, claims = case_map["cases"], claim_map["claims"]
    need(len(source.cases) == CASE_COUNT and
         all(isinstance(cid, str) for cid in source.cases),
         "original case owners are missing, duplicated or malformed")
    need(set(source.claims) == CLAIMS and len(claims) == len(CLAIMS) and
         claim_map.get("count") == len(CLAIMS),
         "claim owners are missing, duplicated or foreign")
    surveyed_cases = [survey_case(source, case)
                      for case in sorted(cases, key=lambda c: c["case_id"])]
    surveyed_claims = [survey_claim(source, claim, set(source.cases))
                       for claim in sorted(claims, key=lambda c: c["claim_id"])]
    # A test file shared between claims risks one claim borrowing another's
    # positive/negative method; the reviewer must keep them claim-specific.
    owners = {}
    for claim in surveyed_claims:
        for test in claim["test_sources"]:
            owners.setdefault(test["path"], []).append(claim["claim_id"])
    for claim in surveyed_claims:
        for test in claim["test_sources"]:
            test["shared_with_claims"] = [
                cid for cid in owners[test["path"]] if cid != claim["claim_id"]]
        if any(test["shared_with_claims"] for test in claim["test_sources"]):
            claim["flags"] = sorted(
                set(claim["flags"]) | {"TEST_SOURCE_SHARED_WITH_OTHER_CLAIMS"})

    def flagged(rows, key, flag):
        return [row[key] for row in rows if flag in row["flags"]]

    complete = (all(c["coverage_complete"] for c in surveyed_cases) and
                all(c["coverage_complete"] for c in surveyed_claims))
    return {
        "format": FORMAT,
        "status": ("UNREVIEWED_SURVEY_COVERAGE_COMPLETE" if complete else
                   "UNREVIEWED_SURVEY_COVERAGE_INCOMPLETE"),
        "source_head": head,
        "case_map": {"path": CASE_MAP, "sha256": sha(case_raw),
                     "format": case_map.get("format"),
                     "status": case_map.get("status")},
        "claim_map": {"path": CLAIM_MAP, "sha256": sha(claim_raw),
                      "format": claim_map.get("format"),
                      "status": claim_map.get("status")},
        "summary": {
            "original_cases": len(surveyed_cases),
            "claims": len(surveyed_claims),
            "coverage_complete": complete,
            "cases_with_multiple_eligible_positive_routes": flagged(
                surveyed_cases, "case_id", "MULTIPLE_ELIGIBLE_POSITIVE_ROUTES"),
            "cases_with_multiple_lean_providers": flagged(
                surveyed_cases, "case_id", "MULTIPLE_LEAN_PROVIDERS"),
            "cases_with_multiple_semantic_negative_routes": flagged(
                surveyed_cases, "case_id",
                "MULTIPLE_SEMANTIC_NEGATIVE_ROUTES"),
            "cases_with_ineligible_positive_routes": flagged(
                surveyed_cases, "case_id", "INELIGIBLE_POSITIVE_ROUTE_PRESENT"),
            "cases_without_complete_coverage": [
                c["case_id"] for c in surveyed_cases
                if not c["coverage_complete"]],
            "claims_requiring_positive_negative_test_choice": flagged(
                surveyed_claims, "claim_id",
                "POSITIVE_AND_NEGATIVE_TEST_METHODS_REQUIRE_REVIEW"),
            "claims_with_multiple_lean_providers": flagged(
                surveyed_claims, "claim_id", "MULTIPLE_LEAN_PROVIDERS"),
            "claims_sharing_test_sources": flagged(
                surveyed_claims, "claim_id",
                "TEST_SOURCE_SHARED_WITH_OTHER_CLAIMS"),
            "claims_without_complete_coverage": [
                c["claim_id"] for c in surveyed_claims
                if not c["coverage_complete"]],
        },
        "cases": surveyed_cases,
        "claims": surveyed_claims,
        "selection_written": False,
        "independent_review": False,
        "mathematical_relevance_established": False,
        "accepted_cases": 0,
        "accepted_claims": 0,
    }


def markdown(report):
    summary = report["summary"]

    def ids(values):
        return ", ".join(values) if values else "none"

    lines = [
        "# PR113 selection candidate survey (UNREVIEWED)",
        "",
        "Generated from committed exact-H maps; not a selection, review or "
        "acceptance. Method discovery does not establish mathematical "
        "relevance, and no negative Lean statement is provided.",
        "",
        "- Source head: `%s`" % report["source_head"],
        "- Case map SHA-256: `%s`" % report["case_map"]["sha256"],
        "- Claim map SHA-256: `%s`" % report["claim_map"]["sha256"],
        "- Status: `%s`" % report["status"],
        "",
        "## Summary",
        "",
        "| Item | Owners |",
        "|---|---|",
    ]
    for key in sorted(k for k in summary if isinstance(summary[k], list)):
        lines.append("| %s (%d) | %s |" % (
            key.replace("_", " "), len(summary[key]), ids(summary[key])))
    lines += ["", "## Original cases", "",
              "| Case | Eligible positive routes | Lean providers | Flags |",
              "|---|---|---|---|"]
    for case in report["cases"]:
        lines.append("| %s | %s | %s | %s |" % (
            case["case_id"],
            "<br>".join("`%s::%s.%s` (%s, %s)" % (
                r["path"], ",".join(r["defining_classes"]) or "-",
                r["method"], r["role"], r["status"])
                for r in case["positive_routes"]),
            "<br>".join("`%s`%s" % (p["path"], "" if p["present_at_head"]
                                    else " (absent)")
                        for p in case["lean_providers"]),
            ", ".join(case["flags"]) or "-"))
    lines += ["", "## Claims", "",
              "| Claim | Lean providers | Test sources (methods) | Flags |",
              "|---|---|---|---|"]
    for claim in report["claims"]:
        lines.append("| %s | %s | %s | %s |" % (
            claim["claim_id"],
            "<br>".join("`%s`" % p["path"] for p in claim["lean_providers"]),
            "<br>".join("`%s` (%d)" % (s["path"], s["test_method_count"])
                        for s in claim["test_sources"]),
            ", ".join(claim["flags"])))
    return "\n".join(lines) + "\n"


def write(head, output):
    need(isinstance(head, str) and SHA40.fullmatch(head) is not None,
         "exact 40-hex source head required")
    actual = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                            capture_output=True, text=True, timeout=30)
    need(actual.returncode == 0 and actual.stdout.strip() == head,
         "stale/not actual exact-H source checkout")
    target = Path(output)
    need(not target.is_symlink() and
         not target.name.startswith("reviewed_"),
         "survey output must not be symlinked or named as a reviewed input")
    target = target.resolve()
    need(not target.exists() and not target.is_relative_to(ROOT.resolve()),
         "survey output must be a new directory outside the Git checkout")
    read = git_blob_reader(head, ROOT)
    try:
        case_raw, claim_raw = read(CASE_MAP), read(CLAIM_MAP)
    except RealControlError as exc:
        raise SurveyError(str(exc)) from exc
    report = build_survey(head, case_raw, claim_raw, read)
    target.mkdir(parents=True)
    (target / JSON_NAME).write_text(
        json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    (target / MARKDOWN_NAME).write_text(markdown(report), encoding="utf-8")
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        report = write(args.head, args.out)
    except (SurveyError, RealControlError, OSError, KeyError,
            TypeError) as exc:
        print("PR113 SELECTION SURVEY BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({"status": report["status"],
                      "original_cases": report["summary"]["original_cases"],
                      "claims": report["summary"]["claims"]},
                     sort_keys=True))
    return 0 if report["summary"]["coverage_complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
