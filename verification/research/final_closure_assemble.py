"""Assemble an UNREVIEWED external premerge receipt candidate from real H CI.

This tool cannot manufacture case/claim decisions or reviewer IDs. Those
remain empty pending independent, exact-H scope review and signed payload
binding. Re-run on each final source H; never check future H into that H.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys

from final_closure_authenticate import (
    BASE, REQUIRED, authenticated_checks, git, AuthenticationError,
)
from final_closure_case_receipts import (
    ROOT, FORMAT, EvidenceError, load_detached_bundle,
)
from final_closure_schema import validate_overlay


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def assemble(head: str, synthetic: str, *, compiler_candidate: Path,
             mutation_candidates: Path, bundle: Path):
    if git("rev-parse", "HEAD") != head:
        raise AuthenticationError("reviewed Git worktree differs from branch HEAD")
    for h in (head, synthetic):
        if git("cat-file", "-t", h) != "commit":
            raise AuthenticationError("missing real source/synthetic Git object")
    if git("show", "-s", "--format=%P", synthetic).split() != [BASE, head]:
        raise AuthenticationError("wrong synthetic source B/H parent ordering")
    tree = git("rev-parse", head+"^{tree}")
    if git("rev-parse", synthetic+"^{tree}") != tree:
        raise AuthenticationError("synthetic merge changes source tree")
    checks = authenticated_checks(head)
    evidence = load_detached_bundle(bundle, sha(bundle.read_bytes()))
    source = json.loads(compiler_candidate.read_text())
    mutants = json.loads(mutation_candidates.read_text())
    if (source.get("head_sha") != head or
        source.get("status") != "COMPILER_ONLY_UNREVIEWED" or
        not isinstance(source.get("compiler_axiom_receipts"), list) or
        not source["compiler_axiom_receipts"] or
        not isinstance(mutants, list)):
        raise EvidenceError("candidate compiler/mutant sources are incomplete")
    compiler = []
    for row in source["compiler_axiom_receipts"]:
        if row.get("head_sha") != head or row.get("compiler_result") != "PASS":
            raise EvidenceError("wrong head or false proof candidate")
        copy = dict(row)
        copy.pop("CI_binding", None)
        copy.pop("independent_review", None)
        # CI passed at H, but did NOT necessarily execute this detached probe.
        copy["check_run_id"] = None
        compiler.append(copy)
    negatives, positives = [], []
    for row in mutants:
        if row.get("head_sha") != head or row.get("outcome") != "REJECTED_SEMANTIC":
            raise EvidenceError("unverified mutation source or wrong head")
        negative = dict(row)
        negative.pop("CI_binding", None)
        negative.pop("review_status", None)
        # A matching CI check alone never authenticates local mutation logs.
        negative["check_run_id"] = None
        negatives.append(negative)
        positive = dict(negative)
        positive["id"] = "positive:" + negative["id"]
        positive["outcome"] = "PASS"
        positive["compiler_exit_code"] = 0
        positive["log_member"] = negative["positive_control"]["log_member"]
        positive["log_sha256"] = negative["positive_control"]["log_sha256"]
        for key in ("mutant_source_member", "mutant_source_sha256",
                    "original_lean_source_sha256",
                    "original_lean_source_path"):
            positive.pop(key, None)
        positives.append(positive)
    for row in compiler:
        if row["axiom_log_member"] not in evidence:
            raise EvidenceError("compiler axiom log not sealed into evidence bundle")
    for row in negatives:
        for key in ("log_member", "mutant_source_member"):
            if row[key] not in evidence:
                raise EvidenceError("semantic mutant source/log missing from bundle")
    out = {
        "format": FORMAT,
        "phase": "premerge_review",
        "base_sha": BASE,
        "head_sha": head,
        "synthetic_sha": synthetic,
        "merged_main_sha": None,
        "actual_synthetic_parents": [BASE, head],
        "synthetic_tree_sha": tree,
        "evidence_bundle_sha256": sha(bundle.read_bytes()),
        "source_bound_ci": [
            {"name": name, "id": checks[name]["id"], "head_sha": head}
            for name in sorted(REQUIRED)],
        "compiler_axiom_receipts": compiler,
        "positive_test_receipts": positives,
        "semantic_negative_receipts": negatives,
        "case_decisions": [],
        "claim_decisions": [],
        "independent_source_reviews": [],
        "trusted_axioms": ["Classical.choice", "Quot.sound", "propext"],
    }
    validate_overlay(out)
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True)
    ap.add_argument("--synthetic", required=True)
    ap.add_argument("--compiler-candidate", required=True, type=Path)
    ap.add_argument("--mutation-candidates", required=True, type=Path)
    ap.add_argument("--bundle", required=True, type=Path)
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args(argv)
    try:
        if args.output.resolve().is_relative_to(ROOT.resolve()):
            raise EvidenceError("external reviewed data must not be committed into H")
        payload = assemble(args.head, args.synthetic,
                           compiler_candidate=args.compiler_candidate,
                           mutation_candidates=args.mutation_candidates,
                           bundle=args.bundle)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(payload, indent=2, sort_keys=True)+"\n")
    except (OSError, KeyError, ValueError, AuthenticationError) as exc:
        print("PREMERGE RECEIPT ASSEMBLY BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({"source": args.head, "status": "UNREVIEWED_SOURCE_CANDIDATE",
                      "case_decisions": 0, "claim_decisions": 0}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
