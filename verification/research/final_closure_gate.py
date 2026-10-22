#!/usr/bin/env python3
"""Explicit premerge REVIEW gate and postmerge strict acceptance entrypoint.

A premerge reviewed integration candidate is NOT mathematical full45 or
scientific release approval. This script never merges or tags Git objects.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from final_closure_authenticate import (
    AuthenticationError, verify_premerge,
)
from final_closure_case_receipts import (
    EvidenceError, FORMAT, load_detached_bundle, effective_acceptance,
)
from final_closure_verify import (
    GateError, NEW, read_json, strict,
)
from final_closure_schema import validate_overlay


def premerge(receipts: dict, bundle: Path):
    validate_overlay(receipts)
    if receipts.get("format") != FORMAT or \
       receipts.get("phase") != "premerge_review" or \
       receipts.get("merged_main_sha") is not None:
        raise GateError("premerge requires detached v2 source, no future M")
    provenance = verify_premerge(receipts, require_independent_review=True)
    members = load_detached_bundle(bundle, receipts.get("evidence_bundle_sha256"))
    decisions = read_json(NEW/"acceptance_decisions.json")
    inventory = read_json(NEW/"claim_inventory.json")
    verified = effective_acceptance(
        receipts, head=provenance["H"], case_ledger=decisions,
        claims=inventory["claims"], members=members,
        accepted_checks=provenance["checks"],
        approved_review_scopes=provenance["review_scopes"])
    if verified["accepted_case_count"] + verified["accepted_claim_count"] == 0:
        raise GateError("no exact source-scope case or claim independently reviewed")
    return {**verified,
            "gate": "PREMERGE_REVIEWED_CANDIDATE",
            "source_head": provenance["H"],
            "synthetic_sha": provenance["S"],
            "merged_main_sha": None,
            "merge_authorized": False,
            "scientific_release_approved": False}


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase",
                        choices=("premerge", "full45-strict",
                                 "scoped-release-strict"),
                        required=True)
    parser.add_argument("--receipts", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--approved-manifest", type=Path)
    opts = parser.parse_args(argv)
    try:
        receipts = json.loads(opts.receipts.read_bytes())
        if opts.phase == "premerge":
            result = premerge(receipts, opts.bundle)
        else:
            manifest = (
                json.loads(opts.approved_manifest.read_bytes())
                if opts.approved_manifest else None)
            result = strict(receipts, opts.phase, manifest,
                            bundle_path=opts.bundle)
    except (GateError, EvidenceError, AuthenticationError,
            OSError, KeyError, ValueError) as exc:
        print("NOT ACCEPTED:", exc, file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
