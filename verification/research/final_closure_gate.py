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
    EvidenceError, FORMAT, FORMAT_V3, load_detached_bundle, effective_acceptance,
)
from final_closure_verify import (
    GateError, NEW, read_json, strict,
)
from final_closure_schema import validate_overlay
from final_closure_full_contract import require_full_source, require_complete_obligation_receipts


def premerge(receipts: dict, bundle: Path, *, full: bool = False):
    validate_overlay(receipts)
    if receipts.get("format") not in (FORMAT, FORMAT_V3) or \
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
    if full:
        if receipts.get("format") != FORMAT_V3:
            raise GateError("complete premerge 45/11 requires authenticated v3 producers")
        source_map = read_json(NEW/"acceptance_case_source_map.json")
        full_result = require_full_source(
            verified, decisions, inventory["claims"], source_map)
        claim_map = read_json(NEW/"claim_declaration_map.json")
        full_result.update(require_complete_obligation_receipts(
            receipts, source_map, claim_map))
    else:
        if verified["accepted_case_count"] + verified["accepted_claim_count"] == 0:
            raise GateError("no exact source-scope case or claim independently reviewed")
        full_result = {}
    return {**verified, **full_result,
            "gate": "PREMERGE_FULL_SOURCE_READY" if full else
                    "PREMERGE_REVIEWED_CANDIDATE",
            "source_head": provenance["H"],
            "synthetic_sha": provenance["S"],
            "merged_main_sha": None,
            "merge_authorized": False,
            "scientific_release_approved": False}


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase",
                        choices=("premerge", "premerge-full", "full45-strict",
                                 "scoped-release-strict",
                                 "postmerge-preseal-strict",
                                 "full-release-strict"),
                        required=True)
    parser.add_argument("--receipts", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--approved-manifest", type=Path)
    parser.add_argument("--reproduction-zip", type=Path)
    parser.add_argument("--reproduction-ids", type=Path)
    parser.add_argument("--postseal-zip", type=Path)
    parser.add_argument("--postseal-ids", type=Path)
    opts = parser.parse_args(argv)
    try:
        receipts = json.loads(opts.receipts.read_bytes())
        if opts.phase in ("premerge", "premerge-full"):
            result = premerge(receipts, opts.bundle,
                              full=opts.phase == "premerge-full")
        else:
            manifest = (
                json.loads(opts.approved_manifest.read_bytes())
                if opts.approved_manifest else None)
            if bool(opts.reproduction_zip) != bool(opts.reproduction_ids):
                raise GateError("merged-M reproduction artifact and IDs must be paired")
            reproduction = ({
                "zip_file": opts.reproduction_zip,
                "identities": json.loads(opts.reproduction_ids.read_bytes())}
                if opts.reproduction_zip else None)
            if bool(opts.postseal_zip) != bool(opts.postseal_ids):
                raise GateError("postseal original artifact and IDs must be paired")
            postseal = ({
                "zip_file":opts.postseal_zip,
                "identities":json.loads(opts.postseal_ids.read_bytes())}
                if opts.postseal_zip else None)
            result = strict(receipts, opts.phase, manifest,
                            bundle_path=opts.bundle,
                            reproduction_attachment=reproduction,
                            postseal_attachment=postseal)
    except (GateError, EvidenceError, AuthenticationError,
            OSError, KeyError, ValueError) as exc:
        print("NOT ACCEPTED:", exc, file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
