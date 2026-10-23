"""Exact-head collection of ALL actual PR113 CI producing artifacts.

This is a detached, read-only *candidate evidence* assembler, NOT an
independent case review or mathematical release. It authenticates the real
run/job/check/artifact SHA256 through GitHub for 4 compiler, 9 append-source,
and 8 legacy-original shards. Then it replays the existing full 45/11 theorem
shard merger on the retained compiler outputs.

No ordinary 'research' green check is attributed to a separate candidate
compiler or mutation. No unchecked status flags become approvals.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile

from final_closure_authenticate import AuthenticationError
from final_closure_candidate_artifact_auth import KINDS, verify_artifact
from final_closure_case_receipts import EvidenceError, load_detached_bundle
from final_closure_complete_lean_evidence import ROOT, git_head
from final_closure_merge_compiler_shards import merge, ShardMergeError
from final_closure_all_original_semantics import select_cases
from final_closure_legacy_semantic_evidence import original_case_map

FORMAT = "Permansson.PR113.ExternalProducerCatalog.v1"
OUT_FORMAT = "Permansson.PR113.ExactHeadProducingEvidence.v1"
SHA40 = re.compile(r"^[a-f0-9]{40}$")
MAX_INPUT_BYTES = 64 * 1024 * 1024
MAX_TOTAL_BYTES = 256 * 1024 * 1024


class ProducerCatalogError(ValueError):
    pass


def need(ok, reason):
    if not ok:
        raise ProducerCatalogError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def entries(catalog, head):
    """Check shape and full disjoint 4+9+8 coverage without network access."""
    need(isinstance(head, str) and SHA40.fullmatch(head),
         "invalid source head")
    need(isinstance(catalog, dict) and
         catalog.get("format") == FORMAT and
         catalog.get("head_sha") == head,
         "catalog belongs to wrong source head or schema")
    data = catalog.get("artifacts")
    expected = {(kind, i) for kind, spec in KINDS.items()
                for i in range(spec["count"])}
    need(isinstance(data, list) and len(data) == len(expected),
         "missing or extra required CI producer shards")
    seen, ids, result = set(), set(), []
    for row in data:
        need(isinstance(row, dict) and
             set(row) == {"kind", "shard", "run_id", "artifact_id", "zip_file"},
             "untyped producing artifact entry")
        kind, shard = row["kind"], row["shard"]
        need(type(kind) is str and type(shard) is int and
             (kind, shard) in expected and (kind, shard) not in seen,
             "duplicate/unexpected/missing producer shard")
        seen.add((kind, shard))
        need(type(row["run_id"]) is int and row["run_id"] > 0 and
             type(row["artifact_id"]) is int and row["artifact_id"] > 0 and
             row["artifact_id"] not in ids,
             "duplicate or malformed producing artifact ID")
        ids.add(row["artifact_id"])
        name = row["zip_file"]
        need(isinstance(name, str) and
             re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9_.-]{0,180}[.]zip", name) and
             name not in (".zip", "..zip") and
             "/" not in name and chr(92) not in name,
             "unsafe or nonflat detached artifact ZIP path")
        result.append(row)
    need(seen == expected, "incomplete source-producer coverage")
    return sorted(result, key=lambda r: (r["kind"], r["shard"]))


def collect(*, head, catalog_path: Path, output: Path):
    catalog_path = Path(catalog_path)
    output = Path(output)
    root = ROOT.resolve()
    need(catalog_path.is_file() and not catalog_path.is_symlink() and
         not catalog_path.resolve().is_relative_to(root),
         "external, nonsymlinked catalog required")
    input_dir = catalog_path.resolve().parent
    output = output.resolve()
    need(not output.exists() and
         not output.is_relative_to(root) and
         not output.is_relative_to(input_dir) and
         not input_dir.is_relative_to(output),
         "output must be a new, separate external evidence directory")
    need(git_head() == head, "checked-out source is not requested H")
    rows = entries(json.loads(catalog_path.read_bytes()), head)
    total = 0
    trusted = []
    with tempfile.TemporaryDirectory(prefix="pr113-producer-check-") as td:
        shard_root = Path(td) / "compiler-shards"
        shard_root.mkdir()
        for row in rows:
            artifact = input_dir / row["zip_file"]
            need(artifact.is_file() and not artifact.is_symlink() and
                 artifact.resolve().parent == input_dir and
                 0 < artifact.stat().st_size <= MAX_INPUT_BYTES,
                 "unsafe or missing actual producing artifact")
            total += artifact.stat().st_size
            need(total <= MAX_TOTAL_BYTES, "aggregate artifact size exceeded")
            verified = verify_artifact(
                kind=row["kind"], shard=row["shard"], head=head,
                run_id=row["run_id"], artifact_id=row["artifact_id"],
                artifact_zip=artifact)
            need(verified["status"] ==
                 "CI_ARTIFACT_DIGEST_VERIFIED_UNREVIEWED" and
                 verified["head_sha"] == head and
                 verified["artifact_id"] == row["artifact_id"],
                 "producing CI attestation is unverified or mismatched")
            trusted.append(verified)
            if row["kind"] == "compiler":
                members = load_detached_bundle(
                    artifact, verified["artifact_sha256"])
                folder = shard_root / ("shard-%02d" % row["shard"])
                need(not folder.exists(), "duplicate compiler shard directory")
                folder.mkdir()
                for member, content in members.items():
                    target = folder.joinpath(*member.split("/"))
                    need(target.resolve().is_relative_to(folder.resolve()),
                         "unsafe compiler evidence member")
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(content)
        output.mkdir(parents=True, exist_ok=False)
        full = merge(shard_root, output / "compiler", head=head)
        need(full["case_count"] == 45 and full["claim_count"] == 11 and
             full["proof_count"] == full["inventory_count"],
             "complete 45/11 compiler theorem coverage not proven")
    from final_closure_all_original_semantics import EXPECTED
    original, legacy_cases = original_case_map(head)
    need(len(original) == 45 and len(EXPECTED) == 25 and
         len(legacy_cases) == 20 and
         not (EXPECTED & set(legacy_cases)) and
         set(original) == EXPECTED | set(legacy_cases),
         "original 25+20 original-case partition changed")
    report = {
        "format": OUT_FORMAT,
        "status": "CI_PRODUCER_ARTIFACTS_AUTHENTICATED_UNREVIEWED",
        "head_sha": head,
        "producing_artifact_count": len(trusted),
        "compiler_targets_executed": full["proof_count"],
        "original_cases_in_canonical_map": 45,
        "claim_ids_in_canonical_map": 11,
        "append_candidate_routes": 25,
        "legacy_observation_routes": 20,
        "producer_artifact_checks": trusted,
        "merged_compiler_sha256": digest(
            (output / "compiler" / "complete_compiler_candidate.json").read_bytes()),
        "independent_source_review": False,
        "semantic_criterion_acceptance": False,
        "mathematical_release_approved": False,
        "merged_main_sha": None,
    }
    (output / "unreviewed_producer_catalog.json").write_text(
        json.dumps(report, sort_keys=True, indent=2) + "\n",
        encoding="utf-8")
    return report


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True)
    ap.add_argument("--catalog", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    opts = ap.parse_args(argv)
    try:
        result = collect(head=opts.head, catalog_path=opts.catalog,
                         output=opts.output)
    except (ProducerCatalogError, AuthenticationError, EvidenceError,
            ShardMergeError, OSError, KeyError, ValueError) as exc:
        print("PR113 PRODUCER CATALOG BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({k: result[k] for k in (
        "status", "head_sha", "producing_artifact_count",
        "compiler_targets_executed")}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
