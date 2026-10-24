"""Package actual twenty legacy and eleven claim-control executions for v3.1.

Inputs must be the original detached outputs of the real Lean/unittest
executors, never hand-authored acceptance rows. This adds *unreviewed* CI
ownership only. The final v3.1 verifier separately authenticates the real
GitHub workflow, job, check, artifact digest and entire member set.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

from pr113_v31_execution_integrity import (
    verify_owner, RealControlError, REQUIRED_CLAIM_MEMBERS,
)

ROOT = Path(__file__).resolve().parents[2]
INDEX_FORMAT = "Permansson.PR113.AdditionalControlProducerIndex.v1"
ID = re.compile(r"^[A-Za-z][A-Za-z0-9_-]{1,40}$")
CLAIMS = frozenset(("Q1", "Q2", "Q3", "M1", "M2", "M3",
                    "N1", "N2", "N3", "D8", "D9"))


class PackError(ValueError):
    pass


def need(ok, msg):
    if not ok:
        raise PackError(msg)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def secure_file(path):
    raw = Path(path).absolute()
    need(not any(p.is_symlink() for p in (raw, *raw.parents)) and
         raw.is_file(), "untrusted producer source file or symlink: " +
         str(path))
    return raw.read_bytes()


def secure_source(source):
    given = Path(source).absolute()
    need(not any(x.is_symlink() for x in (given, *given.parents)),
         "source artifact path contains a symlink")
    root = given.resolve(strict=True)
    need(root.is_dir() and not root.is_relative_to(ROOT.resolve()) and
         not ROOT.resolve().is_relative_to(root),
         "original executed evidence must live outside checkout")
    return root


def safe_output(output, source):
    given = Path(output).absolute()
    need(not any(p.is_symlink() for p in (given, *given.parents)) and
         not given.exists() and
         not given.is_relative_to(source) and
         not given.is_relative_to(ROOT.resolve()) and
         not ROOT.resolve().is_relative_to(given),
         "candidate producer output must be fresh and outside source")
    return given


def manifest(head, run_id, run_attempt, kind, source, output):
    need(isinstance(head, str) and re.fullmatch("[0-9a-f]{40}", head),
         "original exact head SHA required")
    need(type(run_id) is int and run_id > 0 and
         type(run_attempt) is int and run_attempt > 0,
         "real positive GitHub run and attempt numbers required")
    need(kind in ("legacy_negative", "claim_pair"),
         "unsupported CI producer ownership kind")
    source = secure_source(source)
    target = safe_output(output, source)
    if kind == "legacy_negative":
        data = json.loads(secure_file(
            source / "unreviewed_batch_replays.json"))
        rows = data.get("replays")
        need(data.get("format") ==
             "Permansson.PR113.LegacyBatchAppendOnlyCandidate.v1" and
             data.get("status") ==
             "TWENTY_REAL_LEAN_REPLAYS_UNREVIEWED_NOT_CI_BOUND" and
             data.get("source_head") == head and
             data.get("replayed_case_count") == 20 and
             data.get("new_source_bound_CI_acceptance") is False and
             data.get("independent_case_reviews") == 0 and
             data.get("mathematical_release_approved") is False and
             isinstance(rows, list) and len(rows) == 20,
             "actual 20 original source-appended executions missing")
    else:
        data = json.loads(secure_file(
            source / "unreviewed_11_claim_control_summary.json"))
        rows = data.get("claim_controls")
        need(data.get("format") ==
             "Permansson.PR113.ClaimControlsCandidate.v1" and
             data.get("status") ==
             "ALL_ELEVEN_EXECUTED_UNREVIEWED_NO_CI_ATTRIBUTION" and
             data.get("source_head") == head and
             data.get("actual_new_claims_executed") == 11 and
             data.get("actual_producing_ci_check_run_id") is None and
             data.get("independent_claim_reviews") == 0 and
             data.get("mathematical_release_approved") is False and
             isinstance(rows, list) and len(rows) == 11,
             "all eleven genuine claim controls are not executed")
    expected_ids = ([row.get("case_id") for row in rows]
                    if kind == "legacy_negative" else
                    [row.get("claim_id") for row in rows])
    need(all(isinstance(cid, str) and ID.fullmatch(cid)
             for cid in expected_ids) and
         len(set(expected_ids)) == len(rows) and
         (kind != "claim_pair" or set(expected_ids) == CLAIMS),
         "actual original source owner IDs are not unique or complete")

    # Authenticate every original member before creating ANY release artifact.
    payloads = []
    total_bytes = 0
    for row in sorted(rows, key=lambda item: item[
            "case_id" if kind == "legacy_negative" else "claim_id"]):
        cid = row["case_id" if kind == "legacy_negative" else "claim_id"]
        if kind == "legacy_negative":
            original = secure_file(source / cid / "unreviewed_replay.json")
            replay = json.loads(original)
            binary = secure_file(source / cid / "semantic_replay_candidate.zip")
            need(row.get("replay_bundle_sha256") == sha(binary) and
                 replay.get("detached_bundle_sha256") == sha(binary) and
                 row.get("status") ==
                    "SOURCE_APPENDED_REPLAYED_UNREVIEWED_NOT_CI_ATTRIBUTED" and
                 row.get("new_replay_producer_check_run_id") is None and
                 type(row.get("original_legacy_producing_artifact_id")) is int and
                 row["original_legacy_producing_artifact_id"] > 0,
                 "historical nested semantic replay cannot be traced to source")
            base = "legacy/" + cid + "/"
            path = base + "unreviewed_legacy_ci.json"
            wrapped = {
                "status": row["status"],
                "head_sha": head,
                "case_id": cid,
                "historical_producing_artifact_id":
                    row["original_legacy_producing_artifact_id"],
                "actual_ci_check_run_id": None,
                "execution_receipt_member":
                    base + "original_unreviewed_replay.json",
                "execution_receipt_sha256": sha(original),
                "semantic_zip_member": base + "semantic_replay_candidate.zip",
                "semantic_zip_sha256": sha(binary),
                "independent_case_review": False,
                "mathematical_acceptance": False,
                "scientific_release_approved": False,
            }
            meta = (json.dumps(wrapped, sort_keys=True, indent=2) +
                    "\n").encode("utf-8")
            entries = {
                path: meta,
                base + "original_unreviewed_replay.json": original,
                base + "semantic_replay_candidate.zip": binary,
            }
        else:
            original = secure_file(
                source / cid / "unreviewed_claim_control.json")
            receipt = json.loads(original)
            need(receipt == row and
                 receipt.get("status") ==
                 "LEAN_POSITIVE_AND_FALSE_MUTANT_EXECUTED_UNREVIEWED" and
                 receipt.get("head_sha") == head and
                 receipt.get("actual_ci_check_run_id") is None,
                 "claim source controller differs from original summary")
            base = "claim/" + cid + "/"
            path = base + "unreviewed_claim_control.json"
            entries = {path: original}
            for name in sorted(REQUIRED_CLAIM_MEMBERS):
                entries[base + name] = secure_file(source / cid / name)
            meta = original
        total_bytes += sum(len(x) for x in entries.values())
        need(total_bytes <= 256 * 1024 * 1024,
             "control original evidence exceeded aggregate ZIP budget")
        # The same exact verifier will re-run on GitHub's original uploaded ZIP.
        need(verify_owner(kind, cid, path, entries, head)["owner_id"] == cid,
             "original executed Lean/source evidence is invalid")
        payloads.append((cid, path, meta, entries))

    target.mkdir(parents=True)
    all_entries = {}
    owners = []
    for cid, path, raw, entries in payloads:
        owners.append({
            "kind": kind, "owner_id": cid,
            "receipt_member": path, "receipt_sha256": sha(raw),
        })
        for name, bytes_ in entries.items():
            need(name not in all_entries, "duplicate output source member")
            all_entries[name] = bytes_
    for name, bytes_ in sorted(all_entries.items()):
        file = target / name
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_bytes(bytes_)
    index = {
        "format": INDEX_FORMAT,
        "head_sha": head,
        "github_run_id": run_id,
        "github_run_attempt": run_attempt,
        "accepted_cases": 0,
        "accepted_claims": 0,
        "independent_review": False,
        "owners": owners,
    }
    (target / "owner_index.json").write_text(
        json.dumps(index, sort_keys=True, indent=2) + "\n")
    return index


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head", required=True)
    parser.add_argument("--kind", choices=("legacy_negative", "claim_pair"),
                        required=True)
    parser.add_argument("--run-id", required=True, type=int)
    parser.add_argument("--run-attempt", required=True, type=int)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        result = manifest(args.head, args.run_id, args.run_attempt,
                          args.kind, args.source, args.output)
    except (PackError, RealControlError, OSError, ValueError,
            KeyError, TypeError) as exc:
        print("PR113 SOURCE-OWNED CONTROL PACKAGING BLOCKED:", exc,
              file=sys.stderr)
        return 2
    print(json.dumps({"status": "EXECUTED_CI_OWNERS_UNREVIEWED",
                      "control_owners": len(result["owners"])}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
