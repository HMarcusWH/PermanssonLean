"""Fail-closed recombination of original 45-case / 11-claim compiler shards.

Accepted inputs: DETACHED per-shard raw logs and manifests which match
the exact reviewed source-owner inventory. The output is only an unreviewed
compiler candidate; its evidence still requires an authenticated GitHub
artifact, immutable exact-head CI check-run mapping, semantic false mutants,
and independent review. No check-run ID is asserted or synthesized.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

from closure_elaborated_type import (
    compiled_type_record, elaborated_type_sha256, TypeEvidenceError
)
from final_closure_case_receipts import (
    TRUSTED_AXIOMS, parse_target_axioms, EvidenceError,
)
from final_closure_complete_lean_evidence import (
    ROOT, required_inventory, inventory_digest, shard_indices, git_head
)

SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
MAX_LOG_BYTES = 4 * 1024 * 1024
MAX_TOTAL_BYTES = 64 * 1024 * 1024


class ShardMergeError(ValueError):
    pass


def need(ok, reason):
    if not ok:
        raise ShardMergeError(reason)


def sha(content):
    return hashlib.sha256(content).hexdigest()


def merge(shard_root: Path, output: Path, *, head: str,
          inventory: list[dict] | None = None) -> dict:
    need(isinstance(head, str) and SHA40.fullmatch(head),
         "invalid exact source head")
    need(git_head() == head, "source checkout does not match merged compiler H")
    shard_root = Path(shard_root).resolve()
    output = Path(output).resolve()
    need(shard_root.is_dir() and not shard_root.is_symlink() and
         not shard_root.is_relative_to(ROOT.resolve()) and
         not output.is_relative_to(ROOT.resolve()) and
         not output.is_relative_to(shard_root) and
         not shard_root.is_relative_to(output) and
         not output.exists(),
         "shard and merged output must be detached, disjoint and new")
    planned = required_inventory() if inventory is None else inventory
    need(isinstance(planned, list) and len(planned) >= 11,
         "canonical compiler source-owner inventory unavailable")
    fingerprint = inventory_digest(planned)
    # The shard tree must contain only numbered shard folders; never
    # silently skip a missing/cancelled shard or accept an extra directory.
    child_names = sorted(p.name for p in shard_root.iterdir())
    need(child_names and all(re.fullmatch(r"shard-[0-9]{2}", n)
                             for n in child_names),
         "unexpected file or directory in compiler shard root")
    count = len(child_names)
    need(1 <= count <= 16 and
         child_names == [f"shard-{i:02}" for i in range(count)],
         "missing, duplicated or out-of-order compiler shard")
    imported = {}
    raw_logs = {}
    total_bytes = 0
    for i in range(count):
        folder = shard_root / f"shard-{i:02}"
        need(folder.is_dir() and not folder.is_symlink(),
             "compiler shard folder missing/unsafe")
        path = folder / "complete_compiler_candidate.json"
        need(path.is_file() and not path.is_symlink(),
             "compiler shard candidate manifest missing")
        data = json.loads(path.read_bytes())
        need(isinstance(data, dict) and
             data.get("format") == "Permansson.AllCaseCompilerCandidate.v1" and
             data.get("status") == "COMPILER_ONLY_UNREVIEWED" and
             data.get("head_sha") == head and
             data.get("case_count") == 45 and
             data.get("claim_count") == 11 and
             data.get("inventory_count") == len(planned) and
             data.get("inventory_sha256") == fingerprint and
             data.get("shard_index") == i and
             data.get("shard_count") == count and
             data.get("independent_review") is False and
             data.get("authentic_ci_job_bound") is False and
             data.get("merged_main_sha") is None,
             "compiler shards disagree on inventory or provenance")
        expected_indices = shard_indices(len(planned), i, count)
        rows = data.get("compiler_axiom_receipts")
        need(isinstance(rows, list) and
             len(rows) == data.get("proof_count") == len(expected_indices),
             "compiler shard omitted required source obligations")
        index_to_row = {}
        for row in rows:
            need(isinstance(row, dict), "malformed compiler shard receipt")
            j = row.get("inventory_index")
            need(type(j) is int and j in expected_indices and
                 j not in index_to_row and j not in imported,
                 "extra/duplicate/wrong-shard compiler proof")
            required = planned[j]
            need(row.get("id") == f"all:{j:04}" and
                 row.get("path") == required["path"] and
                 row.get("declaration") == required["declaration"] and
                 row.get("case_ids") == required["case_ids"] and
                 row.get("claim_ids") == required["claim_ids"] and
                 row.get("head_sha") == head and
                 row.get("compiler_result") == "PASS" and
                 row.get("compiler_check") == "research" and
                 row.get("check_run_id") is None and
                 row.get("declaration_kind") in
                   {"theorem", "definition", "opaque", "axiom", "inductive",
                    "constructor", "recursor", "quotient"},
                 "compiler receipt does not match pinned original theorem")
            src = (ROOT / row["path"]).resolve()
            need(src.is_relative_to(ROOT.resolve()) and src.is_file() and
                 sha(src.read_bytes()) == row.get("source_sha256"),
                 "source bytes differ from compiler proof input")
            name = f"axiom_logs/all_{j:04}.log"
            need(row.get("axiom_log_member") == name and
                 SHA256.fullmatch(str(row.get("axiom_log_sha256"))) is not None,
                 "invented proof log member/digest")
            log_path = folder / name
            need(log_path.is_file() and not log_path.is_symlink() and
                 log_path.resolve().is_relative_to(folder.resolve()),
                 "required true proof log absent")
            blob = log_path.read_bytes()
            total_bytes += len(blob)
            need(0 < len(blob) <= MAX_LOG_BYTES and
                 total_bytes <= MAX_TOTAL_BYTES and
                 sha(blob) == row["axiom_log_sha256"],
                 "log bytes exceed bound or mismatch original attestation")
            log = blob.decode("utf-8", errors="replace")
            need("error:" not in log.lower() and "sorryAx" not in log,
                 "invalid compiler-success diagnostic")
            try:
                actual = compiled_type_record(log, row["declaration"])
                expected_axioms = parse_target_axioms(log, row["declaration"])
            except (TypeEvidenceError, EvidenceError) as exc:
                raise ShardMergeError(
                    "unverifiable compiler theorem type or axioms") from exc
            need(row.get("elaborated_type_sha256") ==
                     elaborated_type_sha256(actual) and
                 row.get("declaration_kind") ==
                     actual["declaration_kind"] and
                 row.get("universe_params_repr") ==
                     actual["universe_params_repr"] and
                 row.get("transitive_axioms") == expected_axioms and
                 set(expected_axioms) <= TRUSTED_AXIOMS,
                 "source theorem elaboration/axioms do not match log")
            index_to_row[j] = row
            imported[j] = row
            raw_logs[name] = blob
        need(set(index_to_row) == set(expected_indices),
             "shard has incomplete original theorem coverage")
        need(set(p.relative_to(folder).as_posix() for p in folder.rglob("*")
                 if p.is_file()) ==
             {"complete_compiler_candidate.json"} |
             {f"axiom_logs/all_{j:04}.log" for j in expected_indices},
             "unexpected/hidden files in source compiler shard")
    need(set(imported) == set(range(len(planned))),
         "union of compiler shards does not cover all exact original owners")
    output.mkdir(parents=True, exist_ok=False)
    (output / "axiom_logs").mkdir()
    for name, raw in sorted(raw_logs.items()):
        (output / name).write_bytes(raw)
    merged = {
        "format": "Permansson.AllCaseCompilerCandidate.v1",
        "status": "COMPILER_ONLY_UNREVIEWED",
        "head_sha": head,
        "proof_count": len(imported),
        "case_count": 45, "claim_count": 11,
        "inventory_sha256": fingerprint, "inventory_count": len(planned),
        "compiler_axiom_receipts": [imported[i] for i in sorted(imported)],
        "merged_shards": count,
        "independent_review": False,
        "authentic_ci_job_bound": False,
        "check_run_id": None,
        "merged_main_sha": None,
    }
    (output / "complete_compiler_candidate.json").write_text(
        json.dumps(merged, sort_keys=True, indent=2)+"\n", encoding="utf-8")
    return merged


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--head", required=True)
    p.add_argument("--shards", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args(argv)
    try:
        summary = merge(args.shards, args.output, head=args.head)
    except (ShardMergeError, OSError, ValueError, KeyError) as exc:
        print("COMPLETE COMPILER SHARD MERGE BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({"status": summary["status"],
                      "source_head": summary["head_sha"],
                      "proof_count": summary["proof_count"],
                      "case_count": summary["case_count"],
                      "claim_count": summary["claim_count"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
