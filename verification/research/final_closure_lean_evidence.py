"""Actual pinned-Lean theorem evidence exporter; NEVER auto-accepts claims.

Run from a clean checkout of ONE chosen frozen branch head H. The output is
external to the repository and contains compiler proofs and literal source
hashes, but no independent review IDs or fabricated final main SHA.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from final_closure_case_receipts import statement_header, parse_target_axioms, EvidenceError
from closure_elaborated_type import (
    lean_probe, compiled_type_record, elaborated_type_sha256, TypeEvidenceError,
)

ROOT = Path(__file__).resolve().parents[2]
MAP = ROOT / "research/paper_closures/post_merge_112/claim_declaration_map.json"
DECL_RE = re.compile(r"^[A-Za-z0-9_'.]+$")
SHA40 = re.compile(r"^[0-9a-f]{40}$")
CLAIM_IDS = ("Q1", "Q2", "Q3", "M1", "M2", "M3",
             "N1", "N2", "N3", "D8", "D9")
BAD = ("error:", "sorryax", "unknown identifier", "unknown module",
       "maximum number of heartbeats", "timeout", "failed to import")
AXIOM_LIST = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")


class CompilerEvidenceError(RuntimeError):
    pass


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def git_head() -> str:
    result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                            text=True, capture_output=True, timeout=30)
    if result.returncode:
        raise CompilerEvidenceError("genuine local Git head unavailable")
    return result.stdout.strip()


def run_probe(path: Path):
    if not shutil.which("lake"):
        raise CompilerEvidenceError("pinned Lean/Lake unavailable")
    try:
        return subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                              text=True, capture_output=True, timeout=900)
    except subprocess.TimeoutExpired as exc:
        raise CompilerEvidenceError("compiler heartbeat/process timeout") from exc


def parse_axioms(log: str, declaration: str) -> list[str]:
    """Validate an isolated one-declaration Lean probe, never a mixed log.

    The detached receipt parser may locate an exact target among unrelated
    diagnostics, but the *producing* compiler probe must contain precisely one
    axiom statement overall. This also prevents a valid target record hiding
    a second, off-target axiom record.
    """
    if any(word in log.lower() for word in BAD):
        raise CompilerEvidenceError("failed or untrusted compiler output: " + declaration)
    if declaration not in log:
        raise CompilerEvidenceError("wrong compiled Lean declaration: " + declaration)
    records = re.findall(
        r"\\bdepends on axioms:\\s*\\[|\\bdoes not depend on any axioms\\b",
        log)
    if len(records) != 1:
        raise CompilerEvidenceError(
            "isolated compiler probe must emit exactly one axiom record: " +
            declaration)
    try:
        return parse_target_axioms(log, declaration)
    except EvidenceError as exc:
        raise CompilerEvidenceError(str(exc)) from exc


def candidate_records(head: str, out: Path) -> dict:
    if not SHA40.fullmatch(head) or head != git_head():
        raise CompilerEvidenceError("checkout HEAD differs from frozen source head")
    if out.resolve().is_relative_to(ROOT.resolve()):
        raise CompilerEvidenceError("evidence output must be detached from Git checkout")
    if not MAP.is_file():
        raise CompilerEvidenceError("qualified source map missing")
    source_map = json.loads(MAP.read_text())
    claim_rows = source_map.get("claims")
    if (source_map.get("count") != len(CLAIM_IDS) or
        not isinstance(claim_rows, list) or
        len(claim_rows) != len(CLAIM_IDS) or
        [c.get("claim_id") for c in claim_rows if isinstance(c, dict)]
            != list(CLAIM_IDS)):
        raise CompilerEvidenceError("exact eleven claim identities/rows missing")
    declaration_owners = set()
    for claim in claim_rows:
        rows = claim.get("declarations")
        if (not isinstance(rows, list) or not rows or
            not isinstance(claim.get("original_case_links"), list) or
            not claim["original_case_links"] or
            not isinstance(claim.get("test_source_candidates"), list) or
            not claim["test_source_candidates"]):
            raise CompilerEvidenceError("claim lacks declarations/case/test obligations")
        for row in rows:
            if not isinstance(row, dict):
                raise CompilerEvidenceError("invalid declaration owner entry")
            pair = (row.get("path"), row.get("declaration"))
            if pair in declaration_owners:
                raise CompilerEvidenceError("duplicated primary claim declaration owner")
            declaration_owners.add(pair)
        for test in claim["test_source_candidates"]:
            if (not isinstance(test, str) or
                not test.startswith("verification/research/test_") or
                not test.endswith(".py") or
                not (ROOT / test).is_file()):
                raise CompilerEvidenceError("claim test candidate is not current source")
    log_dir = out / "axiom_logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    outputs = []
    for claim in source_map["claims"]:
        for idx, row in enumerate(claim["declarations"]):
            src = ROOT / row["path"]
            if not src.is_file() or not src.resolve().is_relative_to(ROOT.resolve()):
                raise CompilerEvidenceError("missing actual theorem source")
            declaration = row["declaration"]
            if not DECL_RE.fullmatch(declaration) or "." not in declaration:
                raise CompilerEvidenceError("unqualified theorem")
            source = src.read_text(encoding="utf-8")
            header = statement_header(source, declaration)
            module = row["path"].removesuffix(".lean").replace("/", ".")
            code = lean_probe(module, declaration)
            # Compile from a temporary source under the configured Lean path.
            with tempfile.TemporaryDirectory(
                    prefix="closure-proof-", dir=ROOT / ".lake") as temp:
                probe = Path(temp) / "Proof.lean"
                probe.write_text(code, encoding="utf-8")
                result = run_probe(probe)
            log = (result.stdout + "\n" + result.stderr).encode("utf-8")
            if result.returncode != 0:
                raise CompilerEvidenceError(
                    "Lean #check/#print axioms failed: " + declaration +
                    "\n" + log.decode("utf-8", "replace")[-700:])
            axioms = parse_axioms(log.decode("utf-8"), declaration)
            try:
                compiled = compiled_type_record(log.decode("utf-8"), declaration)
            except TypeEvidenceError as exc:
                raise CompilerEvidenceError(str(exc)) from exc
            member = f"axiom_logs/{claim['claim_id']}_{idx}.log"
            (out / member).write_bytes(log)
            outputs.append({
                "id": f"{claim['claim_id']}:{idx}", "claim_ids": [claim["claim_id"]],
                "case_ids": claim["original_case_links"],
                "head_sha": head, "path": row["path"],
                "declaration": declaration,
                "source_sha256": sha256(src.read_bytes()),
                # Display-only lexical excerpt; NEVER authoritative theorem type.
                "statement_sha256": sha256(header.encode("utf-8")),
                "elaborated_type_sha256": elaborated_type_sha256(compiled),
                "declaration_kind": compiled["declaration_kind"],
                "universe_params_repr": compiled["universe_params_repr"],
                "transitive_axioms": axioms,
                "axiom_log_member": member,
                "axiom_log_sha256": sha256(log),
                "compiler_check": "research",
                "compiler_result": "PASS",
                "check_run_id": None,
                "CI_binding": "PENDING_REAL_CHECK_RUN_ID_ON_FROZEN_H",
                "independent_review": "NOT_RECEIVED",
            })
    report = {
        "format": "Permansson.LeanCompilerCandidateEvidence.v1",
        "head_sha": head,
        "claim_count": 11,
        "proof_count": len(outputs),
        "status": "COMPILER_ONLY_UNREVIEWED",
        "compiler_axiom_receipts": outputs,
        "semantic_negative_receipts": [],
        "reviews": [],
        "limitations": [
            "Compiler success does not imply criterion or hypothesis sufficiency",
            "Check-run ID, signed negative mutant and reviewer scope not yet bound",
            "No empirical GR/PR, unrestricted randomized optimum, or final M inferred",
        ],
    }
    out.mkdir(parents=True, exist_ok=True)
    (out / "compiler_candidate.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    return report


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True)
    ap.add_argument("--output", type=Path, required=True)
    opt = ap.parse_args(argv)
    try:
        result = candidate_records(opt.head, opt.output)
    except (CompilerEvidenceError, OSError, ValueError) as exc:
        print("COMPILER EVIDENCE BLOCKED:", exc)
        return 2
    print(json.dumps({"head_sha": result["head_sha"],
                      "proofs": result["proof_count"],
                      "status": result["status"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
