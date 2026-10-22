"""Stamp genuine GitHub execution metadata on compiler *candidate* outputs.

Runs inside the dedicated CI proof-evidence job, AFTER actual Lean execution.
This is provenance for a future externally checked GitHub artifact, not itself
a GitHub check-run ID, approval, authenticated evidence bundle, or release.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA64 = re.compile(r"^[0-9a-f]{64}$")
MAX_LOG_BYTES = 4 * 1024 * 1024


class StampingError(ValueError):
    pass


def need(ok, msg):
    if not ok:
        raise StampingError(msg)


def source_git(*args):
    try:
        return subprocess.check_output(["git", *args], cwd=ROOT, text=True,
                                       stderr=subprocess.DEVNULL, timeout=25).strip()
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise StampingError("genuine local Git identity unavailable") from exc


def attestation(folder: Path, *, head: str, env: dict) -> dict:
    need(SHA40.fullmatch(head) is not None, "invalid expected source H")
    need(source_git("rev-parse", "HEAD") == head, "CI did not execute frozen source H")
    tree = source_git("rev-parse", "HEAD^{tree}")
    need(SHA40.fullmatch(tree) is not None, "invalid source tree identity")
    need(env.get("GITHUB_ACTIONS") == "true" and
         env.get("GITHUB_REPOSITORY") == "HMarcusWH/PermanssonLean" and
         env.get("GITHUB_EVENT_NAME") in {"workflow_dispatch", "pull_request"} and
         env.get("GITHUB_SHA") == head,
         "untrusted runner/repository/event/source identity")
    rid = env.get("GITHUB_RUN_ID", "")
    attempt = env.get("GITHUB_RUN_ATTEMPT", "")
    need(re.fullmatch(r"[1-9][0-9]*", rid) is not None and
         re.fullmatch(r"[1-9][0-9]*", attempt) is not None and
         env.get("GITHUB_JOB") == "compiler-candidate" and
         env.get("GITHUB_WORKFLOW") == "PR113 Compiler Evidence Candidate",
         "missing genuine CI run/attempt/job/workflow binding")
    folder = Path(folder).resolve()
    need(not folder.is_relative_to(ROOT.resolve()) and folder.is_dir(),
         "candidate log directory must be detached from source")
    data = json.loads((folder / "compiler_candidate.json").read_bytes())
    rows = data.get("compiler_axiom_receipts")
    need(data.get("status") == "COMPILER_ONLY_UNREVIEWED" and
         data.get("head_sha") == head and
         data.get("claim_count") == 11 and
         isinstance(rows, list) and bool(rows) and
         len(rows) == data.get("proof_count"),
         "compiled candidate claims are missing or fabricated")
    ids = set()
    evidence_files = {}
    for item in rows:
        need(isinstance(item, dict), "invalid theorem record")
        rid_ = item.get("id")
        name = item.get("axiom_log_member")
        expected_hash = item.get("axiom_log_sha256")
        need(isinstance(rid_, str) and rid_ and rid_ not in ids and
             isinstance(name, str) and name and
             SHA64.fullmatch(str(expected_hash)) is not None,
             "duplicate/missing proof log identity")
        ids.add(rid_)
        rel = PurePosixPath(name)
        need(not rel.is_absolute() and ".." not in rel.parts and
             "\\" not in name and rel.as_posix() == name and
             name.startswith("axiom_logs/"),
             "unsafe proof artifact member path")
        log_path = (folder / name).resolve()
        need(log_path.is_relative_to(folder) and log_path.is_file() and
             not (folder / name).is_symlink() and
             log_path.stat().st_size <= MAX_LOG_BYTES,
             "unretained/oversized proof artifact log")
        raw = log_path.read_bytes()
        sha = hashlib.sha256(raw).hexdigest()
        need(sha == expected_hash, "compiled theorem log digest mismatch")
        evidence_files[name] = sha
        need(item.get("head_sha") == head and
             item.get("check_run_id") is None and
             item.get("compiler_result") == "PASS" and
             item.get("CI_binding") == "PENDING_REAL_CHECK_RUN_ID_ON_FROZEN_H",
             "candidate must never inherit unrelated or future CI ID")
    require_owners = {"Q1", "Q2", "Q3", "M1", "M2", "M3",
                      "N1", "N2", "N3", "D8", "D9"}
    owned = [c for item in rows for c in item.get("claim_ids", [])]
    need(set(owned) == require_owners, "missing required eleven claim owners")
    main = folder / "compiler_candidate.json"
    result = {
        "format": "Permansson.CIExecutedCompilerCandidate.v1",
        "status": "EXECUTED_UNREVIEWED_NO_CHECKRUN_CLAIM",
        "source_head": head, "source_tree": tree,
        "github_repository": env["GITHUB_REPOSITORY"],
        "github_workflow": env["GITHUB_WORKFLOW"],
        "github_job": env["GITHUB_JOB"],
        "github_run_id": int(rid),
        "github_run_attempt": int(attempt),
        "github_event_name": env["GITHUB_EVENT_NAME"],
        "compiler_candidate_sha256": hashlib.sha256(main.read_bytes()).hexdigest(),
        "compiler_evidence": dict(sorted(evidence_files.items())),
        "proof_count": len(rows), "claim_count": len(require_owners),
        "check_run_id": None,
        "independent_review": False,
        "merged_main_sha": None,
        "full_mathematical_acceptance": False,
    }
    return result


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True)
    ap.add_argument("--evidence-dir", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    a = ap.parse_args(argv)
    try:
        payload = attestation(a.evidence_dir, head=a.head, env=os.environ)
        out = a.out.resolve()
        need(out.parent == a.evidence_dir.resolve() and
             not out.exists(), "stamp must be new and inside detached artifact")
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    except (StampingError, ValueError, OSError, KeyError) as exc:
        print("CI EVIDENCE STAMP BLOCKED:", exc)
        return 2
    print(json.dumps({"head": payload["source_head"],
                      "proofs": payload["proof_count"],
                      "status": payload["status"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
