"""Join this maintenance release's actual main-push evidence to its frozen PR ledger.

External receipt tooling only: no acquisition, Git writes, source changes,
publication, merge or administrative rollout. No output before all joins pass.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import zipfile

ARTIFACTS = Path(__file__).resolve().parent
H = "92e45179a5e3ecbe1b2bcadc4da54a0d1657f501"
B = "37c0cb8f2fbe7934639127e5f8b6d64a01e6950f"
S = "d5f2d3a72bda670859c5da87bb173f9eb96696ee"
T = "71cc34fa0bc4b639c05d2ec5f39f0b88afd56388"
TREE = "d1c01b2812a13b672f164841a7cc4a8ab7dcc778"
M = "39279799834ae536bda715dedecdc11a32bf6c82"
PREMERGE = "maintenance-acceptance-ledger-finalized-premerge-verified.json"
PREMERGE_SHA256 = "5958d8c155086bbf3ccbca1dc6c651fe0b88ffa6bba729facce4dcaf4e632524"
POST_DIRECTORY = "hardening-pr77-finalized-main-push"
PACKET_HELPER_SHA256 = "1da37f4aa9859a14974b452c55717d74493e5d1e9941ebf9a28ba0eb4cf40c21"
ADAPTER = "hardening-pr77/verify_main_capture.py"
ADAPTER_SHA256 = "d901d59f376dc0140518a4b755498e3a7180391fa5f8a66cd676aeb63c312fbb"
TECHNICAL_STAGES = {"F1.code_verified", "F2.code_verified", "F3.bundle_materialized",
                    "F3.offline_restore_verified", "F3.original_evidence_captured"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def safe_path(path, *, exists=True):
    path = Path(path).absolute()
    require(not any(p.is_symlink() or (hasattr(p, "is_junction") and p.is_junction())
                    for p in (path, *path.parents)), "Receipt path cannot traverse a link/junction")
    path = path.resolve()
    require(path.is_relative_to(ARTIFACTS), "Receipt inputs/output must stay in the explicit artifacts directory")
    if exists:
        require(path.is_file(), "Missing receipt input: " + str(path))
    return path


def reviewed_packet_helper():
    path = safe_path(ARTIFACTS / "build_maintenance_receipt_packet.py")
    require(sha(path.read_bytes()) == PACKET_HELPER_SHA256, "Reviewed packet helper changed")
    spec = importlib.util.spec_from_file_location("reviewed_main_packet_helper", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_premerge(ledger):
    context = ledger["maintenance_context"]
    require(all(context[k] == v for k, v in {"repository": "HMarcusWH/PermanssonLean", "pr_number": 77,
            "head_H": H, "base_B": B, "synthetic_S": S, "synthetic_tree": TREE,
            "main_merge_M": None, "main_tree": None}.items()), "Premerge source is not the fixed accepted PR tuple")
    require(ledger["registry_source"]["commit"] == T and len(ledger["cases"]) == 108
            and Counter(c["status"] for c in ledger["cases"]) == {"PASS": 96, "DEFERRED_BY_USER": 12},
            "Premerge conjunction must remain96 technical passes and12 deferred OPS")
    require(sum(c["level"] == "unit" for c in ledger["cases"]) == 87, "Expected87 original unit cases")
    for case in ledger["cases"]:
        if case["level"] == "authorized_rollout":
            require(case["status"] == "DEFERRED_BY_USER" and case["actual_result"] is None
                    and case["evidence"] == [], "OPS cannot be promoted")
    require(all(v == ("PASS" if k in TECHNICAL_STAGES else "DEFERRED_BY_USER")
                for k, v in ledger["stage_states"].items()), "Technical/enforcement stage states differ")
    require(set(TECHNICAL_STAGES).issubset(ledger["stage_states"]), "Missing technical stage")
    require(ledger["completion_policy"]["all108_complete"] is False
            and ledger["completion_policy"]["all96_technical_complete"] is True
            and ledger["completion_policy"]["overall_F3_closed"] is False, "F3/OPS closure cannot be inferred")
    science = ledger["scientific_exclusions"]
    require(science["new_or_changed_theorem_declarations"] == science["new_mathematical_assumptions"] == 0
            and science["scientific_promotion"] is False, "Mathematical scope cannot be promoted")
    require(ledger["premerge_acceptance"]["main_merge_M"] is None
            and ledger["additional_acceptance_conditions"][0]["status"] == "PASS"
            and ledger["additional_acceptance_conditions"][0]["checked_sha"] == S, "Original PR/K4 acceptance changed")


def git_read(repo, *args):
    environment = {k: v for k, v in os.environ.items() if not k.upper().startswith("GIT_")}
    environment.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_CONFIG_NOSYSTEM="1",
                       GIT_CONFIG_GLOBAL=os.devnull, GIT_TERMINAL_PROMPT="0", GIT_OPTIONAL_LOCKS="0")
    result = subprocess.run(["git", "--no-replace-objects", "-c", "core.fsmonitor=false", "-C", str(repo), *args],
                            env=environment, capture_output=True, timeout=60)
    require(result.returncode == 0 and len(result.stdout) <= 8 * 1024 * 1024, "Required canonical Git read failed")
    return result.stdout


def replay_adapter(module, selected, index, summary):
    """Recheck raw API/ZIP data in scratch; do not mutate the frozen capture."""
    adapter = safe_path(ARTIFACTS / ADAPTER)
    raw_adapter = adapter.read_bytes()
    require(sha(raw_adapter) == ADAPTER_SHA256, "Reviewed main-capture adapter changed")
    scratch = safe_path(ARTIFACTS / "hardening-temp", exists=False)
    require(scratch.is_dir(), "Existing external scratch directory is required")
    with tempfile.TemporaryDirectory(prefix="permansson-main-receipt-", dir=scratch) as temporary:
        directory = Path(temporary)
        for name, payload in selected.items():
            relative = PurePosixPath(name).relative_to(POST_DIRECTORY).as_posix()
            require("/" not in relative, "Postmerge capture must be flat and explicitly indexed")
            (directory / relative).write_bytes(payload)
        result = subprocess.run([sys.executable, "-I", "-S", "-B", str(adapter), "--main", M,
                                 "--directory", str(directory)], cwd=directory,
                                capture_output=True, timeout=120)
        require(result.returncode == 0, "Reviewed main adapter rejected raw captured evidence: "
                + result.stderr.decode("utf-8", "replace")[:2000])
        reproduced = module.load((directory / "verification-summary.json").read_bytes())
        def without_time(value):
            value = deepcopy(value)
            require(isinstance(value.pop("executed_at", None), str), "Main summary lacks its execution timestamp")
            return value
        require(without_time(reproduced) == without_time(summary), "Reproduced main summary differs beyond execution time")
        for name in ("legacy-context-artifacts.json", "legacy-context-verification.json"):
            require(module.load((directory / name).read_bytes()) == module.load(selected[POST_DIRECTORY + "/" + name]),
                    "Reproduced legacy source-context record differs")
    require(adapter.read_bytes() == raw_adapter, "Reviewed main adapter changed during verification")
    return {"adapter_path": ADAPTER, "adapter_sha256": ADAPTER_SHA256,
            "isolated_standard_library_parser_replay": "PASS", "summary_equal_except_execution_time": True,
            "capture_mutated": False, "local_Lean_rerun": False, "network_isolation_claim": False}


def complete(args):
    require(args.main == M and re.fullmatch(r"[0-9a-f]{40}", args.main) is not None, "Explicit actual maintenance M is required")
    module = reviewed_packet_helper()
    premerge_path = safe_path(args.premerge_ledger)
    raw = premerge_path.read_bytes()
    require(premerge_path.name == PREMERGE and sha(raw) == PREMERGE_SHA256, "Frozen premerge ledger bytes differ")
    original = module.load(raw)
    validate_premerge(original)
    index = module.relative(args.postmerge_index)
    require(PurePosixPath(index).parent.as_posix() == POST_DIRECTORY
            and PurePosixPath(index).name in {"capture-inventory.json", "capture-files.json"}, "Explicit sibling main-push index is required")
    selected = module.indexed_inputs(ARTIFACTS, index, postmerge=True)
    require(sum(map(len, selected.values())) <= module.MAX_TOTAL, "Postmerge capture exceeds fixed receipt budget")
    for name, payload in selected.items():
        module.screen_payload(payload, name)
    summary = module.load(selected[POST_DIRECTORY + "/verification-summary.json"])
    require(summary["format"] == "Permansson.Hardening.MainPushArtifactVerification.v1", "Actual main-capture summary format required")
    module.verify_postmerge_capture(selected, POST_DIRECTORY, H, B, S, TREE, M)
    repo = Path(args.repo).resolve()
    canonical = module.commit_identity(repo, M)
    require(canonical["parents"] == [B, H] and canonical["tree"] == TREE
            and module.commit_identity(repo, S)["tree"] == TREE, "Canonical M does not match accepted S")
    git_read(repo, "merge-base", "--is-ancestor", T, M)
    require(git_read(repo, "rev-parse", "refs/remotes/origin/main").decode().strip() == M, "Current fetched origin/main is not this M")
    replay = replay_adapter(module, selected, index, summary)
    require(all(module.read(ARTIFACTS, name) == payload for name, payload in selected.items())
            and premerge_path.read_bytes() == raw, "Frozen input changed during joining")
    def evidence(relative):
        payload = module.read(ARTIFACTS, relative)
        return {"path": relative, "original_artifact_path": relative, "sha256": sha(payload), "bytes": len(payload)}
    runs = module.api_payload(module.load(selected[POST_DIRECTORY + "/main-runs.json"]))["workflow_runs"]
    ledger = deepcopy(original)
    ledger["maintenance_context"].update(main_merge_M=M, main_tree=TREE,
        main_push_workflow_runs=[{"run_id": r["id"], "run_attempt": r["run_attempt"], "event": "push",
                                  "head_sha": M, "conclusion": "success"} for r in sorted(runs, key=lambda r: r["id"])])
    ledger["receipt_assembly"]["merge_acceptance"] = "MAIN_PUSH_VERIFIED; ORIGINAL_PR_ACCEPTANCE_RETAINED"
    ledger["postmerge_acceptance"] = {"format": "Permansson.Hardening.PostmergeAcceptance.v1",
        "status": "MAIN_PUSH_VERIFIED_TECHNICAL_PASS_OPS_DEFERRED", "assembled_at_utc": datetime.now(timezone.utc).isoformat(),
        "source": {**summary["source"], "tooling_T": T, "repository": "HMarcusWH/PermanssonLean", "pr_number": 77},
        "frozen_premerge_ledger": evidence(PREMERGE), "main_capture_index": evidence(index),
        "main_verification_summary": evidence(POST_DIRECTORY + "/verification-summary.json"),
        "main_commit_API": evidence(POST_DIRECTORY + "/main-commit.json"), "verification_parser_replay": replay,
        "actual_check_contexts": 9, "actual_push_workflows": 6, "publisher_ZIPs": 10,
        "Linux_unit_methods": 112, "Windows_portability_methods": 63,
        "actual_main_Research_Lean_check": "success", "PR_only_C10_main": summary["c10_main"],
        "all108_case_records_preserved": True, "original_PR_workflow_runs_preserved": True,
        "scope_limits": ["Original PR case checked_sha/evidence and premerge acceptance remain unchanged at their actual S/H.",
                         "Main-push execution is a separate actual M record, not transferred PR C10 evidence.",
                         "No mathematical promotion, counted GitHub APPROVED review, publisher authentication or OPS completion."]}
    require(ledger["cases"] == original["cases"] and ledger["premerge_acceptance"] == original["premerge_acceptance"]
            and ledger["maintenance_context"]["workflow_runs"] == original["maintenance_context"]["workflow_runs"]
            and ledger["stage_states"] == original["stage_states"]
            and ledger["completion_policy"] == original["completion_policy"]
            and ledger["scientific_exclusions"] == original["scientific_exclusions"], "Original evidence or scope was changed")
    return ledger


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("premerge-ledger", "postmerge-index", "repo", "main", "output"):
        parser.add_argument("--" + name, required=True)
    args = parser.parse_args(argv)
    try:
        output = safe_path(args.output, exists=False)
        require(not output.exists(), "Refuse to overwrite an existing receipt")
        result = complete(args)
        payload = (json.dumps(result, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False) + "\n").encode()
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("xb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        print(json.dumps({"status": result["postmerge_acceptance"]["status"], "main": M,
                          "sha256": sha(payload), "technical_PASS": 96, "OPS_deferred": 12}))
        return 0
    except (ValueError, OSError, KeyError, TypeError, zipfile.BadZipFile, subprocess.SubprocessError) as error:
        print("Main acceptance blocked: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
