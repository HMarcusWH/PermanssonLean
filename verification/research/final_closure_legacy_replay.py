"""Replay a selected legacy false Lean probe against exact original source.

Captured old unittest inputs are not append-only original-source mutations and
MUST NOT be converted by changing their JSON status. This opt-in adapter
reconstructs a *new* append-only Lean negative candidate from one captured
compiler input, verifies the selected original case, and genuinely recompiles
both positive original source and combined false source with pinned Lean.

All outputs are detached, explicitly UNREVIEWED and CI-unattributed. Even
a successful replay has no independently accepted case/claim or scholarly
release status. Missing theorem relevance remains subject to external review.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

from final_closure_mutation_evidence import (
    MutationEvidenceError, committed_file_bytes, git_head, produce, seal_logs,
)
from final_closure_legacy_semantic_evidence import (
    ROOT, original_case_map, selected_methods, test_observations,
)

MAX_FALSE_SOURCE = 16 * 1024
MAX_COMBINED_SOURCE = 4 * 1024 * 1024
SHA40 = re.compile(r"^[a-f0-9]{40}$")
EVENT_ID = re.compile(r"^event-[0-9]+-[0-9]{6}$")
TEST_NAME = re.compile(r"^test_[A-Za-z0-9_]+$")


def need(condition, message):
    if not condition:
        raise MutationEvidenceError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def appended_mutant(original: bytes, captured: bytes, provider_module: str) -> bytes:
    """Strip only leading imports from a standalone Lean falsification probe."""
    need(isinstance(original, bytes) and original
         and isinstance(captured, bytes) and captured, "empty Lean sources")
    need(len(original) <= MAX_COMBINED_SOURCE and
         len(captured) <= MAX_COMBINED_SOURCE + MAX_FALSE_SOURCE,
         "unbounded Lean replay input")
    if captured.startswith(original):
        # Some legacy tests actually compile the complete frozen original
        # provider with a short source-appended false declaration. When that
        # exact immutable prefix is proven byte-for-byte, retain the already
        # source-preserving capture instead of converting it to an import-only
        # synthetic probe.
        suffix = captured[len(original):]
        need(0 < len(suffix) <= MAX_FALSE_SOURCE,
             "missing or oversized appended mathematical false statement")
        try:
            remaining = suffix.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise MutationEvidenceError("non-UTF8 appended Lean source") from exc
        need(re.search(r"(?m)^\s*(?:example|theorem|lemma)\b", remaining),
             "appended original source lacks an explicit mathematical assertion")
        need(not re.search(
                 r"(?m)^\s*(?:import|axiom|opaque|constant|set_option)\b",
                 remaining) and
             not re.search(r"(?i)\b(?:sorry|sorryAx|admit)\b", remaining),
             "appended original source changes imports, axioms or admissions")
        return captured
    need(len(captured) <= MAX_FALSE_SOURCE,
         "unbounded standalone Lean replay input")
    try:
        text = captured.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise MutationEvidenceError("non-UTF8 captured Lean input") from exc
    lines = text.splitlines(keepends=True)
    imports = []
    body = []
    seen_statement = False
    for line in lines:
        trimmed = line.strip()
        if trimmed.startswith("import "):
            need(not seen_statement, "legacy false source has a late import")
            imports.append(trimmed)
        else:
            body.append(line)
            if trimmed and not trimmed.startswith("--"):
                seen_statement = True
    need("import " + provider_module in imports,
         "legacy false source did not import the selected original provider")
    remaining = "".join(body).strip()
    need(remaining and re.search(r"(?m)^\s*(?:example|theorem|lemma)\b",
                                 remaining),
         "captured Lean probe has no explicit false mathematical statement")
    need(not re.search(r"(?m)^\s*(?:import|axiom|opaque|constant|set_option)\b",
                       remaining) and
         not re.search(r"(?i)\b(?:sorry|sorryAx|admit)\b", remaining),
         "captured false source introduces imports, admissions or axioms")
    suffix = ("\n/- PR113 ORIGINAL LEGACY REPLAY: CANDIDATE ONLY -/\n"
              + remaining + "\n").encode("utf-8")
    need(len(original) + len(suffix) <= MAX_COMBINED_SOURCE,
         "replayed Lean source exceeds source limit")
    return original + suffix


def choose_original(head: str, row: dict, provider: str):
    rel = Path(provider)
    need(not rel.is_absolute() and ".." not in rel.parts and
         rel.suffix == ".lean" and
         rel.as_posix().startswith("PermanssonResearch/"),
         "invalid provider path")
    required = {
        item.get("path") for item in
        row.get("historical_proof_declarations", [])
        if isinstance(item, dict)
    } | {
        item.get("path") for item in
        row.get("new_claim_source_candidates", [])
        if isinstance(item, dict)
    }
    need(provider in required,
         "selected original provider is not in the frozen case theorem map")
    source = ROOT / rel
    raw = committed_file_bytes(head, source, root=ROOT)
    return source, raw, ".".join(rel.with_suffix("").parts)


def replay(head: str, *, case_id: str, method: str, provider: str,
           test_output: Path, observation_id: str, output: Path):
    need(SHA40.fullmatch(head) is not None and git_head() == head,
         "source head not frozen")
    need(TEST_NAME.fullmatch(method) is not None and
         EVENT_ID.fullmatch(observation_id) is not None,
         "malformed named case or compiler event identity")
    byid, legacy_ids = original_case_map(head)
    need(case_id in legacy_ids, "case is not in twenty original legacy candidates")
    row = byid[case_id]
    if test_output.is_symlink() or output.is_symlink():
        raise MutationEvidenceError("symlinked evidence roots are not allowed")
    test_output = test_output.resolve()
    output = output.resolve()
    root = ROOT.resolve()
    need(test_output.is_dir() and not test_output.is_symlink() and
         not test_output.is_relative_to(root) and
         not output.exists() and
         not output.is_relative_to(root) and
         not root.is_relative_to(output) and
         not test_output.is_relative_to(output) and
         not output.is_relative_to(test_output),
         "detached legacy input/output roots invalid or overlapping")
    test_report = test_output / "unreviewed_test_manifest.json"
    need(test_report.is_file() and not test_report.is_symlink(),
         "selected legacy test report missing")
    manifest = json.loads(test_report.read_bytes())
    need(manifest.get("case_id") == case_id and
         manifest.get("format") == "Permansson.LegacyCaseTestExecutionCandidate.v1"
         and manifest.get("independent_review") is False
         and manifest.get("ci_check_run_id") is None
         and manifest.get("release_approved") is False and
         manifest.get("test_exit_code") == 0 and
         manifest.get("status") == "EXECUTED_UNREVIEWED_NOT_AUTHENTICATED",
         "legacy test did not pass as a non-approved candidate")
    relative_test = manifest.get("test_file")
    names = manifest.get("selected_methods")
    need(isinstance(relative_test, str) and
         isinstance(names, list) and method in names and
         names == sorted(set(names)), "selected test method manifest invalid")
    registered = selected_methods(head, row)
    need(any(rel == relative_test and method in method_names
             for rel, _cls, method_names in registered),
         "legacy method not registered against original case")
    test_file = ROOT / relative_test
    original_test = committed_file_bytes(head, test_file, root=ROOT)
    need(manifest.get("source_test_sha256") == sha(original_test),
         "legacy selected test source does not match frozen Git")
    for name, digest_field in (("test_stdout.log", "stdout_sha256"),
                               ("test_stderr.log", "stderr_sha256")):
        file = test_output / name
        need(file.is_file() and not file.is_symlink() and
             sha(file.read_bytes()) == manifest.get(digest_field),
             "legacy Python execution log is not retained")
    raw_root = test_output / "raw_compiler"
    need(raw_root.is_dir() and not raw_root.is_symlink(),
         "raw original compiler observation root unavailable")
    observations = test_observations(raw_root, expected_case=case_id,
                                     expected_methods=",".join(names))
    observed = [obs for obs in observations
                if obs["observation_id"] == observation_id and
                obs.get("method_observed_unverified") == method]
    need(len(observed) == 1 and
         observed[0]["possible_semantic_diagnostic"] is True and
         observed[0]["method_attribution_ambiguous"] is False,
         "selected named method has no retained semantic false diagnostic")
    event = raw_root / observation_id
    need(event.is_dir() and not event.is_symlink() and
         (event / "source.lean").is_file() and
         not (event / "source.lean").is_symlink(),
         "original false Lean input not retained")
    false_raw = (event / "source.lean").read_bytes()
    need(sha(false_raw) == observed[0]["source_sha256"],
         "captured false source differs from compiler observation")
    true_source, original, module = choose_original(head, row, provider)
    mutated = appended_mutant(original, false_raw, module)
    output.mkdir(parents=True, exist_ok=False)
    # Bind the captured candidate inputs both before and after Lean work.
    frozen_test_report = test_report.read_bytes()
    frozen_observation = (event / "observation.json").read_bytes()
    with tempfile.TemporaryDirectory(prefix="pr113-replay-", dir=output) as td:
        replay_file = Path(td) / "OriginalAppendedFalse.lean"
        replay_file.write_bytes(mutated)
        logs = output / "source_logs"
        receipt = produce(
            head, true_source=true_source, mutant=replay_file,
            test_path=test_file, test_name=method,
            case_id=case_id, claim_ids=[], out=logs)
    if (test_report.read_bytes() != frozen_test_report or
            (event / "observation.json").read_bytes() != frozen_observation or
            (event / "source.lean").read_bytes() != false_raw):
        raise MutationEvidenceError("legacy captured input changed during replay")
    zip_path = output / "semantic_replay_candidate.zip"
    bundle_sha = seal_logs(logs, zip_path)
    raw_capture = output / "original_legacy_capture"
    raw_capture.mkdir()
    for name in ("observation.json", "source.lean",
                 "stdout.log", "stderr.log"):
        inp = event / name
        if inp.is_file() and not inp.is_symlink():
            shutil.copyfile(inp, raw_capture / name)
    replay_record = {
        "format": "Permansson.LegacyAppendOnlyReplayCandidate.v1",
        "status": "REPLAYED_APPEND_ONLY_UNREVIEWED_UNATTRIBUTED",
        "head_sha": head, "case_id": case_id,
        "selected_test_path": relative_test,
        "selected_method": method,
        "original_provider_path": provider,
        "original_observation_id": observation_id,
        "legacy_test_manifest_sha256": sha(test_report.read_bytes()),
        "raw_observation_sha256": observed[0]["raw_metadata_sha256"],
        "captured_false_source_sha256": sha(false_raw),
        "replayed_false_source_sha256": sha(mutated),
        "detached_bundle_sha256": bundle_sha,
        "mutation_record": receipt,
        "ci_check_run_id": None,
        "independent_review": False,
        "mathematical_acceptance": False,
        "scientific_release_approved": False,
    }
    (output / "unreviewed_replay.json").write_text(
        json.dumps(replay_record, sort_keys=True, indent=2) + "\n",
        encoding="utf-8")
    return replay_record


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--head", required=True)
    parser.add_argument("--case-id", required=True)
    parser.add_argument("--method", required=True)
    parser.add_argument("--original-provider", required=True)
    parser.add_argument("--test-output", required=True, type=Path)
    parser.add_argument("--observation-id", required=True)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        record = replay(args.head, case_id=args.case_id,
                        method=args.method, provider=args.original_provider,
                        test_output=args.test_output,
                        observation_id=args.observation_id,
                        output=args.out)
    except (MutationEvidenceError, OSError, ValueError, KeyError) as exc:
        print("LEGACY APPEND-ONLY REPLAY BLOCKED:", exc, file=sys.stderr)
        return 2
    print(json.dumps({k: record[k] for k in (
        "status", "head_sha", "case_id", "detached_bundle_sha256")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
