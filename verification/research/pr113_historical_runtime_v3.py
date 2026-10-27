"""Stage-gated original historical T/A2 or inherited M113 evidence adapter.

The original PR113 uses its exact v2 required gate. Descendants rerun that
same reviewed M113 source in an isolated checkout with actual GitHub inputs.
Never convert an inherited infrastructure receipt into current mathematics.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from pr113_boundary_io import detached_destination, strict_json_object
from pr113_lifecycle_source_v3 import actual_source
from pr113_historical_inheritance_v3 import verify as inherited_verify

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.PR113.RequiredHistoricalLifecycleTransport.v3"


class RuntimeError113(ValueError):
    pass


def need(ok, why):
    if not ok:
        raise RuntimeError113(why)


def produce(producer_run_id, security_review_id, *, event=None):
    event = actual_source() if event is None else event
    phase = event["phase"]
    need(phase in ("initial_113_pr", "initial_113_main",
                   "main_descendant_pr", "main_descendant_push"),
         "unknown required historical lifecycle phase")
    if phase.startswith("main_descendant"):
        receipt = inherited_verify(producer_run_id, security_review_id,
                                   lifecycle=event)
        return {"phase": phase, "event": event, "required": receipt,
                "envelope": None, "zips": {}, "transport": None}
    from pr113_historical_artifact_delivery_v2 import (
        deliver, deliver_merged, source_git,
    )
    source_context = {
        "original_base_sha": event["base_sha"] if phase == "initial_113_pr"
                             else event["base_sha"],
        "head_sha": event["head_sha"] if phase == "initial_113_pr"
                    else event["infrastructure_head_sha"],
        "synthetic_sha": event["synthetic_sha"],
    }
    if phase == "initial_113_pr":
        original = deliver(source_context, producer_run_id, security_review_id,
                           git=source_git)
        from pr113_required_dual_gate_v2 import verify
        checked = verify(original["envelope"],
                         original["zips"]["T"], original["zips"]["A2"],
                         git=source_git)
    else:
        from pr113_historical_postmerge_v2 import (
            check_historical_merged,
        )
        merged_context = {
            "original_base_sha": event["base_sha"],
            "reviewed_head_sha": event["infrastructure_head_sha"],
            "merged_main_sha": event["infrastructure_merge_sha"],
        }
        original = deliver_merged(merged_context, producer_run_id,
                                  security_review_id, git=source_git)
        checked = check_historical_merged(
            original["envelope"], original["zips"]["T"],
            original["zips"]["A2"], event_context=merged_context,
            git=source_git)
    need(checked.get("independent_security_review_authenticated") is True,
         "original historical security evidence not independently reviewed")
    return {"phase": phase, "event": event, "required": checked,
            "envelope": original["envelope"],
            "zips": original["zips"], "transport": original["transport"]}


def store(result, output, producer_run_id, security_review_id):
    out = detached_destination(output, ROOT)
    out.mkdir(parents=True, exist_ok=False)
    current = result["event"]
    receipt = {
        "format": FORMAT,
        "phase": result["phase"],
        "source_commit_sha": current["source_commit_sha"],
        "original_github_run_id": current["github_run_id"],
        "original_github_run_attempt": current["github_run_attempt"],
        "historical_producer_run_id": producer_run_id,
        "historical_security_review_id": security_review_id,
        "historical_required_result": result["required"],
        "accepted_current_mathematics": False,
        "owner_merge_authorized": False,
        "publication_authorized": False,
    }
    for item, path in (
        (receipt, "historical_required.json"),
        (result["envelope"], "historical_envelope.json"),
        (result["transport"], "historical_transport_unreviewed.json"),
    ):
        if item is None:
            continue
        with (out / path).open("x", encoding="utf-8") as writer:
            json.dump(item, writer, sort_keys=True, indent=2)
            writer.write("\n")
    for kind, file in (("T", "historical_T.zip"), ("A2", "historical_A2.zip")):
        if kind in result["zips"]:
            with (out / file).open("xb") as writer:
                writer.write(result["zips"][kind])
    return out, receipt


def check_stored(path, producer_run_id, security_review_id, *, event=None,
                 recompute=None):
    """Fail closed on a saved receipt unless authentic evidence rechecks.

    The production CLI never injects the recomputation function. Only
    source-bound unit tests may provide a synthetic recomputation.
    """
    event = actual_source() if event is None else event
    output = detached_destination(path, ROOT, must_exist=True)
    original = strict_json_object(output.read_bytes(), max_bytes=4*1024*1024)
    need(original.get("format") == FORMAT
         and original.get("phase") == event["phase"]
         and original.get("source_commit_sha") == event["source_commit_sha"]
         and original.get("original_github_run_id") == event["github_run_id"]
         and original.get("original_github_run_attempt") == event["github_run_attempt"]
         and original.get("historical_producer_run_id") == producer_run_id
         and original.get("historical_security_review_id") == security_review_id
         and original.get("accepted_current_mathematics") is False
         and original.get("owner_merge_authorized") is False
         and original.get("publication_authorized") is False,
         "retained historical result is not bound to current genuine runner")
    source = original.get("historical_required_result")
    need(isinstance(source, dict), "original required gate result missing")
    if event["phase"].startswith("main_descendant"):
        need(source.get("status") ==
             "PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT"
             and source.get("historical_merged_main_sha") ==
                event["infrastructure_merge_sha"]
             and source.get("current_required_ci_accepted") is False,
             "no actual inherited original historical evidence")
    else:
        need(source.get("independent_security_review_authenticated") is True
             and source.get("head_sha") == event["infrastructure_head_sha"]
                if event["phase"] == "initial_113_main"
                else source.get("independent_security_review_authenticated") is True
                     and source.get("head_sha") == event["head_sha"],
             "original PR113 historical source is not bound")
    if recompute is None:
        recompute = produce
    fresh = recompute(producer_run_id, security_review_id, event=event)
    need(isinstance(fresh, dict)
         and fresh.get("phase") == event["phase"]
         and fresh.get("event") == event
         and fresh.get("required") == source,
         "saved historical receipt differs from live reauthenticated evidence")
    parent = output.parent
    if event["phase"].startswith("initial_113"):
        for key, name in (("envelope", "historical_envelope.json"),
                          ("transport", "historical_transport_unreviewed.json")):
            saved = detached_destination(parent / name, ROOT, must_exist=True)
            need(isinstance(fresh.get(key), dict)
                 and strict_json_object(saved.read_bytes()) == fresh[key],
                 "saved historical envelope or transport differs from original")
        for kind, name in (("T", "historical_T.zip"), ("A2", "historical_A2.zip")):
            saved = detached_destination(parent / name, ROOT, must_exist=True)
            need(fresh.get("zips", {}).get(kind) == saved.read_bytes(),
                 "saved genuine historical GitHub ZIP differs from revalidated bytes")
    else:
        need(fresh.get("envelope") is None and fresh.get("transport") is None
             and fresh.get("zips") == {}
             and not any((parent / name).exists() for name in (
                 "historical_envelope.json", "historical_transport_unreviewed.json",
                 "historical_T.zip", "historical_A2.zip")),
             "descendant evidence cannot borrow original PR113 ZIP files")
    return original


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--producer-run-id", type=int, required=True)
    ap.add_argument("--security-review-id", type=int, required=True)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--check-existing", action="store_true")
    args = ap.parse_args(argv)
    try:
        if args.check_existing:
            receipt = check_stored(args.out, args.producer_run_id,
                                   args.security_review_id)
        else:
            out, receipt = store(
                produce(args.producer_run_id, args.security_review_id),
                args.out, args.producer_run_id, args.security_review_id)
            if receipt["phase"].startswith("initial_113"):
                env = Path(__import__("os").environ.get("GITHUB_ENV", "/dev/null"))
                with env.open("a", encoding="utf-8") as f:
                    for key, path in {
                        "PERMANSSON_DUAL_HISTORICAL_EVIDENCE":
                            "historical_envelope.json",
                        "PERMANSSON_DUAL_ORIGINAL_T_ZIP": "historical_T.zip",
                        "PERMANSSON_DUAL_ORIGINAL_A2_ZIP": "historical_A2.zip",
                    }.items():
                        f.write(key + "=" + str(out / path) + "\n")
        print(json.dumps({"status": receipt["phase"],
                          "source_commit_sha": receipt["source_commit_sha"],
                          "historical_required": True,
                          "new_mathematical_acceptance": False}))
        return 0
    except (RuntimeError113, OSError, KeyError, ValueError, TypeError) as exc:
        print("REQUIRED_HISTORICAL_LIFECYCLE_BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
