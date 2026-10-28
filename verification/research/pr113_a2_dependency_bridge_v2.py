"""Corrected-baseline dependency bridge, distinct from immutable legacy v1.

Only exact pinned dependency packages may be shared. Current project proof
builds, receipt relabeling, TLS exceptions and source edits are never allowed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

import pr113_historical_a2_baseline_v1 as baseline

FORMAT = "Permansson.PR113.HistoricalA2DependencyBridge.v2"
STATUS = "PINNED_DEPENDENCIES_REUSED_WITHOUT_PROOF_BUILD_IMPORT"
MATHLIB_REV = "5ed2965256430c3649e86755f9576b54eca72435"
FIELDS = frozenset((
    "format", "status", "historical_head", "historical_tree_sha",
    "historical_introducer", "current_head", "manifest_sha256", "pinned_packages",
    "original_verifier_modified", "historical_project_proofs_reused",
    "independent_security_review", "mathematical_acceptance",
))


class DependencyBridgeError(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise DependencyBridgeError(message)


def strict_object(raw):
    need(type(raw) is bytes and 0 < len(raw) <= 1024 * 1024,
         "missing or unbounded dependency JSON bytes")
    def unique(pairs):
        result = {}
        for key, value in pairs:
            need(key not in result, "duplicate dependency JSON key")
            result[key] = value
        return result
    def invalid_number(value):
        raise DependencyBridgeError("noninteger dependency JSON number")
    try:
        value = json.loads(raw, object_pairs_hook=unique,
                           parse_constant=invalid_number, parse_float=invalid_number)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise DependencyBridgeError("invalid dependency JSON") from exc
    need(type(value) is dict, "dependency JSON must be an object")
    return value


def manifest_packages(raw):
    manifest = strict_object(raw)
    need(manifest.get("packagesDir") == ".lake/packages"
         and type(manifest.get("packages")) is list and manifest["packages"],
         "invalid pinned dependency manifest")
    expected = {}
    for item in manifest["packages"]:
        need(type(item) is dict and item.get("type") == "git"
             and type(item.get("name")) is str
             and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_-]*", item["name"])
             and item["name"] not in expected and type(item.get("rev")) is str
             and re.fullmatch(r"[a-f0-9]{40}", item["rev"]),
             "duplicate, unsafe or unpinned dependency")
        expected[item["name"]] = item["rev"]
    need(expected.get("mathlib") == MATHLIB_REV, "unauthorized historical mathlib")
    return expected


def verify_A2_dependency_bridge(files, head, *, manifest_raw):
    need(type(head) is str and re.fullmatch(r"[a-f0-9]{40}", head),
         "exact current source commit required")
    if isinstance(manifest_raw, str):
        manifest_raw = manifest_raw.encode("utf-8")
    packages = manifest_packages(manifest_raw)
    raw = files.get("historical_dependency_bridge.json")
    bridge = strict_object(raw)
    need(set(bridge) == FIELDS and bridge.get("format") == FORMAT
         and bridge.get("status") == STATUS
         and bridge.get("historical_head") == baseline.REPLAY_HEAD
         and bridge.get("historical_tree_sha") == baseline.REPLAY_TREE
         and bridge.get("historical_introducer") == baseline.INTRODUCER
         and bridge.get("current_head") == head
         and bridge.get("manifest_sha256") == hashlib.sha256(manifest_raw).hexdigest()
         and bridge.get("pinned_packages") == packages
         and all(bridge.get(flag) is False for flag in (
             "original_verifier_modified", "historical_project_proofs_reused",
             "independent_security_review", "mathematical_acceptance")),
         "corrected-baseline dependency bridge is stale, mixed-version or unauthenticated")
    return hashlib.sha256(raw).hexdigest()


def prepare(historical, current, head, output):
    from pr113_historical_a2_replay_v1 import dependency_bridge, unchanged, scalar
    old, now = Path(historical).resolve(strict=True), Path(current).resolve(strict=True)
    baseline.verify_positive_source(historical)
    need(old != now, "historical and current source must differ")
    need(type(head) is str and re.fullmatch(r"[a-f0-9]{40}", head), "bad current head")
    need(Path(scalar(now, "rev-parse", "--show-toplevel")).resolve() == now,
         "current source must be real checkout root")
    unchanged(now, head)
    baseline.git(now, "merge-base", "--is-ancestor", baseline.REPLAY_HEAD, head)
    dest = Path(output).absolute()
    need(not dest.exists() and not dest.is_symlink()
         and not any(p.is_symlink() for p in dest.parents), "fresh detached bridge required")
    dest = dest.resolve()
    need(not dest.is_relative_to(old) and not dest.is_relative_to(now),
         "bridge cannot be written inside source")
    # This checks all package revisions/cleanliness both before and after linking.
    packages = dependency_bridge(now, old)
    raw = (old / "lake-manifest.json").read_bytes()
    need(packages == manifest_packages(raw), "bridge package execution differs from manifest")
    receipt = {
        "format": FORMAT, "status": STATUS, "historical_head": baseline.REPLAY_HEAD,
        "historical_tree_sha": baseline.REPLAY_TREE,
        "historical_introducer": baseline.INTRODUCER, "current_head": head,
        "manifest_sha256": hashlib.sha256(raw).hexdigest(),
        "pinned_packages": dict(sorted(packages.items())),
        "original_verifier_modified": False, "historical_project_proofs_reused": False,
        "independent_security_review": False, "mathematical_acceptance": False,
    }
    encoded = (json.dumps(receipt, sort_keys=True, indent=2) + "\n").encode()
    verify_A2_dependency_bridge({"historical_dependency_bridge.json": encoded}, head,
                                manifest_raw=raw)
    unchanged(old, baseline.REPLAY_HEAD)
    unchanged(now, head)
    dest.parent.mkdir(parents=True, exist_ok=True)
    with dest.open("xb") as stream:
        stream.write(encoded)
    return receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--historical-source", required=True, type=Path)
    parser.add_argument("--current-source", required=True, type=Path)
    parser.add_argument("--current-head", required=True)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        receipt = prepare(args.historical_source, args.current_source, args.current_head, args.out)
    except (OSError, ValueError, RuntimeError) as exc:
        parser.exit(2, "HISTORICAL_A2_DEPENDENCY_BRIDGE_BLOCKED: " + str(exc) + "\n")
    print(json.dumps({"status": receipt["status"], "historical_head": receipt["historical_head"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
