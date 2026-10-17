"""Independent local import of the repacked delivery; no offline/replay claim."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

workspace = Path(__file__).resolve().parents[2]
root = workspace / "PermanssonLean-hardening"
sys.path.insert(0, str(root))
from verification.integrity.git_objects import GitRepo
from verification.archive.manifest import validate_manifest, read_bounded, strict_json
from verification.archive.verify_bundle import validate_tooling, parse_objects, restore_history
from verification.archive.create_bundle import derive_registry, validate_bindings

H = "92e45179a5e3ecbe1b2bcadc4da54a0d1657f501"
PRIOR = "171c954c4733d2c8eaaac3ad90e60e4d1d4637c3"
OLD = "56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f"
NEW = "f49203e5a7f2189565c24509bd56652318ab383dfcda36ee756b78332b1e5792"
source = root / "archival/v0.2.0/supplement-1"
destination = workspace / "artifacts/hardening-pr77/restore-92e451"
report_path = workspace / "artifacts/hardening-pr77/local-restore-92e451.json"
start = time.monotonic()
repo = GitRepo(root)
restored = None
try:
    if repo.run("rev-parse", "HEAD").decode().strip() != H or repo.run("status", "--porcelain").strip():
        raise RuntimeError("Source is not clean exact H92")
    manifest = validate_manifest(source)
    tooling = validate_tooling(source, manifest, source_repo=root, source_candidate=H)
    if manifest["bundle"]["sha256"] != NEW or hashlib.sha256((source / "history.bundle").read_bytes()).hexdigest() != NEW:
        raise RuntimeError("Repacked bundle digest differs")
    trees = {sha: repo.tree(sha) for sha in (PRIOR, H)}
    identities = {}
    for name in ("refs.json", "objects.jsonl"):
        path = ("archival/v0.2.0/supplement-1/" + name).encode()
        if trees[PRIOR][path] != trees[H][path]:
            raise RuntimeError("Reference/object semantic input changed")
        identities[name] = trees[H][path].oid
    registry = strict_json(read_bounded(source / "refs.json"))
    objects = parse_objects(source / "objects.jsonl")
    if len(objects) != 8202 or sum(row["size"] for row in objects) != 27391135:
        raise RuntimeError("Expected closure measurements differ")
    restored = restore_history(source / "history.bundle", destination, registry, objects)
    if derive_registry(restored) != registry:
        raise RuntimeError("Restored registry differs from fixed accepted authority")
    validate_bindings(restored, registry)
    if repo.run("rev-parse", "HEAD").decode().strip() != H or repo.run("status", "--porcelain").strip():
        raise RuntimeError("Source changed during local restoration")
    report = {"format": "Permansson.IndependentRepackedBundleRestore.v1", "status": "PASS",
              "executed_at": datetime.now(timezone.utc).isoformat(), "head": H,
              "tooling_source": manifest["tooling"]["source_commit"], "tooling_binding": tooling,
              "manifest_sha256": hashlib.sha256((source / "archive-manifest.json").read_bytes()).hexdigest(),
              "bundle_sha256": NEW, "previous_bundle_sha256": OLD, "bundle_bytes_changed": True,
              "bundle_size": manifest["bundle"]["size"], "semantic_inputs": "UNCHANGED",
              "unchanged_semantic_Git_blobs": identities, "refs": len(registry["refs"]),
              "input_commits": len({row["commit"] for row in registry["refs"]}), "objects": len(objects),
              "uncompressed_bytes": sum(row["size"] for row in objects),
              "completed_stages": ["delivered_hashes", "canonical_T_C_tooling", "empty_database_import",
                                   "strict_full_fsck", "exact_all_objects_and_closure", "exact_named_refs",
                                   "accepted_registry", "ordered_parents_trees_and_ancestry"],
              "network_isolation": "NOT_ENFORCED", "artifact_replay": "NOT_PERFORMED",
              "fresh_lean_execution": "NOT_PERFORMED", "publisher_authentication": False,
              "elapsed_seconds": round(time.monotonic() - start, 3)}
    report_path.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
finally:
    if restored is not None:
        restored.close()
    repo.close()
