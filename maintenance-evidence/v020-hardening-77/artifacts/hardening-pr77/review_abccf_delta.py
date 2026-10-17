"""Independent read-only documentation integration delta after package clearance."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2] / "PermanssonLean-hardening"
sys.path.insert(0, str(ROOT))
from verification.integrity.git_objects import GitRepo
from verification.integrity.maintenance_scope import verify_maintenance_candidate
from verification.archive.manifest import validate_manifest
from verification.archive.verify_bundle import validate_tooling
from verification.archive.acquire_evidence import validate_evidence

H = "abccf9d7ce389fffe5637ea0ff0acd5718d9058f"
PREVIOUS = "3f2791d23b08d0dd157303d6c265c3dad036a349"
B = "37c0cb8f2fbe7934639127e5f8b6d64a01e6950f"
T = "cc0d29a38f3b27f4fdb760292790e677e4738d8d"
A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

start = time.monotonic()
repo = GitRepo(ROOT)
need(repo.run("rev-parse", "HEAD").decode().strip() == H, "Wrong HEAD")
need(not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Dirty source")
commit = repo.commit(H)
need(commit.parents == (PREVIOUS, B) and commit.tree == "965cc4973324439d46ccd8d610875c6940d7c6ab", "Wrong integration parents/tree")
trees = {rev: repo.tree(rev) for rev in (H, PREVIOUS, B, T, A)}
changes = sorted(path for path in set(trees[H]) | set(trees[PREVIOUS])
                 if trees[H].get(path) != trees[PREVIOUS].get(path))
need(changes and all(path.startswith(b"docs/hardening/") for path in changes), "Unexpected non-contract integration delta")
for path in changes:
    need(path in trees[H] and trees[H][path].mode == "100644"
         and trees[H][path].object_type == "blob", "Deleted/nonregular documentation delta")
def subtree(tree, prefix):
    return {path: entry for path, entry in tree.items() if path.startswith(prefix)}
need(subtree(trees[H], b"docs/hardening/") == subtree(trees[B], b"docs/hardening/"), "Integrated contract tree differs from accepted base B")
need(subtree(trees[H], b"archival/") == subtree(trees[PREVIOUS], b"archival/"), "Reviewed package changed")
for prefix in (b"verification/integrity/", b"verification/archive/"):
    need(subtree(trees[H], prefix) == subtree(trees[T], prefix), "Tooling differs from T")
    for path, entry in subtree(trees[H], prefix).items():
        need(repo.blob(entry.oid) == (ROOT / path.decode()).read_bytes(), "Executing tooling differs from H")
need(subtree(trees[H], b".github/") == subtree(trees[PREVIOUS], b".github/"), "Workflow/policy integration change")
supp = ROOT / "archival/v0.2.0/supplement-1"
manifest = validate_manifest(supp)
validate_tooling(supp, manifest)
evidence = validate_evidence(supp / "evidence")
need(manifest["tooling"]["source_commit"] == T and len(manifest["tooling"]["files"]) == 33
     and len(manifest["files"]) + 2 == 69, "Manifest tooling/counts differ")
scope = verify_maintenance_candidate(repo, H)
need(scope["candidate"] == H and scope["candidate_tree"] == commit.tree and scope["differences"] == [], "One-time local scope failed")
reserved = (b"PermanssonLean", b"PermanssonResearch", b"release", b"application", b"paper", b"provenance", b"verification/destructive", b"verification/v0.1.8_release_gate", b"verification/lean")
scope_changes = [path.decode() for path in set(trees[A]) | set(trees[H])
                 if trees[A].get(path) != trees[H].get(path)
                 and (path in (b"PermanssonLean.lean", b"PermanssonResearch.lean", b"lean-toolchain", b"lakefile.lean", b"lake-manifest.json")
                      or any(path == prefix or path.startswith(prefix + b"/") for prefix in reserved))]
need(not scope_changes, "Accepted protected/Lean/release/application/toolchain scope changed")
need(repo.run("rev-parse", "HEAD").decode().strip() == H
     and not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Source changed during review")
repo._config.cleanup()
report = {
    "format": "Permansson.IndependentIntegrationDeltaReview.v1", "status": "PASS",
    "executed_at": datetime.now(timezone.utc).isoformat(), "head": H,
    "tree": commit.tree, "parents": list(commit.parents), "base": B,
    "previous_reviewed_package": PREVIOUS, "tooling_commit": T,
    "delta_paths": [path.decode() for path in changes], "contract_tree_equals_B": True,
    "package_equals_previous_reviewed_head": True, "tooling_T_H_executing_equal": True,
    "supplement": {"files": 69, "tooling_files": 33, "capture_files": evidence["capture_files"],
                   "manifest_sha256": hashlib.sha256((supp / "archive-manifest.json").read_bytes()).hexdigest()},
    "one_time_local_candidate_scope": scope, "accepted_scope_differences": scope_changes,
    "elapsed_seconds": round(time.monotonic() - start, 3),
    "limits": ["Fresh genuine synthetic CI and current C10 remain separate", "Actual S one-time CLI receipt still required", "Earlier ZIP/closure review reused from identical canonical package", "No fresh Lean run, GitHub APPROVED review or OPS completion"],
}
target = Path(__file__).with_name("review-abccf-delta.json")
target.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: report[k] for k in ("status", "head", "tree", "delta_paths", "supplement", "elapsed_seconds")}, indent=2))
