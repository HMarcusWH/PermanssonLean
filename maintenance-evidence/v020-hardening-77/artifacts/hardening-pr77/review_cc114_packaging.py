"""Read-only exact-H delta and packaging review, with explicit identical-input reuse."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import sys
import time
from datetime import datetime, timezone
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[2] / "PermanssonLean-hardening"
sys.path.insert(0, str(ROOT))
from verification.integrity.git_objects import GitRepo
from verification.integrity.preservation import validate_maintenance_scope
from verification.archive.manifest import validate_manifest
from verification.archive.acquire_evidence import validate_evidence
from verification.archive.verify_bundle import validate_tooling, bundle_header, parse_objects

H = "cc114ee60ff8749b3bb64bb24a8d5e76d2120af9"
T = "a83d57a707afc91861fc5fec853d01f576ba0334"
PRIOR = "049d2620317afd10f8a584254d768f36af1d4979"
A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
MANIFEST = "019f816a67d492e65dfb3c3873d2f8a353b08b7706a73489251190a42572710a"
ZIP = "da51255e8f47c3c3e16ef28fd41611eb532f370887722654dc88e01ac7dd97d1"
BUNDLE = "56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f"
TEST = "7d177fb0876a78503c347bfea660421211cb18abf739bcc3ec3e47af1c081bac"

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

start = time.monotonic()
repo = GitRepo(ROOT)
require(repo.run("rev-parse", "HEAD").decode().strip() == H, "HEAD differs")
require(not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Worktree dirty")
trees = {sha: repo.tree(sha) for sha in (H, T, PRIOR, A)}
changes = sorted(path for path in set(trees[PRIOR]) | set(trees[H]) if trees[PRIOR].get(path) != trees[H].get(path))
expected = sorted(name.encode() for name in (
    "archival/v0.2.0/publication-candidate/Permansson_v0.2.0_archival-supplement-1.zip",
    "archival/v0.2.0/publication-candidate/Permansson_v0.2.0_archival-supplement-1.zip.sha256",
    "archival/v0.2.0/publication-candidate/README.md",
    "archival/v0.2.0/supplement-1/archive-manifest.json",
    "archival/v0.2.0/supplement-1/archive-manifest.sha256",
    "archival/v0.2.0/supplement-1/tooling/verification/integrity/tests/test_preservation.py",
    "verification/integrity/tests/test_preservation.py",
))
require(changes == expected, "Unexpected exact-H delta")
for path in changes:
    require(trees[H][path].mode == "100644" and trees[H][path].object_type == "blob", "Nonregular changed file")

supp = ROOT / "archival/v0.2.0/supplement-1"
prefix = supp.relative_to(ROOT).as_posix()
manifest = validate_manifest(supp)
require(digest((supp / "archive-manifest.json").read_bytes()) == MANIFEST, "Manifest digest differs")
require(manifest["tooling"]["source_commit"] == T, "Tooling commit differs")
validate_tooling(supp, manifest)
names = sorted(path.relative_to(supp).as_posix() for path in supp.rglob("*") if path.is_file())
require(len(names) == 68 and len(manifest["tooling"]["files"]) == 32, "Counts differ")
for name in names:
    entry = trees[H][(prefix + "/" + name).encode()]
    require(entry.mode == "100644" and entry.object_type == "blob", "Nonregular inner file")
    require(repo.blob(entry.oid) == (supp / name).read_bytes(), "Inner canonical bytes differ")
for row in manifest["tooling"]["files"]:
    key = row["path"].encode()
    source, head = trees[T][key], trees[H][key]
    payload = (supp / "tooling" / row["path"]).read_bytes()
    require(source == head and source.oid == row["blob"], "Tooling T/H identity differs")
    require(repo.blob(source.oid) == payload == (ROOT / row["path"]).read_bytes(), "Tooling canonical/executing/snapshot differs")
    require(digest(payload) == row["sha256"], "Tooling SHA-256 differs")
require(digest((ROOT / "verification/integrity/tests/test_preservation.py").read_bytes()) == TEST, "Test differs from independently reviewed bytes")
evidence = validate_evidence(supp / "evidence")
require(evidence["capture_files"] == 28, "Capture count differs")

registry = json.loads((supp / "refs.json").read_bytes())
refs = {row["ref"]: row["commit"] for row in registry["refs"]}
require(bundle_header(supp / "history.bundle") == refs and len(refs) == 36 and len(set(refs.values())) == 26, "Bundle refs differ")
require(digest((supp / "history.bundle").read_bytes()) == BUNDLE, "Historical bundle digest differs")
objects = parse_objects(supp / "objects.jsonl")
require(len(objects) == 8202 and sum(row["size"] for row in objects) == 27391135, "Object inventory measurements differ")
for name in ("history.bundle", "refs.json", "objects.jsonl"):
    key = (prefix + "/" + name).encode()
    require(trees[H][key] == trees[PRIOR][key], "Historical proof input changed")

validate_maintenance_scope(repo, H)
scope_changes = [path.decode() for path in set(trees[A]) | set(trees[H])
                 if trees[A].get(path) != trees[H].get(path)
                 and (path in (b"PermanssonLean.lean", b"PermanssonResearch.lean")
                      or any(path == root or path.startswith(root + b"/") for root in
                             (b"PermanssonLean", b"PermanssonResearch", b"release", b"application")))]
require(not scope_changes, "Lean/release/application scope differs")
prior = json.loads(Path(__file__).with_name("review-049-packaging.json").read_bytes())
require(prior["status"] == "PASS" and prior["head"] == PRIOR, "Previous reuse evidence differs")
# All seven changes are outside protected reference trees, authority, exporter,
# worker, candidate TeX and permanent production comparator; exact tree/blob
# identity establishes identical inputs for reuse, rather than a fresh run.
for path in (b"verification/integrity/policy.py", b"verification/integrity/preservation.py",
             b"verification/integrity/inventory.py", b"verification/integrity/git_objects.py",
             b"verification/integrity/tex_export.py", b"verification/integrity/_tex_worker.py"):
    require(trees[H][path] == trees[PRIOR][path], "Reused production checker changed")

publication = ROOT / "archival/v0.2.0/publication-candidate"
archive_path = publication / "Permansson_v0.2.0_archival-supplement-1.zip"
raw = archive_path.read_bytes()
require(len(raw) == 7437026 and digest(raw) == ZIP, "ZIP digest/size differs")
require(archive_path.with_suffix(".zip.sha256").read_bytes() == (ZIP + "  " + archive_path.name + "\n").encode(), "ZIP sidecar differs")
with ZipFile(archive_path) as archive:
    members = archive.infolist()
    require([item.filename for item in members] == names and len(set(names)) == 68 and not archive.comment, "ZIP inventory differs")
    for item in members:
        name = item.filename
        require(not name.startswith("/") and "\\" not in name and ":" not in name
                and all(part not in ("", ".", "..") for part in name.split("/"))
                and str(PurePosixPath(name)) == name, "Unsafe ZIP path")
        require(item.create_system == 3 and item.external_attr >> 16 == (stat.S_IFREG | 0o644)
                and item.date_time == (2026, 10, 17, 0, 0, 0)
                and not item.is_dir() and not item.flag_bits & 1, "ZIP mode/timestamp/type differs")
        require(archive.read(name) == (supp / name).read_bytes(), "ZIP payload differs from committed inner H")
for path in publication.iterdir():
    if path.is_file():
        entry = trees[H][path.relative_to(ROOT).as_posix().encode()]
        require(repo.blob(entry.oid) == path.read_bytes(), "Publication file differs from canonical H")
require(repo.run("rev-parse", "HEAD").decode().strip() == H and not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Source changed during review")

report = {
    "format": "Permansson.IndependentExactPackagingDeltaReview.v1", "status": "PASS",
    "executed_at": datetime.now(timezone.utc).isoformat(), "head": H, "tooling_commit": T,
    "previous_cleared_head": PRIOR, "accepted_release": A,
    "delta_paths": [path.decode() for path in changes],
    "test_source_sha256": TEST, "test_execution": "Already passed author and independent targeted execution at identical bytes; not rerun here",
    "supplement": {"files": len(names), "tooling_files": 32, "manifest_sha256": MANIFEST},
    "evidence": evidence,
    "historical_bundle": {"sha256": BUNDLE, "unchanged_from_previous_head": True, "refs": 36, "input_commits": 26, "objects": 8202, "uncompressed_bytes": 27391135, "reused_previous_exact_closure_review": True, "new_full_import": "NOT_PERFORMED"},
    "scope": {"lean_release_application_differences": scope_changes, "maintenance_scope": "PASS"},
    "reused_identical_input_results": {"source_head": PRIOR, "preservation": prior["preservation"], "tex": prior["tex"], "fresh_execution": False},
    "publication_zip": {"bytes": len(raw), "sha256": ZIP, "members": len(names), "all_payloads_equal_H": True, "regular_mode": "100644", "fixed_timestamp": "2026-10-17T00:00:00"},
    "elapsed_seconds": round(time.monotonic() - start, 3),
    "limits": ["No fresh GitHub CI or H/B/S observation", "No new empty import or Linux offline execution", "No fresh Lean execution", "No GitHub APPROVED review", "No settings, remote tag or external publication"],
}
target = Path(__file__).with_name("review-cc114.json")
target.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
print(json.dumps({key: report[key] for key in ("status", "head", "tooling_commit", "supplement", "publication_zip", "elapsed_seconds")}, indent=2))
print("External report: " + str(target))
