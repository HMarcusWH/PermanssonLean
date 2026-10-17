"""Independent read-only exact-commit packaging review; writes external report only."""
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
from verification.integrity.preservation import verify_preservation, validate_maintenance_scope
from verification.integrity.tex_export import compare_tex
from verification.archive.manifest import validate_manifest
from verification.archive.acquire_evidence import validate_evidence
from verification.archive.verify_bundle import validate_tooling, bundle_header, parse_objects
from verification.archive.create_bundle import derive_registry, validate_bindings, object_inventory

H = "049d2620317afd10f8a584254d768f36af1d4979"
T = "562a22210e9e1cb23b19a6ebddacbc6bdc2bd6d0"
A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
PREVIOUS = "bd88afd584e4bb829458f47d3e6a4fb5ebaa09b6"
EXPECTED_MANIFEST = "d64c69508a89d677318c2d5a67a43e8ed2393911c5b22fdaee7cebf7d69b353c"
EXPECTED_BUNDLE = "56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f"
EXPECTED_ZIP = "4c95cc07f915612e4fd1270d75ed046449e7a2c33bbea02d5236e0058f16fe79"

def require(condition, description):
    if not condition:
        raise RuntimeError(description)

def digest(data):
    return hashlib.sha256(data).hexdigest()

started = time.monotonic()
repo = GitRepo(ROOT)
require(repo.run("rev-parse", "HEAD").decode().strip() == H, "Current head differs")
require(not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Worktree dirty")
trees = {sha: repo.tree(sha) for sha in (H, T, A, PREVIOUS)}
supp = ROOT / "archival/v0.2.0/supplement-1"
relative_supp = supp.relative_to(ROOT).as_posix()
manifest = validate_manifest(supp)
require(digest((supp / "archive-manifest.json").read_bytes()) == EXPECTED_MANIFEST, "Manifest pin differs")
require(manifest["tooling"]["source_commit"] == T, "Tooling commit differs")
validate_tooling(supp, manifest)

all_files = sorted(path.relative_to(supp).as_posix() for path in supp.rglob("*") if path.is_file())
require(len(all_files) == 68, "Wrong supplement count")
for name in all_files:
    key = (relative_supp + "/" + name).encode()
    entry = trees[H][key]
    require(entry.mode == "100644" and entry.object_type == "blob", "Nonregular supplement Git entry")
    require(repo.blob(entry.oid) == (supp / name).read_bytes(), "Working supplement differs from H")

tooling = manifest["tooling"]["files"]
require(len(tooling) == 32, "Wrong tooling count")
for row in tooling:
    key = row["path"].encode()
    t, h = trees[T][key], trees[H][key]
    payload = (supp / "tooling" / row["path"]).read_bytes()
    require(t == h and t.oid == row["blob"], "Tooling canonical identity mismatch")
    require(repo.blob(t.oid) == payload == (ROOT / row["path"]).read_bytes(), "Tooling source closure mismatch")
    require(digest(payload) == row["sha256"], "Tooling digest mismatch")

evidence = validate_evidence(supp / "evidence")
registry = json.loads((supp / "refs.json").read_bytes())
require(registry == derive_registry(repo), "Registry differs from accepted receipts")
validate_bindings(repo, registry)
refs = {row["ref"]: row["commit"] for row in registry["refs"]}
require(len(refs) == 36 and len(set(refs.values())) == 26, "Registry count mismatch")
require(bundle_header(supp / "history.bundle") == refs, "Bundle header mismatch")
require(digest((supp / "history.bundle").read_bytes()) == EXPECTED_BUNDLE, "Bundle digest mismatch")
require((supp / "history.bundle").read_bytes() == repo.blob(trees[PREVIOUS][b"archival/v0.2.0/supplement-1/history.bundle"].oid), "Historical bundle changed")
objects = parse_objects(supp / "objects.jsonl")
require(len(objects) == 8202 and sum(row["size"] for row in objects) == 27391135, "Object count/size mismatch")
require(objects == object_inventory(repo, sorted(set(refs.values()))), "Object inventory differs from actual historical closure")
oids = {row["oid"] for row in objects}
require(set(refs.values()) <= oids and T not in oids and H not in oids, "Historical roots or maintenance exclusion mismatch")

preservation = verify_preservation(repo, H)
validate_maintenance_scope(repo, H)
tex = compare_tex(repo, H)
all_changes = sorted(path for path in set(trees[A]) | set(trees[H]) if trees[A].get(path) != trees[H].get(path))
protected_scope_changes = [path.decode() for path in all_changes if path in (b"PermanssonLean.lean", b"PermanssonResearch.lean") or any(path == root or path.startswith(root + b"/") for root in (b"PermanssonLean", b"PermanssonResearch", b"release", b"application"))]
require(not protected_scope_changes, "Lean/release/application scope changed")
require(trees[T][b"verification/integrity/policy.py"] == trees[H][b"verification/integrity/policy.py"], "Policy differs between T and H")

publication = ROOT / "archival/v0.2.0/publication-candidate"
zip_path = publication / "Permansson_v0.2.0_archival-supplement-1.zip"
raw_zip = zip_path.read_bytes()
require(len(raw_zip) == 7436361 and digest(raw_zip) == EXPECTED_ZIP, "Publication ZIP digest/size differs")
require(zip_path.with_suffix(".zip.sha256").read_bytes() == (EXPECTED_ZIP + "  " + zip_path.name + "\n").encode(), "Publication sidecar differs")
with ZipFile(zip_path) as archive:
    infos = archive.infolist()
    names = [info.filename for info in infos]
    require(names == all_files and len(set(names)) == 68 and archive.comment == b"", "ZIP inventory/order/comment mismatch")
    for info in infos:
        name = info.filename
        require(not name.startswith("/") and "\\" not in name and ":" not in name and all(part not in ("", ".", "..") for part in name.split("/")) and str(PurePosixPath(name)) == name, "Unsafe ZIP member")
        require(info.create_system == 3 and info.external_attr >> 16 == stat.S_IFREG | 0o644 and info.date_time == (2026, 10, 17, 0, 0, 0), "ZIP mode/timestamp mismatch")
        require(not info.is_dir() and not info.flag_bits & 1, "ZIP directory/encryption")
        require(archive.read(name) == (supp / name).read_bytes(), "ZIP payload differs from committed H inner file")
for path in publication.iterdir():
    if path.is_file():
        entry = trees[H][path.relative_to(ROOT).as_posix().encode()]
        require(entry.mode == "100644" and repo.blob(entry.oid) == path.read_bytes(), "Publication differs from committed H")

require(repo.run("rev-parse", "HEAD").decode().strip() == H and not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Source changed during review")
report = {
    "format": "Permansson.IndependentExactPackagingReview.v1",
    "executed_at": datetime.now(timezone.utc).isoformat(),
    "status": "PASS", "head": H, "tooling_commit": T, "accepted_release": A,
    "runtime": {"python": sys.version, "platform": sys.platform},
    "supplement": {"files": len(all_files), "manifest_sha256": EXPECTED_MANIFEST, "tooling_files": len(tooling)},
    "historical_bundle": {"size": (supp / "history.bundle").stat().st_size, "sha256": EXPECTED_BUNDLE, "refs": len(refs), "input_commits": len(set(refs.values())), "objects": len(objects), "uncompressed_bytes": sum(row["size"] for row in objects), "historical_bundle_unchanged": True, "new_full_import": "NOT_PERFORMED_BY_THIS_REVIEW"},
    "evidence": evidence,
    "preservation": preservation,
    "tex": tex,
    "protected_scope_changes": protected_scope_changes,
    "publication_zip": {"bytes": len(raw_zip), "sha256": EXPECTED_ZIP, "members": len(all_files), "payloads_equal_committed_inner": True, "fixed_timestamp": "2026-10-17T00:00:00", "mode": "100644"},
    "elapsed_seconds": round(time.monotonic() - started, 3),
    "limits": ["No new GitHub H/B/S or CI observation", "No new Linux namespace/offline replay", "No GitHub APPROVED review", "No fresh Lean execution or mathematical promotion", "No settings, tag or external publication operation"],
}
target = Path(__file__).with_name("review-049-packaging.json")
target.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps({key: report[key] for key in ("status", "head", "tooling_commit", "supplement", "historical_bundle", "publication_zip", "elapsed_seconds")}, indent=2))
print("External report: " + str(target))
