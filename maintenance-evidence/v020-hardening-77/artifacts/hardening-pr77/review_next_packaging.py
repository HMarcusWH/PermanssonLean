"""External read-only review for the maintenance-scope follow-up package."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import sys
import time
from zipfile import ZipFile

p = argparse.ArgumentParser()
for field in ("head", "tooling", "manifest", "zip-sha256", "test-sha256", "report"):
    p.add_argument("--" + field, required=True)
p.add_argument("--zip-size", type=int, required=True)
a = p.parse_args()
ROOT = Path(__file__).resolve().parents[2] / "PermanssonLean-hardening"
sys.path.insert(0, str(ROOT))
from verification.integrity.git_objects import GitRepo
from verification.integrity.maintenance_scope import verify_maintenance_candidate
from verification.archive.manifest import validate_manifest
from verification.archive.acquire_evidence import validate_evidence
from verification.archive.verify_bundle import validate_tooling, bundle_header, parse_objects

PRIOR = "cc114ee60ff8749b3bb64bb24a8d5e76d2120af9"
A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
BUNDLE = "56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f"
REVIEWED_MODULE = "fb55ab26b16ce02e154c0c349c9c319614f81713b16c5e9be403ab3c8d8b1411"
REVIEWED_SCHEMA = "f071aaebf6092081e99be315ec632954f8d64b493d5dfee19a044b36ef3eb5a6"

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

start = time.monotonic()
repo = GitRepo(ROOT)
need(repo.run("rev-parse", "HEAD").decode().strip() == a.head, "Current HEAD differs")
need(not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Worktree dirty")
trees = {revision: repo.tree(revision) for revision in (a.head, a.tooling, PRIOR, A)}
changed = sorted(path for path in set(trees[PRIOR]) | set(trees[a.head])
                 if trees[PRIOR].get(path) != trees[a.head].get(path))
allowed_tool_changes = {b"verification/integrity/maintenance_scope.py",
                        b"verification/integrity/tests/test_preservation.py",
                        b"verification/integrity/test_coverage.json",
                        b"verification/integrity/schemas/check-report.schema.json"}
source_changes = [path for path in changed if path.startswith((b"verification/", b".github/"))]
need(set(source_changes) == allowed_tool_changes, "Unexpected production/test/workflow source delta")
for path in changed:
    need(path in trees[a.head] and trees[a.head][path].mode == "100644"
         and trees[a.head][path].object_type == "blob", "Deleted or nonregular delta")
need(sha((ROOT / "verification/integrity/tests/test_preservation.py").read_bytes()) == a.test_sha256,
     "Test bytes differ from independent source-review target")
need(sha((ROOT / "verification/integrity/maintenance_scope.py").read_bytes()) == REVIEWED_MODULE
     and sha((ROOT / "verification/integrity/schemas/check-report.schema.json").read_bytes()) == REVIEWED_SCHEMA,
     "CLI/schema differ from independently reviewed bytes")

supp = ROOT / "archival/v0.2.0/supplement-1"
prefix = supp.relative_to(ROOT).as_posix()
manifest = validate_manifest(supp)
need(sha((supp / "archive-manifest.json").read_bytes()) == a.manifest, "Manifest digest differs")
need(manifest["tooling"]["source_commit"] == a.tooling, "Tooling identity differs")
validate_tooling(supp, manifest)
files = sorted(path.relative_to(supp).as_posix() for path in supp.rglob("*") if path.is_file())
need(len(files) == 69 and len(manifest["tooling"]["files"]) == 33, "Wrong supplement/tooling counts")
for name in files:
    entry = trees[a.head][(prefix + "/" + name).encode()]
    need(entry.mode == "100644" and entry.object_type == "blob"
         and repo.blob(entry.oid) == (supp / name).read_bytes(), "Inner canonical H identity differs")
for row in manifest["tooling"]["files"]:
    key = row["path"].encode()
    t, h = trees[a.tooling][key], trees[a.head][key]
    payload = (supp / "tooling" / row["path"]).read_bytes()
    need(t == h and t.oid == row["blob"] and repo.blob(t.oid) == payload
         == (ROOT / row["path"]).read_bytes() and sha(payload) == row["sha256"], "T/H/executing/snapshot tooling differs")
evidence = validate_evidence(supp / "evidence")
need(evidence["capture_files"] == 28, "Capture count differs")
evidence_prefix = (prefix + "/evidence/").encode()
need({k: v for k, v in trees[a.head].items() if k.startswith(evidence_prefix)}
     == {k: v for k, v in trees[PRIOR].items() if k.startswith(evidence_prefix)}, "Historical evidence changed")
for name in ("history.bundle", "refs.json", "objects.jsonl"):
    key = (prefix + "/" + name).encode()
    need(trees[a.head][key] == trees[PRIOR][key], "Historical restoration input changed")
registry = json.loads((supp / "refs.json").read_bytes())
refs = {row["ref"]: row["commit"] for row in registry["refs"]}
objects = parse_objects(supp / "objects.jsonl")
need(bundle_header(supp / "history.bundle") == refs and len(refs) == 36
     and len(set(refs.values())) == 26 and len(objects) == 8202
     and sum(row["size"] for row in objects) == 27391135
     and sha((supp / "history.bundle").read_bytes()) == BUNDLE, "Historical inventory measurements differ")

scope = verify_maintenance_candidate(repo, a.head)
need(scope["candidate"] == a.head and scope["candidate_tree"] == repo.commit(a.head).tree
     and scope["acceptance_only"] is True and scope["permanent_preservation_policy"] is False
     and scope["differences"] == [], "One-time maintenance result not candidate-bound")
reserved = (b"PermanssonLean", b"PermanssonResearch", b"release", b"application", b"paper",
            b"provenance", b"verification/destructive", b"verification/v0.1.8_release_gate", b"verification/lean")
protected_changes = [path.decode() for path in set(trees[A]) | set(trees[a.head])
                     if trees[A].get(path) != trees[a.head].get(path)
                     and (path in (b"PermanssonLean.lean", b"PermanssonResearch.lean")
                          or any(path == root or path.startswith(root + b"/") for root in reserved))]
need(not protected_changes, "Lean/release/frozen scope changed")

publication = ROOT / "archival/v0.2.0/publication-candidate"
zip_path = publication / "Permansson_v0.2.0_archival-supplement-1.zip"
raw = zip_path.read_bytes()
need(len(raw) == a.zip_size and sha(raw) == a.zip_sha256, "Publication ZIP size/digest differs")
need(zip_path.with_suffix(".zip.sha256").read_bytes()
     == (a.zip_sha256 + "  " + zip_path.name + "\n").encode(), "Publication ZIP sidecar differs")
with ZipFile(zip_path) as archive:
    entries = archive.infolist()
    need([entry.filename for entry in entries] == files and len(set(files)) == 69
         and archive.comment == b"", "ZIP inventory/order/comment differs")
    for entry in entries:
        name = entry.filename
        need(not name.startswith("/") and "\\" not in name and ":" not in name
             and all(part not in ("", ".", "..") for part in name.split("/"))
             and str(PurePosixPath(name)) == name and not entry.is_dir()
             and not entry.flag_bits & 1 and entry.create_system == 3
             and entry.external_attr >> 16 == stat.S_IFREG | 0o644
             and entry.date_time == (2026, 10, 17, 0, 0, 0), "Unsafe/noncanonical ZIP member")
        need(entry.file_size == (supp / name).stat().st_size, "ZIP declared payload size differs")
        need(archive.read(entry) == (supp / name).read_bytes(), "ZIP payload differs from H inner")
for path in publication.iterdir():
    if path.is_file():
        entry = trees[a.head][path.relative_to(ROOT).as_posix().encode()]
        need(entry.mode == "100644" and repo.blob(entry.oid) == path.read_bytes(), "Publication differs from canonical H")
need(repo.run("rev-parse", "HEAD").decode().strip() == a.head
     and not repo.run("status", "--porcelain", "--untracked-files=all").strip(), "Source changed during review")
report = {
    "format": "Permansson.IndependentMaintenanceFollowupPackagingReview.v1", "status": "PASS",
    "executed_at": datetime.now(timezone.utc).isoformat(), "head": a.head, "tooling_commit": a.tooling,
    "previous_cleared_head": PRIOR, "accepted_release": A, "source_delta": [path.decode() for path in source_changes],
    "all_delta_paths": [path.decode() for path in changed], "test_sha256": a.test_sha256,
    "reviewed_source_hashes": {"maintenance_scope.py": REVIEWED_MODULE, "check-report.schema.json": REVIEWED_SCHEMA},
    "supplement": {"files": 69, "tooling_files": 33, "manifest_sha256": a.manifest},
    "evidence": evidence, "historical_bundle": {"sha256": BUNDLE, "unchanged": True, "refs": 36,
    "input_commits": 26, "objects": 8202, "uncompressed_bytes": 27391135},
    "one_time_local_candidate_scope": scope, "protected_scope_changes": protected_changes,
    "publication_zip": {"bytes": len(raw), "sha256": sha(raw), "members": 69, "all_payloads_equal_H": True,
                        "mode": "100644", "fixed_timestamp": "2026-10-17T00:00:00"},
    "reused_identical_inputs": {"previous_head": PRIOR, "full_historical_closure_review": True,
                               "preservation_and_tex": True, "fresh_execution": False},
    "elapsed_seconds": round(time.monotonic() - start, 3),
    "limits": ["No genuine new PR H/B/S CI or merge acceptance", "No new full import or offline replay",
               "Local candidate scope must join independent genuine H/B/S evidence", "No GitHub APPROVED review",
               "No new Lean execution, mathematical promotion, settings, tags or external publication"],
}
Path(a.report).write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
print(json.dumps({k: report[k] for k in ("status", "head", "tooling_commit", "supplement", "publication_zip", "elapsed_seconds")}, indent=2))
