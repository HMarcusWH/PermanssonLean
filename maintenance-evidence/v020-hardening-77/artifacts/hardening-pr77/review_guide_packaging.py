"""External read-only review for the source/guide closure follow-up package."""
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
for field in ("head", "tooling", "manifest", "zip-sha256", "reviewed-sources", "report"):
    p.add_argument("--" + field, required=True)
p.add_argument("--zip-size", type=int, required=True)
a = p.parse_args()
ROOT = Path(__file__).resolve().parents[2] / "PermanssonLean-hardening"
sys.path.insert(0, str(ROOT))
from verification.integrity.git_objects import GitRepo
from verification.integrity.maintenance_scope import verify_maintenance_candidate
from verification.integrity.preservation import verify_preservation
from verification.archive.manifest import validate_manifest
from verification.archive.acquire_evidence import validate_evidence
from verification.archive.verify_bundle import validate_tooling, bundle_header, parse_objects

PRIOR = "abccf9d7ce389fffe5637ea0ff0acd5718d9058f"
A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
BUNDLE = "56c401a24130fd37231d667fdbad3f5578587bb6a1c6d3c406698bd5a966537f"
reviewed_sources = json.loads(Path(a.reviewed_sources).read_bytes())
need_source_paths = set(reviewed_sources)

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
allowed_tool_changes = {name.encode() for name in need_source_paths}
source_changes = [path for path in changed if path.startswith((b"verification/", b".github/"))]
need(set(source_changes) == allowed_tool_changes, "Unexpected production/test/workflow source delta")
for path in changed:
    need(path in trees[a.head] and trees[a.head][path].mode == "100644"
         and trees[a.head][path].object_type == "blob", "Deleted or nonregular delta")
for name, expected in reviewed_sources.items():
    need(sha((ROOT / name).read_bytes()) == expected,
         "Current source differs from independently reviewed bytes: " + name)

supp = ROOT / "archival/v0.2.0/supplement-1"
prefix = supp.relative_to(ROOT).as_posix()
manifest = validate_manifest(supp)
need(sha((supp / "archive-manifest.json").read_bytes()) == a.manifest, "Manifest digest differs")
need(manifest["tooling"]["source_commit"] == a.tooling, "Tooling identity differs")
tooling_binding = validate_tooling(supp, manifest, source_repo=ROOT, source_candidate=a.head)
need(tooling_binding["binding"] == "canonical_T_C_and_executing_code"
     and tooling_binding["source_candidate"] == a.head
     and tooling_binding["reproduction_instructions_match"] is True, "Tooling binding is not current C/T/guide")
files = sorted(path.relative_to(supp).as_posix() for path in supp.rglob("*") if path.is_file())
need(len(files) == 70 and len(manifest["tooling"]["files"]) == 34, "Wrong supplement/tooling counts")
for name in files:
    entry = trees[a.head][(prefix + "/" + name).encode()]
    need(entry.mode == "100644" and entry.object_type == "blob"
         and repo.blob(entry.oid) == (supp / name).read_bytes(), "Inner canonical H identity differs")
for row in manifest["tooling"]["files"]:
    key = row["path"].encode()
    t, h = trees[a.tooling][key], trees[a.head][key]
    payload = (supp / "tooling" / row["path"]).read_bytes()
    need(t == h and t.oid == row["blob"] and repo.blob(t.oid) == payload
         and sha(payload) == row["sha256"], "T/H/snapshot tooling differs")
    if row["path"] != "archival/v0.2.0/README.md":
        need(payload == (ROOT / row["path"]).read_bytes(), "Executing source differs from canonical code")
need((supp / "OFFLINE_REPRODUCTION.md").read_bytes()
     == (supp / "tooling/archival/v0.2.0/README.md").read_bytes(), "Guide and reproduction copy differ")
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
preservation = verify_preservation(repo, a.head)
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
    need([entry.filename for entry in entries] == files and len(set(files)) == 70
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
    "previous_reviewed_head": PRIOR, "accepted_release": A, "source_delta": [path.decode() for path in source_changes],
    "all_delta_paths": [path.decode() for path in changed], "reviewed_source_hashes": reviewed_sources,
    "supplement": {"files": 70, "tooling_files": 34, "manifest_sha256": a.manifest, "tooling_binding": tooling_binding},
    "evidence": evidence, "historical_bundle": {"sha256": BUNDLE, "unchanged": True, "refs": 36,
    "input_commits": 26, "objects": 8202, "uncompressed_bytes": 27391135},
    "one_time_local_candidate_scope": scope, "preservation": preservation, "protected_scope_changes": protected_changes,
    "publication_zip": {"bytes": len(raw), "sha256": sha(raw), "members": 70, "all_payloads_equal_H": True,
                        "mode": "100644", "fixed_timestamp": "2026-10-17T00:00:00"},
    "reused_identical_inputs": {"previous_head": PRIOR, "full_historical_closure_review": True,
                               "tex": True, "fresh_execution": False},
    "elapsed_seconds": round(time.monotonic() - start, 3),
    "limits": ["No genuine new PR H/B/S CI or merge acceptance", "No new full import or offline replay",
               "Local candidate scope must join independent genuine H/B/S evidence", "No GitHub APPROVED review",
               "No new Lean execution, mathematical promotion, settings, tags or external publication"],
}
Path(a.report).write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
repo.close()
print(json.dumps({k: report[k] for k in ("status", "head", "tooling_commit", "supplement", "publication_zip", "elapsed_seconds")}, indent=2))
