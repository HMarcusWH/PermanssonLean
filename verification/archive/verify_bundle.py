"""Restore an empty object database and replay accepted artifacts, never Lean."""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import stat
import subprocess
import sys

from verification.integrity.git_objects import GitRepo
from verification.integrity.reports import HardeningError, check_report, write_report
from .acquire_evidence import validate_evidence
from .create_bundle import (ACCEPTED, ACCEPTED_TREE, BASELINE, CORE, MAX_METADATA,
                            REPOSITORY, RESEARCH, R_IDENTITY, R_SOURCE, derive_registry,
                            object_inventory, validate_bindings, validate_registry_shape)
from .manifest import (MAX_BUNDLE, MAX_CLOSURE, MAX_OBJECT, MAX_OBJECTS, SHA, SHA256,
                       digest, fail, read_bounded, safe_path, strict_json, validate_manifest)


def bundle_header(path):
    """Validate only the header; callers must also import and fsck its pack."""
    path = Path(path)
    if path.stat().st_size > MAX_BUNDLE:
        fail("E_LIMIT", "Bundle exceeds fixed 256 MiB budget")
    refs, total = {}, 0
    with path.open("rb") as stream:
        if stream.readline(128) != b"# v2 git bundle\n":
            fail("E_BUNDLE_REFS", "Only unfiltered SHA-1 bundle version 2 is supported")
        while True:
            line = stream.readline(4097)
            total += len(line)
            if not line or len(line) > 4096 or total > MAX_METADATA:
                fail("E_BUNDLE_REFS", "Malformed or unbounded bundle header")
            if line == b"\n":
                break
            if line.startswith(b"-"):
                fail("E_BUNDLE_PREREQUISITE", "Incremental bundle prerequisites are forbidden")
            if line.startswith(b"@"):
                fail("E_BUNDLE_REFS", "Unknown bundle capability is forbidden")
            fields = line.rstrip(b"\n").split(b" ", 1)
            try:
                oid, ref = fields[0].decode("ascii"), fields[1].decode("ascii")
            except (IndexError, UnicodeError):
                fail("E_BUNDLE_REFS", "Invalid bundle ref header")
            if not SHA.fullmatch(oid) or ref in refs:
                fail("E_BUNDLE_REFS", "Duplicate or invalid bundle ref")
            refs[ref] = oid
    return refs


def parse_objects(path):
    raw = read_bounded(path)
    rows, total, previous = [], 0, ""
    for line in raw.splitlines():
        row = strict_json(line)
        if (not isinstance(row, dict) or set(row) != {"oid", "type", "size", "sha256"}
                or not SHA.fullmatch(row.get("oid", "")) or row["oid"] <= previous
                or row.get("type") not in {"commit", "tree", "blob", "tag"}
                or type(row.get("size")) is not int or row["size"] < 0
                or not SHA256.fullmatch(row.get("sha256", ""))):
            fail("E_OBJECT_INVENTORY", "Malformed, unsorted or duplicate object inventory row")
        if row["size"] > MAX_OBJECT:
            fail("E_LIMIT", "Declared object exceeds fixed object budget")
        total += row["size"]
        previous = row["oid"]
        rows.append(row)
    if not rows or len(rows) > MAX_OBJECTS or total > MAX_CLOSURE:
        fail("E_LIMIT", "Declared object closure exceeds fixed budget")
    return rows


def require_empty_scratch(path, *, create=True):
    path = Path(path).absolute()
    if path.is_symlink() or any(parent.is_symlink() for parent in path.parents):
        fail("E_MANIFEST_FORMAT", "Scratch path may not traverse a symlink", 2)
    path = path.resolve()
    if path.exists():
        if not path.is_dir() or any(path.iterdir()):
            fail("E_MANIFEST_FORMAT", "Scratch must be new or an empty directory", 2)
    elif create:
        path.mkdir(parents=True)
    return path


def restore_history(bundle, scratch, registry, expected_objects, *, after_import=None):
    """Actual empty-repository restoration, also used by tiny internal fixtures."""
    refs = validate_registry_shape(registry)
    if bundle_header(bundle) != refs:
        fail("E_BUNDLE_REFS", "Bundle header differs from exact named-ref registry")
    scratch = require_empty_scratch(scratch)
    root = scratch / "restored.git"
    git = __import__("shutil").which("git")
    if not git:
        fail("E_DEPENDENCY_MISSING", "Git unavailable for restoration", 3)
    environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    # Reject the inherited dependency before clearing it; sanitization must not
    # conceal a claimed clean-room precondition violation.
    if any(os.environ.get(name) for name in ("GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_COMMON_DIR")):
        fail("E_HISTORY_EXTERNAL", "Inherited Git object-store dependencies are forbidden")
    environment.update({"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                        "GIT_NO_REPLACE_OBJECTS": "1", "GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"})
    subprocess.run([git, "-c", "init.templateDir=", "init", "--bare", str(root)],
                   env=environment, capture_output=True, check=True, timeout=60)
    restored = GitRepo(root)
    if os.name == "nt":
        restored.run("config", "core.longpaths", "true")
    try:
        header_output = restored.run("bundle", "verify", str(Path(bundle).resolve()))
    except HardeningError as exc:
        raise HardeningError("E_BUNDLE_IMPORT", "Bundle verification failed before import: " + str(exc)) from exc
    try:
        restored.run("-c", "protocol.file.allow=always", "fetch", "--no-tags", "--no-write-fetch-head",
                     str(Path(bundle).resolve()), *[name + ":" + name for name in sorted(refs)])
    except HardeningError as exc:
        raise HardeningError("E_BUNDLE_IMPORT", "Bundle payload import failed: " + str(exc)) from exc
    restored.preflight()
    if restored.run("remote").strip():
        fail("E_HISTORY_EXTERNAL", "Restored repository unexpectedly has a remote")
    if after_import is not None:
        after_import(restored)  # private fixture injection; never a CLI option
    try:
        restored.run("fsck", "--full", "--strict")
    except HardeningError as exc:
        raise HardeningError("E_GIT_FSCK", "Restored object integrity check failed: " + str(exc)) from exc
    actual_refs = restored.run("for-each-ref", "--format=%(refname) %(objectname)")
    expected_refs = "".join(name + " " + oid + "\n" for name, oid in sorted(refs.items())).encode()
    if actual_refs != expected_refs:
        fail("E_BUNDLE_REFS", "Imported refs differ from exact expected targets")
    require_commit_targets(restored, refs)
    actual_objects = object_inventory(restored)
    closure = object_inventory(restored, sorted(refs))
    if actual_objects != expected_objects or closure != expected_objects:
        fail("E_OBJECT_INVENTORY", "Imported database/closure differs from exact object inventory")
    return restored


def require_commit_targets(repo, refs):
    for ref, oid in refs.items():
        try:
            repo.commit(oid)
        except HardeningError as exc:
            raise HardeningError("E_BUNDLE_REFS", "Required archive ref does not resolve to a commit: " + ref) from exc


def restore_checkout(repo, destination, sha=ACCEPTED):
    """Write canonical blobs without executing hooks, filters or symlink targets."""
    destination = Path(destination).absolute()
    if destination.exists():
        fail("E_MANIFEST_FORMAT", "Accepted checkout destination already exists")
    repo.run("worktree", "add", "--detach", "--no-checkout", str(destination), sha)
    for path, entry in repo.tree(sha).items():
        try:
            relative = safe_path(path.decode("utf-8"))
        except UnicodeError:
            fail("E_MANIFEST_FORMAT", "Accepted source has an unsupported non-UTF8 path")
        if entry.object_type != "blob" or entry.mode not in {"100644", "100755"}:
            fail("E_PROTECTED_TYPE", "Accepted source contains a nonregular source entry")
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(repo.blob(entry.oid, limit=MAX_OBJECT))
        target.chmod(0o755 if entry.mode == "100755" else 0o644)
    checkout = GitRepo(destination)
    checkout.run("-c", "core.autocrlf=false", "reset", "--mixed", sha)
    ensure_clean(checkout)
    return checkout


def ensure_clean(repo):
    if repo.run("-c", "core.autocrlf=false", "-c", "core.filemode=true", "status", "--porcelain", "--untracked-files=all").strip():
        fail("E_LEGACY_VERIFY", "Restored accepted source changed during artifact replay")


def run_legacy(checkout, archive):
    """Execute only the unchanged accepted verifier, package check and 29 tests."""
    import importlib.metadata
    try:
        version = importlib.metadata.version("pypdf")
    except importlib.metadata.PackageNotFoundError:
        fail("E_DEPENDENCY_MISSING", "Install pinned pypdf before the offline boundary", 3)
    if version != "6.10.0":
        fail("E_DEPENDENCY_MISSING", "Legacy replay requires pypdf==6.10.0", 3)
    root, kit = checkout.root, checkout.root / "release/v0.2.0"
    env = {key: value for key, value in checkout.env.items()
           if key not in {"PYTHONPATH", "PYTHONHOME"} and not key.startswith("GITHUB_")}
    env.update({"PYTHONDONTWRITEBYTECODE": "1", "CI": ""})
    results = []
    commands = [[sys.executable, "-B", str(kit / "verify_release.py")],
                [sys.executable, "-B", str(kit / "package_release.py"), "--verify"],
                [sys.executable, "-B", "-c",
                 "import sys,unittest;sys.path.insert(0,sys.argv[1]);"
                 "s=unittest.TestLoader().discover(sys.argv[1],pattern='test_*.py');"
                 "n=s.countTestCases();print('LEGACY_METHOD_COUNT='+str(n));"
                 "r=unittest.TextTestRunner(verbosity=2).run(s);"
                 "sys.exit(0 if n==29 and r.wasSuccessful() and not r.skipped else 1)", str(kit)],
                [sys.executable, "-B", "-c",
                 "import json,sys;sys.path.insert(0,sys.argv[1]);"
                 "from c10_archive_validation import validate_c10_archive;"
                 "from pathlib import Path;"
                 "print(json.dumps(validate_c10_archive(Path(sys.argv[2]),json.loads(sys.argv[3]),Path(sys.argv[4])),sort_keys=True))",
                 str(kit), str(Path(archive).resolve()), json.dumps(R_SOURCE), str(root)]]
    for index, command in enumerate(commands):
        try:
            done = subprocess.run(command, cwd=root, env=env, capture_output=True, timeout=300, check=False)
        except subprocess.TimeoutExpired as exc:
            raise HardeningError("E_COMMAND_TIMEOUT", "Accepted artifact replay exceeded its time budget") from exc
        if len(done.stdout) + len(done.stderr) > MAX_METADATA:
            fail("E_LIMIT", "Accepted replay diagnostic exceeds budget")
        output = (done.stdout + done.stderr).decode("utf-8", "replace")
        if done.returncode:
            code = "E_C10_CONTENT" if index == 3 else "E_LEGACY_VERIFY"
            fail(code, "Accepted artifact replay failed: " + output[-4000:])
        results.append({"stage": ["final_release_verifier", "package_verify_only", "legacy_29_tests", "R_c10_consistency"][index],
                        "exit_code": 0, "output_sha256": digest(done.stdout + done.stderr), "diagnostic_tail": output[-4000:]})
    return results


def validate_c10_content(archive, root, source=R_SOURCE):
    """Direct independent content stage for repaired-hash adversaries.

    This intentionally does not authenticate the outer publisher ZIP: production
    calls validate_evidence first; unit tests must reach content even after a
    controlled fixture's outer and nested hashes have been repaired.
    """
    root = Path(root).resolve()
    command = [sys.executable, "-B", "-c",
               "import json,sys;sys.path.insert(0,sys.argv[1]);"
               "from c10_archive_validation import validate_c10_archive;from pathlib import Path;"
               "print(json.dumps(validate_c10_archive(Path(sys.argv[2]),json.loads(sys.argv[3]),Path(sys.argv[4]))))",
               str(root / "release/v0.2.0"), str(Path(archive).resolve()), json.dumps(source), str(root)]
    environment = {key: value for key, value in os.environ.items() if key not in {"PYTHONPATH", "PYTHONHOME"}}
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    try:
        done = subprocess.run(command, cwd=root, env=environment, capture_output=True, timeout=60)
    except subprocess.TimeoutExpired as exc:
        raise HardeningError("E_COMMAND_TIMEOUT", "C10 content checker exceeded its budget") from exc
    if len(done.stdout) + len(done.stderr) > MAX_METADATA:
        fail("E_LIMIT", "C10 content diagnostics exceed budget")
    if done.returncode:
        fail("E_C10_CONTENT", "Independent C10 content rejected: " + done.stderr.decode("utf-8", "replace")[-3000:])
    return strict_json(done.stdout)


def validate_tooling(root, manifest):
    """Compare delivered tooling to this executing source closure, not itself."""
    source = Path(__file__).resolve().parents[1]
    expected = {}
    for directory in (source / "integrity", source / "archive"):
        for path in directory.rglob("*"):
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc":
                relative = "verification/" + path.relative_to(source).as_posix()
                expected[relative] = digest(path.read_bytes())
    rows = manifest["tooling"].get("files")
    if not isinstance(rows, list) or not SHA.fullmatch(manifest["tooling"].get("source_commit", "")):
        fail("E_TOOLING_CLOSURE", "Missing pre-packaging source commit/tooling closure")
    actual = {}
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"path", "blob", "sha256"}:
            fail("E_TOOLING_CLOSURE", "Malformed tooling source record")
        name = safe_path(row["path"])
        if name in actual or not SHA.fullmatch(row.get("blob", "")):
            fail("E_TOOLING_CLOSURE", "Duplicate or malformed tooling source identity")
        payload = read_bounded(Path(root) / "tooling" / name)
        if digest(payload) != row.get("sha256"):
            fail("E_TOOLING_CLOSURE", "Tooling content differs from its declared source")
        kind = b"blob " + str(len(payload)).encode() + b"\0"
        if __import__("hashlib").sha1(kind + payload).hexdigest() != row["blob"]:
            fail("E_TOOLING_CLOSURE", "Tooling Git blob identity differs")
        actual[name] = digest(payload)
    if actual != expected:
        fail("E_TOOLING_CLOSURE", "Delivered tooling differs from the executing committed tool closure")


def verify_supplement(supplement, scratch, require_isolation=True):
    if require_isolation:
        from .offline_smoke import isolation_attestation, require_dependencies
        isolation_attestation(os.environ.get("PERMANSSON_PARENT_NETNS"))
        require_dependencies()
    supplement = Path(supplement).absolute()
    if supplement.is_symlink() or any(parent.is_symlink() for parent in supplement.parents):
        fail("E_MANIFEST_FORMAT", "Supplement path may not traverse a symlink")
    supplement = supplement.resolve()
    scratch = require_empty_scratch(scratch, create=False)
    if scratch == supplement or supplement in scratch.parents or scratch in supplement.parents:
        fail("E_MANIFEST_FORMAT", "Scratch and supplement must be separate trees", 2)
    scratch.mkdir(parents=True, exist_ok=True)
    manifest = validate_manifest(supplement)
    if (manifest["repository"] != REPOSITORY or manifest["accepted_release"] != ACCEPTED
            or manifest["accepted_tree"] != ACCEPTED_TREE
            or manifest["provenance"] != {"frozen_core": CORE, "historical_baseline": BASELINE, "research_source": RESEARCH}
            or manifest["r_c10"] != {**R_IDENTITY, "source": R_SOURCE}):
        fail("E_REFERENCE_ID", "Supplement authority differs from the fixed release profile")
    validate_tooling(supplement, manifest)
    evidence = validate_evidence(supplement / "evidence")
    registry = strict_json(read_bounded(supplement / "refs.json"))
    objects = parse_objects(supplement / "objects.jsonl")
    if (len(objects) != manifest["object_inventory"].get("count")
            or sum(row["size"] for row in objects) != manifest["object_inventory"].get("uncompressed_size")
            or len(registry.get("refs", [])) != 36
            or len({row.get("commit") for row in registry.get("refs", [])}) != 26):
        fail("E_OBJECT_INVENTORY", "Registry/object measurements disagree")
    restored = restore_history(supplement / "history.bundle", scratch / "history", registry, objects)
    expected_registry = derive_registry(restored)
    if registry != expected_registry:
        fail("E_BUNDLE_REFS", "Restored registry differs from accepted authority-derived identities")
    validate_bindings(restored, expected_registry)
    receipt = restored.blob(restored.tree(ACCEPTED)[b"release/v0.2.0/acceptance-evidence.json"].oid)
    if read_bounded(supplement / "accepted-source-receipts.json") != receipt:
        fail("E_CAPTURE_ID", "Accepted source receipt convenience copy differs")
    checkout = restore_checkout(restored, scratch / "accepted")
    from verification.integrity.preservation import verify_preservation
    from verification.integrity.tex_export import compare_tex
    verify_preservation(checkout, ACCEPTED)
    compare_tex(checkout, ACCEPTED)
    replay = run_legacy(checkout, supplement / "evidence/R-c10.zip")
    ensure_clean(checkout)
    validate_manifest(supplement)
    return {"replay_target": ACCEPTED, "replay_tree": ACCEPTED_TREE,
            "completed_stages": ["delivered_inventory", "tooling_closure", "original_evidence", "empty_import", "strict_fsck",
                                 "exact_objects_refs", "parents_trees_ancestry", "canonical_checkout", "369_pins", "exact_tex", "legacy_replay", "post_replay_hashes"],
            "counts": {"refs": 36, "input_commits": 26, "objects": len(objects), "legacy_test_methods": 29},
            "source_restore": "PASS", "artifact_replay": "PASS", "fresh_lean_execution": "NOT_PERFORMED",
            "publisher_authentication": "NOT_CREATED_BY_OFFLINE_REPLAY", "evidence": evidence, "legacy": replay}


def main(argv=None):
    from .offline_smoke import invocation_context, restored_artifact_context
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--supplement", required=True)
    parser.add_argument("--scratch", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--repo")
    parser.add_argument("--candidate")
    args = parser.parse_args(argv)
    context = None
    try:
        context = invocation_context(args.repo, args.candidate)
        details = verify_supplement(args.supplement, args.scratch)
        if context is None:
            context = restored_artifact_context(args.scratch)
            details["acceptance_scope"] = "accepted_artifact_replay_only"
        result = check_report("archive-reproducibility", context, details=details, completed_stages=details["completed_stages"])
        code = 0
    except HardeningError as exc:
        result = check_report("archive-reproducibility", context, "BLOCKED" if exc.exit_code == 3 else "FAIL", exc)
        code = exc.exit_code
    except Exception as exc:
        result = check_report("archive-reproducibility", context, "FAIL", HardeningError("E_UNEXPECTED", str(exc)))
        code = 1
    write_report(args.report, result)
    print("archive-reproducibility: " + result["status"])
    return code


if __name__ == "__main__":
    raise SystemExit(main())
