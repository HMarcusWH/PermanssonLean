"""Create an acyclic full-history supplement from fixed accepted Git objects."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import shutil
import subprocess
import tempfile

from verification.integrity.git_objects import GitRepo
from verification.integrity.reports import HardeningError
from .manifest import (FORMAT, MAX_CLOSURE, MAX_METADATA, MAX_OBJECT, MAX_OBJECTS,
                       SHA, atomic_json, digest, fail, file_record, scan_files,
                       stable_json, strict_json)

ACCEPTED = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
ACCEPTED_TREE = "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
RESEARCH = "5822cdff0fc360d9e368e10ff5f7576c3141a1b3"
BASELINE = "6191a1acbf00867042a21c8e6c4a532af43017bc"
CORE = "c018f79ea4ce46f4f679ad5bca254509778fc53c"
REPOSITORY = "HMarcusWH/PermanssonLean"
REF_PREFIX = "refs/archive/permansson/v0.2.0/"
R_SOURCE = {"repository": REPOSITORY, "pr_number": 76,
            "head_sha": "cdbe7ed5124781be495404122fac1de3315cb6ec",
            "base_sha": RESEARCH,
            "synthetic_merge_sha": "c70362b97ae7d0828a569fa15e194f9861b22b46"}
R_IDENTITY = {"artifact_id": 12106535829, "run_id": 39045919534, "size": 9377,
              "sha256": "75d61c01020f63d7f9555f10f32de9d63a09c0107536463ae549cdb85ebe9fc8"}
RECEIPT_PATH = b"release/v0.2.0/acceptance-evidence.json"


def derive_registry(repo):
    """Derive authority from A, never from a mutable candidate registry.

    The separately described package registry was not supplied locally. Names
    below implement its stated namespace/roles and are explicitly derived,
    rather than pretending to be a byte-identical copy of that missing input.
    """
    if repo.commit(ACCEPTED).tree != ACCEPTED_TREE:
        fail("E_REFERENCE_ID", "Accepted archive authority has the wrong tree")
    entry = repo.tree(ACCEPTED).get(RECEIPT_PATH)
    if entry is None or entry.mode != "100644" or entry.object_type != "blob":
        fail("E_REFERENCE_MISSING", "Accepted source receipt is unavailable")
    raw = repo.blob(entry.oid, limit=MAX_METADATA)
    receipt = strict_json(raw)
    if (receipt.get("repository") != REPOSITORY or receipt.get("accepted_source_sha") != RESEARCH
            or receipt.get("baseline_sha") != BASELINE or receipt.get("frozen_core_release_sha") != CORE):
        fail("E_REFERENCE_ID", "Accepted receipt provenance disagrees with fixed authority")
    milestones = []
    for row in receipt.get("receipts", []):
        milestones.append({"anchor": row["anchor"], "pr": row["pr"],
                           "head": row["source_sha"], "base": row["base_sha"],
                           "synthetic": row["synthetic_merge_sha"], "main": row["main_merge_sha"]})
    if [m["anchor"] for m in milestones] != ["C69", "C70", "E1", "F1", "A3", "D2", "X1"]:
        fail("E_REFERENCE_ID", "Accepted receipt has unexpected milestones")
    milestones.append({"anchor": "R", "pr": 76, "head": R_SOURCE["head_sha"],
                       "base": RESEARCH, "synthetic": R_SOURCE["synthetic_merge_sha"], "main": ACCEPTED})
    roots = {"release": ACCEPTED, "research-source": RESEARCH,
             "historical-baseline": BASELINE, "frozen-core": CORE}
    refs = [{"ref": REF_PREFIX + name, "commit": commit} for name, commit in roots.items()]
    for milestone in milestones:
        for role in ("head", "base", "synthetic", "main"):
            refs.append({"ref": REF_PREFIX + milestone["anchor"] + "/" + role,
                         "commit": milestone[role]})
    refs.sort(key=lambda item: item["ref"])
    if len(refs) != 36 or len({item["commit"] for item in refs}) != 26:
        fail("E_REFERENCE_ID", "Derived archive registry count differs from contract")
    return {"format": "Permansson.Hardening.ArchiveRefs.v1", "schema_version": 1,
            "provenance": {"kind": "derived_from_accepted_git_receipts_and_fixed_R",
                           "accepted_commit": ACCEPTED, "receipt_path": RECEIPT_PATH.decode(),
                           "receipt_blob": entry.oid, "receipt_sha256": digest(raw),
                           "external_registry_package_available": False},
            "refs": refs, "milestones": milestones}


def validate_registry_shape(registry):
    if not isinstance(registry, dict) or not isinstance(registry.get("refs"), list):
        fail("E_BUNDLE_REFS", "Missing named-ref registry")
    refs = {}
    for row in registry["refs"]:
        if not isinstance(row, dict) or set(row) != {"ref", "commit"}:
            fail("E_BUNDLE_REFS", "Malformed archive ref")
        name, oid = row["ref"], row["commit"]
        if (not isinstance(name, str) or not name.startswith(REF_PREFIX) or name in refs
                or any(part in {"", ".", ".."} for part in name.split("/"))
                or any(c in name for c in " ~^:?*[\\\n\r\t")
                or not SHA.fullmatch(oid)):
            fail("E_BUNDLE_REFS", "Unsafe, duplicate or malformed archive ref")
        refs[name] = oid
    if not refs:
        fail("E_BUNDLE_REFS", "Empty named-ref registry")
    return refs


def validate_bindings(repo, registry, *, production=True):
    if production and registry != derive_registry(repo):
        fail("E_BUNDLE_REFS", "Archive roots differ from exact accepted authority registry")
    refs = validate_registry_shape(registry)
    for oid in set(refs.values()):
        repo.commit(oid)
    for item in registry.get("milestones", []):
        expected = (item["base"], item["head"])
        synthetic, main = repo.commit(item["synthetic"]), repo.commit(item["main"])
        if synthetic.parents != expected or main.parents != expected:
            fail("E_PARENT_BINDING", "Ordered merge parents differ for " + item["anchor"])
        if synthetic.tree != main.tree:
            fail("E_TREE_BINDING", "Synthetic/main trees differ for " + item["anchor"])
        if production and item["anchor"] != "R":
            try:
                repo.run("merge-base", "--is-ancestor", item["main"], RESEARCH)
            except HardeningError as exc:
                raise HardeningError("E_ANCESTRY", "Milestone is not an ancestor of accepted research") from exc
    if production and repo.commit(ACCEPTED).tree != ACCEPTED_TREE:
        fail("E_TREE_BINDING", "Accepted release tree differs")


def object_inventory(repo, refs=None):
    """Inventory canonical payloads in bounded cat-file batches."""
    if refs is None:
        metadata = repo.run("cat-file", "--batch-all-objects", "--batch-check=%(objectname) %(objecttype) %(objectsize)", limit=MAX_METADATA)
    else:
        names = repo.run("rev-list", "--objects", "--no-object-names", *refs, limit=MAX_METADATA)
        metadata = repo.run("cat-file", "--batch-check=%(objectname) %(objecttype) %(objectsize)", input=names, limit=MAX_METADATA)
    descriptions = {}
    total = 0
    for line in metadata.splitlines():
        fields = line.split()
        if len(fields) != 3:
            fail("E_OBJECT_INVENTORY", "Malformed Git object inventory")
        oid, kind = fields[0].decode("ascii"), fields[1].decode("ascii")
        try:
            size = int(fields[2])
        except ValueError:
            fail("E_OBJECT_INVENTORY", "Invalid Git object size")
        if not SHA.fullmatch(oid) or kind not in {"blob", "tree", "commit", "tag"} or size < 0:
            fail("E_OBJECT_INVENTORY", "Invalid Git object metadata")
        if oid in descriptions:
            continue
        if size > MAX_OBJECT:
            fail("E_LIMIT", "Git object exceeds 128 MiB")
        total += size
        descriptions[oid] = (kind, size)
    if len(descriptions) > MAX_OBJECTS or total > MAX_CLOSURE:
        fail("E_LIMIT", "Git object closure exceeds fixed budget")
    rows, pending, batch_size = [], [], 0
    def flush():
        nonlocal pending, batch_size
        if not pending:
            return
        raw = repo.run("cat-file", "--batch", input=("\n".join(pending) + "\n").encode(),
                       limit=batch_size + len(pending) * 128)
        cursor = 0
        for oid in pending:
            end = raw.find(b"\n", cursor)
            header = raw[cursor:end].split()
            kind, size = descriptions[oid]
            if end < cursor or header != [oid.encode(), kind.encode(), str(size).encode()]:
                fail("E_OBJECT_INVENTORY", "Git batch header disagrees with inventory")
            start = end + 1
            content = raw[start:start + size]
            if len(content) != size or raw[start + size:start + size + 1] != b"\n":
                fail("E_OBJECT_INVENTORY", "Git batch payload is incomplete")
            if hashlib.sha1(kind.encode() + b" " + str(size).encode() + b"\0" + content).hexdigest() != oid:
                fail("E_OBJECT_INVENTORY", "Git object identity does not match payload")
            rows.append({"oid": oid, "type": kind, "size": size, "sha256": digest(content)})
            cursor = start + size + 1
        if cursor != len(raw):
            fail("E_OBJECT_INVENTORY", "Extra Git batch output")
        pending, batch_size = [], 0
    for oid, (_, size) in sorted(descriptions.items()):
        if pending and batch_size + size > 16 * 1024 * 1024:
            flush()
        pending.append(oid)
        batch_size += size
    flush()
    return rows


def build_history(repo, registry, destination, *, production=True):
    validate_bindings(repo, registry, production=production)
    refs = validate_registry_shape(registry)
    destination = Path(destination).absolute()
    if destination.exists():
        fail("E_MANIFEST_FORMAT", "Bundle destination must not exist", 2)
    with tempfile.TemporaryDirectory(prefix="permansson-archive-stage-") as temporary:
        root = Path(temporary) / "stage.git"
        subprocess.run([repo.executable, "-c", "init.templateDir=", "init", "--bare", str(root)], env=repo.env,
                       check=True, capture_output=True, timeout=60)
        stage = GitRepo(root)
        stage.run("-c", "protocol.file.allow=always", "fetch", "--no-tags", "--no-write-fetch-head",
                  str(repo.root), *sorted(set(refs.values())))
        for ref, oid in sorted(refs.items()):
            stage.run("update-ref", ref, oid)
        observed = stage.run("for-each-ref", "--format=%(refname) %(objectname)")
        if observed != "".join(ref + " " + oid + "\n" for ref, oid in sorted(refs.items())).encode():
            fail("E_BUNDLE_REFS", "Staging refs differ from exact approved registry")
        stage.run("bundle", "create", "--version=2", str(destination), *sorted(refs))
        return object_inventory(stage, sorted(refs))


def create_supplement(repo, evidence, output):
    """Production builder: clean T first, package outside the source tree."""
    from .acquire_evidence import validate_evidence
    evidence, requested_output = Path(evidence).resolve(), Path(output).absolute()
    if requested_output.exists() or requested_output.is_symlink():
        fail("E_MANIFEST_FORMAT", "Supplement output must be new", 2)
    if any(parent.is_symlink() for parent in requested_output.parents):
        fail("E_MANIFEST_FORMAT", "Supplement output may not traverse a symlink", 2)
    output = requested_output.resolve()
    if output == repo.root or repo.root in output.parents:
        fail("E_MANIFEST_FORMAT", "Package outside the repository before committing", 2)
    if repo.run("status", "--porcelain", "--untracked-files=all").strip():
        fail("E_TOOLING_DIRTY", "Commit clean tooling T before supplement packaging")
    tooling_commit = repo.run("rev-parse", "HEAD").decode().strip()
    registry = derive_registry(repo)
    validate_bindings(repo, registry)
    validate_evidence(evidence)
    output.mkdir(parents=True)
    shutil.copytree(evidence, output / "evidence")
    tree = repo.tree(ACCEPTED)
    (output / "accepted-source-receipts.json").write_bytes(repo.blob(tree[RECEIPT_PATH].oid))
    atomic_json(output / "refs.json", registry)
    objects = build_history(repo, registry, output / "history.bundle")
    (output / "objects.jsonl").write_bytes(b"".join(stable_json(row).replace(b"\n", b"") + b"\n" for row in objects))
    tooling = []
    for path, entry in sorted(repo.tree(tooling_commit).items()):
        relative = path.decode("utf-8")
        if not (relative.startswith("verification/integrity/") or relative.startswith("verification/archive/")):
            continue
        if entry.object_type != "blob" or entry.mode not in {"100644", "100755"}:
            fail("E_TOOLING_CLOSURE", "Tooling snapshot contains a nonregular source entry")
        payload = repo.blob(entry.oid)
        target = output / "tooling" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)
        tooling.append({"path": relative, "blob": entry.oid, "sha256": digest(payload)})
    if not any(row["path"] == "verification/archive/verify_bundle.py" for row in tooling):
        fail("E_TOOLING_CLOSURE", "Committed tooling snapshot is incomplete")
    guide = repo.tree(tooling_commit).get(b"archival/v0.2.0/README.md")
    if guide is None or guide.object_type != "blob" or guide.mode not in {"100644", "100755"}:
        fail("E_TOOLING_CLOSURE", "Commit the canonical offline guide before packaging")
    (output / "OFFLINE_REPRODUCTION.md").write_bytes(repo.blob(guide.oid))
    files = scan_files(output)
    by_path = {row["path"]: row for row in files}
    manifest = {"format": FORMAT, "schema_version": 1, "repository": REPOSITORY,
                "accepted_release": ACCEPTED, "accepted_tree": ACCEPTED_TREE,
                "provenance": {"frozen_core": CORE, "historical_baseline": BASELINE, "research_source": RESEARCH},
                "registry": {"path": "refs.json", "sha256": by_path["refs.json"]["sha256"], "count": 36, "distinct_commits": 26},
                "bundle": {"path": "history.bundle", "format": 2,
                           "size": by_path["history.bundle"]["size"], "sha256": by_path["history.bundle"]["sha256"]},
                "object_inventory": {"path": "objects.jsonl", "sha256": by_path["objects.jsonl"]["sha256"],
                                     "count": len(objects), "uncompressed_size": sum(row["size"] for row in objects)},
                "files": files, "r_c10": {**R_IDENTITY, "source": R_SOURCE},
                "tooling": {"source_commit": tooling_commit, "files": tooling},
                "dependencies": {"python": "3.13", "git": "SHA-1 Git with bundle v2", "pypdf": "6.10.0"},
                "reproduction_levels": {"source_restore": True, "artifact_replay": True,
                                        "fresh_lean_execution": False, "publisher_authentication": False}}
    encoded = stable_json(manifest)
    (output / "archive-manifest.json").write_bytes(encoded)
    (output / "archive-manifest.sha256").write_bytes((digest(encoded) + "  archive-manifest.json\n").encode())
    return manifest


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--evidence", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    try:
        result = create_supplement(GitRepo(args.repo), args.evidence, args.output)
        print("Supplement built; offline restoration remains required: " + str(result["object_inventory"]["count"]) + " objects")
        return 0
    except HardeningError as exc:
        print(exc.code + ": " + str(exc))
        return exc.exit_code


if __name__ == "__main__":
    raise SystemExit(main())
