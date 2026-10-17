"""Bounded, strict supplement inventories. Checksums do not authenticate publishers."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

from verification.integrity.reports import HardeningError

FORMAT = "Permansson.Hardening.Archive.v1"
MAX_METADATA = 8 * 1024 * 1024
MAX_BUNDLE = 256 * 1024 * 1024
MAX_OBJECT = 128 * 1024 * 1024
MAX_CLOSURE = 1024 * 1024 * 1024
MAX_OBJECTS = 200_000
# Fixed delivered-filesystem budgets, independent of Git object closure.
# The normal supplement is far below these ceilings.
MAX_FILES = 2048
MAX_TOTAL_BYTES = 512 * 1024 * 1024
MAX_DIRECTORIES = 2048
MAX_DIRECTORY_DEPTH = 128
SHA = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
SELF_FILES = {"archive-manifest.json", "archive-manifest.sha256"}


def fail(code, message, exit_code=1):
    raise HardeningError(code, message, exit_code)


def stable_json(value):
    return (json.dumps(value, ensure_ascii=True, sort_keys=True, indent=2) + "\n").encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def atomic_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    try:
        with temporary.open("xb") as stream:
            stream.write(stable_json(value))
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def strict_json(data, code="E_MANIFEST_FORMAT"):
    if len(data) > MAX_METADATA:
        fail("E_LIMIT", "JSON metadata exceeds the fixed 8 MiB budget")
    def pairs(rows):
        result = {}
        for key, value in rows:
            if key in result:
                fail(code, "Duplicate JSON key: " + key)
            result[key] = value
        return result
    try:
        return json.loads(data.decode("utf-8"), object_pairs_hook=pairs,
                          parse_constant=lambda value: fail(code, "Non-finite JSON number"))
    except (ValueError, UnicodeError) as exc:
        fail(code, "Invalid UTF-8 JSON: " + str(exc))


def safe_path(value):
    if (not isinstance(value, str) or not value or "\\" in value or ":" in value
            or any(ord(c) < 32 for c in value) or value.startswith("/")):
        fail("E_MANIFEST_FORMAT", "Unsafe delivered path")
    parts = value.split("/")
    if any(part in {"", ".", ".."} for part in parts) or str(PurePosixPath(value)) != value:
        fail("E_MANIFEST_FORMAT", "Noncanonical delivered path: " + value)
    return value


def read_bounded(path, limit=MAX_METADATA):
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        fail("E_MANIFEST_FORMAT", "Expected a regular delivered file: " + str(path))
    if path.stat().st_size > limit:
        fail("E_LIMIT", "Delivered file exceeds its size budget: " + str(path))
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        fail("E_LIMIT", "Delivered file grew beyond its size budget")
    return data


def file_record(path, relative, *, expected_size=None):
    relative = safe_path(relative)
    path = Path(path)
    metadata = path.lstat()
    if not stat.S_ISREG(metadata.st_mode) or _is_reparse(metadata):
        fail("E_MANIFEST_FORMAT", "Nonregular delivered payload: " + relative)
    size = metadata.st_size
    limit = MAX_BUNDLE if relative == "history.bundle" else MAX_METADATA
    if size > limit:
        fail("E_LIMIT", "Delivered payload exceeds budget: " + relative)
    if expected_size is not None:
        if size != expected_size:
            fail("E_MANIFEST_FORMAT", "Delivered payload changed after metadata preflight: " + relative)
        # A growing file cannot consume the budget reserved for later files.
        limit = min(limit, expected_size)
    hasher = hashlib.sha256()
    observed_size = 0
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            observed_size += len(chunk)
            if observed_size > limit:
                fail("E_LIMIT", "Delivered payload grew beyond its size budget: " + relative)
            hasher.update(chunk)
    if observed_size != size:
        fail("E_MANIFEST_FORMAT", "Delivered payload changed during inventory: " + relative)
    return {"path": relative, "size": size, "sha256": hasher.hexdigest()}


def _is_reparse(metadata):
    return bool(getattr(metadata, "st_file_attributes", 0)
                & getattr(stat, "FILE_ATTRIBUTE_REPARSE_POINT", 0x400))


def scan_files(root):
    root = Path(root)
    try:
        metadata = root.lstat()
    except OSError:
        fail("E_MANIFEST_FORMAT", "Supplement must be a regular directory")
    if not stat.S_ISDIR(metadata.st_mode) or _is_reparse(metadata):
        fail("E_MANIFEST_FORMAT", "Supplement must be a regular directory")
    # Walk entries incrementally: os.walk would first allocate an unbounded
    # directory listing. Complete the bounded metadata pass before any hashing.
    pending = [(root, 0)]
    payloads = []
    folded = set()
    file_count = directory_count = total_bytes = 0
    while pending:
        directory, depth = pending.pop()
        metadata = directory.lstat()
        if not stat.S_ISDIR(metadata.st_mode) or _is_reparse(metadata):
            fail("E_MANIFEST_FORMAT", "Nonregular delivered directory")
        with os.scandir(directory) as entries:
            for entry in entries:
                path = Path(entry.path)
                relative = safe_path(path.relative_to(root).as_posix())
                metadata = entry.stat(follow_symlinks=False)
                if _is_reparse(metadata):
                    fail("E_MANIFEST_FORMAT", "Reparse-point delivered path: " + relative)
                if stat.S_ISDIR(metadata.st_mode):
                    directory_count += 1
                    if directory_count > MAX_DIRECTORIES or depth + 1 > MAX_DIRECTORY_DEPTH:
                        fail("E_LIMIT", "Delivered directory traversal exceeds its fixed budget")
                    pending.append((path, depth + 1))
                elif stat.S_ISREG(metadata.st_mode):
                    file_count += 1
                    if file_count > MAX_FILES:
                        fail("E_LIMIT", "Delivered file count exceeds its fixed budget")
                    limit = MAX_BUNDLE if relative == "history.bundle" else MAX_METADATA
                    if metadata.st_size > limit:
                        fail("E_LIMIT", "Delivered payload exceeds budget: " + relative)
                    total_bytes += metadata.st_size
                    if total_bytes > MAX_TOTAL_BYTES:
                        fail("E_LIMIT", "Delivered aggregate bytes exceed their fixed budget")
                    if relative not in SELF_FILES:
                        payloads.append((path, relative, metadata.st_size))
                else:
                    fail("E_MANIFEST_FORMAT", "Nonregular delivered path: " + relative)
                folded_path = relative.casefold()
                if folded_path in folded:
                    fail("E_MANIFEST_FORMAT", "Case-ambiguous delivered path")
                folded.add(folded_path)
    records = [file_record(path, relative, expected_size=size) for path, relative, size in payloads]
    return sorted(records, key=lambda row: row["path"])


def validate_manifest(root):
    root = Path(root)
    raw = read_bounded(root / "archive-manifest.json")
    checksum = read_bounded(root / "archive-manifest.sha256", 256)
    expected = (digest(raw) + "  archive-manifest.json\n").encode("ascii")
    if checksum != expected:
        fail("E_EVIDENCE_HASH", "Detached archive manifest checksum differs")
    value = strict_json(raw)
    required = {"format", "schema_version", "repository", "accepted_release", "accepted_tree",
                "provenance", "registry", "bundle", "object_inventory", "files", "r_c10",
                "tooling", "dependencies", "reproduction_levels"}
    if (not isinstance(value, dict) or set(value) != required or value["format"] != FORMAT
            or type(value["schema_version"]) is not int or value["schema_version"] != 1):
        fail("E_MANIFEST_FORMAT", "Unknown or incomplete supplement manifest")
    if not SHA.fullmatch(value.get("accepted_release", "")) or not SHA.fullmatch(value.get("accepted_tree", "")):
        fail("E_MANIFEST_FORMAT", "Malformed accepted identity")
    rows = value["files"]
    if not isinstance(rows, list) or not rows:
        fail("E_MANIFEST_FORMAT", "Missing payload inventory")
    if len(rows) > MAX_FILES:
        fail("E_LIMIT", "Declared file count exceeds its fixed budget")
    names = set()
    total_declared_bytes = 0
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"path", "size", "sha256"}:
            fail("E_MANIFEST_FORMAT", "Malformed delivered payload record")
        name = safe_path(row["path"])
        if name in names or name in SELF_FILES:
            fail("E_MANIFEST_FORMAT", "Duplicate or self-inventoried payload")
        names.add(name)
        if type(row["size"]) is not int or row["size"] < 0 or not SHA256.fullmatch(row["sha256"]):
            fail("E_MANIFEST_FORMAT", "Malformed payload digest or size")
        if row["size"] > (MAX_BUNDLE if name == "history.bundle" else MAX_METADATA):
            fail("E_LIMIT", "Declared payload exceeds fixed budget")
        total_declared_bytes += row["size"]
        if total_declared_bytes > MAX_TOTAL_BYTES:
            fail("E_LIMIT", "Declared aggregate bytes exceed their fixed budget")
    observed = scan_files(root)
    if {row["path"] for row in observed} != names:
        fail("E_MANIFEST_FORMAT", "Missing or extra delivered payload")
    expected_by_path = {row["path"]: row for row in rows}
    for row in observed:
        if row != expected_by_path[row["path"]]:
            code = "E_BUNDLE_HASH" if row["path"] == "history.bundle" else "E_EVIDENCE_HASH"
            fail(code, "Payload digest/size mismatch: " + row["path"])
    for key in ("bundle", "object_inventory", "tooling", "registry", "r_c10", "provenance"):
        if not isinstance(value[key], dict):
            fail("E_MANIFEST_FORMAT", "Malformed " + key)
    if value["bundle"] != {"path": "history.bundle", "format": 2,
                           "size": expected_by_path.get("history.bundle", {}).get("size"),
                           "sha256": expected_by_path.get("history.bundle", {}).get("sha256")}:
        fail("E_MANIFEST_FORMAT", "Bundle record does not match payload inventory")
    registry_payload = expected_by_path.get("refs.json", {})
    if value["registry"] != {"path": "refs.json", "sha256": registry_payload.get("sha256"),
                              "count": 36, "distinct_commits": 26}:
        fail("E_MANIFEST_FORMAT", "Registry declaration differs from delivered inventory")
    object_record = value["object_inventory"]
    if (set(object_record) != {"path", "sha256", "count", "uncompressed_size"}
            or object_record["path"] != "objects.jsonl"
            or object_record["sha256"] != expected_by_path.get("objects.jsonl", {}).get("sha256")):
        fail("E_MANIFEST_FORMAT", "Object inventory declaration differs from delivered payload")
    if value["dependencies"] != {"python": "3.13", "git": "SHA-1 Git with bundle v2", "pypdf": "6.10.0"}:
        fail("E_MANIFEST_FORMAT", "Unsupported or misleading replay dependency declaration")
    if value["reproduction_levels"] != {"source_restore": True, "artifact_replay": True,
                                        "fresh_lean_execution": False, "publisher_authentication": False}:
        fail("E_MANIFEST_FORMAT", "Unsupported reproduction or authentication promotion")
    if set(value["tooling"]) != {"source_commit", "files"}:
        fail("E_MANIFEST_FORMAT", "Malformed tooling snapshot declaration")
    count = value["object_inventory"].get("count")
    size = value["object_inventory"].get("uncompressed_size")
    if type(count) is not int or type(size) is not int or count <= 0 or size < 0:
        fail("E_MANIFEST_FORMAT", "Invalid object-closure measurements")
    if count > MAX_OBJECTS or size > MAX_CLOSURE:
        fail("E_LIMIT", "Object closure exceeds fixed production budget")
    return value
