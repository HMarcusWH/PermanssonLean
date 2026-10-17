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


def file_record(path, relative):
    relative = safe_path(relative)
    path = Path(path)
    if path.is_symlink() or not stat.S_ISREG(path.lstat().st_mode):
        fail("E_MANIFEST_FORMAT", "Nonregular delivered payload: " + relative)
    size = path.stat().st_size
    limit = MAX_BUNDLE if relative == "history.bundle" else MAX_METADATA
    if size > limit:
        fail("E_LIMIT", "Delivered payload exceeds budget: " + relative)
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


def scan_files(root):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        fail("E_MANIFEST_FORMAT", "Supplement must be a regular directory")
    records = []
    folded = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in dirs:
            if (Path(directory) / name).is_symlink():
                fail("E_MANIFEST_FORMAT", "Symlinked supplement directory")
        for name in files:
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            safe_path(relative)
            if relative.casefold() in folded:
                fail("E_MANIFEST_FORMAT", "Case-ambiguous delivered path")
            folded.add(relative.casefold())
            if relative not in SELF_FILES:
                records.append(file_record(path, relative))
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
    names = set()
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
