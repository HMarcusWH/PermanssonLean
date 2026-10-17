"""Derive the frozen inventory from accepted canonical Git objects."""

from dataclasses import dataclass
import hashlib
import json
import re

from .policy import (
    MANIFEST_LIMIT, PRODUCTION_POLICY, PROTECTED_BLOB_LIMIT,
    PROTECTED_TOTAL_LIMIT, _InventoryPolicy,
)
from .reports import HardeningError

_OID = re.compile(r"[0-9a-f]{40}\Z")
_SHA256 = re.compile(r"[0-9a-f]{64}\Z")


@dataclass(frozen=True)
class ProtectedEntry:
    path: bytes
    group: str
    mode: str
    oid: str
    sha256: str
    size: int


def _invalid(message):
    raise HardeningError("E_POLICY_INVENTORY", message)


def _pairs(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            _invalid("duplicate JSON key: " + repr(key))
        obj[key] = value
    return obj


def parse_manifest(payload: bytes, policy: _InventoryPolicy):
    """Strict parser exposed for direct malformed-policy tests."""
    if len(payload) > MANIFEST_LIMIT:
        raise HardeningError("E_LIMIT", "reference manifest exceeds budget")
    try:
        data = json.loads(payload.decode("utf-8"), object_pairs_hook=_pairs,
                          parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    except (UnicodeError, ValueError) as exc:
        _invalid("invalid reference JSON: " + str(exc))
    if not isinstance(data, dict):
        _invalid("reference manifest must be an object")
    expected = {
        "schema_version": 1, "version": "0.2.0", "mode": "final",
        "baseline_sha": policy.historical_baseline,
        "selected_source_sha": policy.research_source,
        "accepted_source_sha": policy.research_source,
    }
    for key, value in expected.items():
        if type(data.get(key)) is not type(value) or data.get(key) != value:
            _invalid("reference identity/schema mismatch: " + key)
    rows = data.get("protected_files")
    if not isinstance(rows, list) or len(rows) != policy.historical_count:
        _invalid("historical inventory count mismatch")
    seen = set()
    for row in rows:
        if not isinstance(row, dict):
            _invalid("historical row must be an object")
        path = row.get("path")
        if not isinstance(path, str):
            _invalid("historical path must be text")
        try:
            raw = path.encode("ascii")
        except UnicodeError:
            _invalid("historical policy paths must be ASCII")
        if (not raw or raw.startswith(b"/") or b"\\" in raw or b"\x00" in raw
                or any(part in (b"", b".", b"..") for part in raw.split(b"/"))
                or b":" in raw or raw in seen):
            _invalid("invalid or duplicate historical path: " + repr(path))
        seen.add(raw)
        if row.get("mode") not in ("100644", "100755"):
            _invalid("historical entry is not a regular-file mode")
        if not isinstance(row.get("git_blob_sha1"), str) or not _OID.fullmatch(row["git_blob_sha1"]):
            _invalid("malformed historical blob identity")
        if not isinstance(row.get("sha256"), str) or not _SHA256.fullmatch(row["sha256"]):
            _invalid("malformed historical SHA-256")
    return data


def _under(path: bytes, root: bytes):
    return path == root or path.startswith(root + b"/")


def _load_reference_inventory(repo, policy: _InventoryPolicy):
    """Private tiny-policy seam for real Git fixtures; never selected by CLI."""
    try:
        authority = repo.commit(policy.accepted_release)
    except HardeningError as exc:
        raise HardeningError("E_REFERENCE_MISSING", "accepted authority commit is absent") from exc
    if authority.tree != policy.accepted_tree:
        raise HardeningError("E_REFERENCE_ID", "accepted authority tree differs from fixed pin")
    tree = repo.tree(policy.accepted_release)
    manifest_entry = tree.get(policy.manifest_path)
    if manifest_entry is None:
        raise HardeningError("E_REFERENCE_MISSING", "accepted manifest is absent")
    if manifest_entry.object_type != "blob" or manifest_entry.mode != "100644":
        _invalid("accepted manifest has invalid type/mode")
    payload = repo.blob(manifest_entry.oid, limit=MANIFEST_LIMIT)
    if hashlib.sha256(payload).hexdigest() != policy.manifest_sha256:
        _invalid("accepted manifest digest differs from fixed pin")
    data = parse_manifest(payload, policy)
    entries = []
    used = set()
    total = 0
    for row in data["protected_files"]:
        path = row["path"].encode("ascii")
        actual = tree.get(path)
        if (actual is None or actual.object_type != "blob" or actual.mode != row["mode"]
                or actual.oid != row["git_blob_sha1"]):
            _invalid("historical Git metadata differs: " + repr(row["path"]))
        blob = repo.blob(actual.oid, limit=PROTECTED_BLOB_LIMIT)
        digest = hashlib.sha256(blob).hexdigest()
        if digest != row["sha256"]:
            _invalid("historical blob digest differs: " + repr(row["path"]))
        entries.append(ProtectedEntry(path, "historical", actual.mode, actual.oid, digest, len(blob)))
        used.add(path)
        total += len(blob)
        if total > PROTECTED_TOTAL_LIMIT:
            raise HardeningError("E_LIMIT", "combined protected bytes exceed budget")
    release_paths = {path for path in tree if _under(path, policy.release_root)}
    release_paths.update(policy.outer_paths)
    if len(release_paths) != policy.release_count or used.intersection(release_paths):
        _invalid("release inventory count or disjointness mismatch")
    for path in sorted(release_paths):
        actual = tree.get(path)
        if actual is None or actual.object_type != "blob" or actual.mode not in ("100644", "100755"):
            _invalid("release inventory member has invalid type/mode: " + repr(path))
        blob = repo.blob(actual.oid, limit=PROTECTED_BLOB_LIMIT)
        entries.append(ProtectedEntry(path, "release_v020", actual.mode, actual.oid,
                                      hashlib.sha256(blob).hexdigest(), len(blob)))
        total += len(blob)
        if total > PROTECTED_TOTAL_LIMIT:
            raise HardeningError("E_LIMIT", "combined protected bytes exceed budget")
    if len(entries) != policy.historical_count + policy.release_count:
        _invalid("union inventory count mismatch")
    return tuple(sorted(entries, key=lambda entry: entry.path))


def load_reference_inventory(repo) -> tuple[ProtectedEntry, ...]:
    return _load_reference_inventory(repo, PRODUCTION_POLICY)


def inventory_digest(entries):
    payload = [{"path": e.path.decode("ascii"), "group": e.group, "mode": e.mode,
                "oid": e.oid, "sha256": e.sha256, "size": e.size} for e in entries]
    return hashlib.sha256(json.dumps(payload, ensure_ascii=True, sort_keys=True,
                                    separators=(",", ":")).encode("utf-8")).hexdigest()
