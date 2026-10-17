"""Bind the committed publication candidate to the verified canonical supplement."""
from __future__ import annotations

from io import BytesIO
from pathlib import Path
import stat
import struct
import zipfile
import zlib

from verification.integrity.reports import HardeningError
from .create_bundle import ACCEPTED, ACCEPTED_TREE
from .manifest import MAX_BUNDLE, MAX_CLOSURE, MAX_METADATA, SELF_FILES, digest, fail, read_bounded, safe_path

SUPPLEMENT_PREFIX = "archival/v0.2.0/supplement-1/"
ZIP_PATH = "archival/v0.2.0/publication-candidate/Permansson_v0.2.0_archival-supplement-1.zip"
MAX_PUBLICATION_FILES = 4096
FIXED_TIME = (2026, 10, 17, 0, 0, 0)


def _reject(message):
    fail("E_PUBLICATION_INTEGRITY", message)


def _verify_zip(payload, expected):
    """Bound classic-ZIP parsing before opening its central directory; never extract."""
    if len(payload) > MAX_BUNDLE or len(payload) < 22 or payload[-22:-18] != b"PK\x05\x06":
        _reject("Publication ZIP exceeds budget or lacks an empty-comment classic ZIP end record")
    _, disk, directory_disk, disk_count, count, size, offset, comment = struct.unpack("<4s4H2LH", payload[-22:])
    if (disk or directory_disk or comment or count != disk_count or count == 65535
            or count != len(expected) or count > MAX_PUBLICATION_FILES
            or offset + size != len(payload) - 22 or not payload.startswith(b"PK\x03\x04")):
        _reject("Publication ZIP has an unsupported, unbounded or inconsistent directory")
    # Do not trust the EOCD count before ZipFile allocates its ZipInfo objects.
    # A repaired end record could conceal many more actual directory entries.
    cursor, observed, end = offset, 0, offset + size
    while cursor < end:
        if cursor + 46 > end or payload[cursor:cursor + 4] != b"PK\x01\x02":
            _reject("Malformed publication central-directory record")
        name_size, extra_size, comment_size = struct.unpack_from("<3H", payload, cursor + 28)
        observed += 1
        cursor += 46 + name_size + extra_size + comment_size
        if observed > count or observed > MAX_PUBLICATION_FILES or cursor > end:
            _reject("Publication central-directory inventory exceeds its declared fixed budget")
    if cursor != end or observed != count:
        _reject("Publication central-directory count differs from the end record")
    try:
        with zipfile.ZipFile(BytesIO(payload)) as archive:
            entries = archive.infolist()
            if [entry.filename for entry in entries] != sorted(expected) or archive.comment:
                _reject("Publication ZIP member inventory/order differs from canonical C")
            local_cursor = 0
            for entry in entries:
                name = entry.filename
                try:
                    safe_path(name)
                except HardeningError as exc:
                    raise HardeningError("E_PUBLICATION_INTEGRITY", "Unsafe publication ZIP member path") from exc
                content = expected[name]
                if (entry.orig_filename != name or entry.is_dir() or entry.flag_bits & ~0x800 or entry.create_system != 3
                        or entry.external_attr >> 16 != stat.S_IFREG | 0o644
                        or entry.date_time != FIXED_TIME or entry.extra or entry.comment
                        or entry.compress_type not in {zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED}
                        or entry.file_size != len(content) or entry.header_offset >= offset):
                    _reject("Publication ZIP member has unsafe metadata or an unexpected size: " + name)
                if entry.header_offset != local_cursor or local_cursor + 30 > offset:
                    _reject("Publication local records contain a gap, overlap or invalid offset")
                local = struct.unpack_from("<4s5H3L2H", payload, local_cursor)
                filename = name.encode("utf-8" if entry.flag_bits & 0x800 else "cp437")
                if (local[:5] != (b"PK\x03\x04", entry.extract_version, entry.flag_bits, entry.compress_type, 0)
                        or local[5] != ((2026 - 1980) << 9 | 10 << 5 | 17)
                        or local[6:9] != (entry.CRC, entry.compress_size, entry.file_size)
                        or local[9:] != (len(filename), 0)
                        or payload[local_cursor + 30:local_cursor + 30 + len(filename)] != filename):
                    _reject("Publication local metadata differs from its canonical central record")
                local_cursor += 30 + len(filename) + entry.compress_size
                if local_cursor > offset:
                    _reject("Publication compressed member overlaps the central directory")
                with archive.open(entry) as stream:
                    actual = stream.read(len(content) + 1)
                if actual != content:
                    _reject("Publication ZIP member differs from canonical supplement: " + name)
            if local_cursor != offset:
                _reject("Publication ZIP has unreferenced bytes before its central directory")
    except (zipfile.BadZipFile, zlib.error, RuntimeError, NotImplementedError, OSError, ValueError, EOFError) as exc:
        raise HardeningError("E_PUBLICATION_INTEGRITY", "Cannot safely read publication ZIP") from exc


def validate_committed_publication(repo, candidate, supplement, manifest):
    """Authority is canonical C, including both manifest files and every inner path."""
    repo.validate_candidate(candidate, accepted_sha=ACCEPTED, accepted_tree=ACCEPTED_TREE)
    if repo.run("rev-parse", "HEAD").decode().strip() != candidate:
        _reject("Publication candidate differs from current checkout HEAD")
    tree = repo.tree(candidate)
    prefix = SUPPLEMENT_PREFIX.encode()
    entries = {path[len(prefix):].decode("utf-8"): entry for path, entry in tree.items() if path.startswith(prefix)}
    expected_names = {row["path"] for row in manifest["files"]} | SELF_FILES
    if not entries or len(entries) > MAX_PUBLICATION_FILES or set(entries) != expected_names:
        _reject("Committed supplement path set differs from the verified delivered inventory")
    expected, total = {}, 0
    for name, entry in entries.items():
        safe_path(name)
        if entry.object_type != "blob" or entry.mode != "100644":
            _reject("Committed supplement contains a nonregular or non-0644 path")
        limit = MAX_BUNDLE if name == "history.bundle" else MAX_METADATA
        content = repo.blob(entry.oid, limit=limit)
        total += len(content)
        if total > MAX_CLOSURE:
            _reject("Canonical supplement exceeds its aggregate byte budget")
        if read_bounded(Path(supplement) / name, limit) != content:
            _reject("Verified supplement filesystem differs from committed C: " + name)
        expected[name] = content
    archive, sidecar = tree.get(ZIP_PATH.encode()), tree.get((ZIP_PATH + ".sha256").encode())
    if any(entry is None or entry.object_type != "blob" or entry.mode != "100644" for entry in (archive, sidecar)):
        _reject("Committed publication ZIP and checksum must be regular 0644 blobs")
    payload = repo.blob(archive.oid, limit=MAX_BUNDLE)
    checksum = repo.blob(sidecar.oid, limit=256)
    if checksum != (digest(payload) + "  " + Path(ZIP_PATH).name + "\n").encode("ascii"):
        _reject("Committed publication ZIP checksum differs")
    _verify_zip(payload, expected)
    return {"status": "PASS", "scope": "canonical_candidate_objects", "candidate": candidate,
            "zip_path": ZIP_PATH, "zip_blob": archive.oid, "sidecar_blob": sidecar.oid,
            "zip_sha256": digest(payload), "zip_bytes": len(payload), "members": len(expected),
            "canonical_inner_files": len(expected), "verified_filesystem_matches_C": True}
