"""Package or independently check the verified v0.2.0 research kit."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import zipfile

from verify_release import verify

PREFIX = "Permansson-v0.2.0-research/"
ARCHIVE = "Permansson_v0.2.0_research-kit.zip"
ENTRY_DATE_TIME = (2026, 10, 17, 0, 0, 0)
ENTRY_CREATE_SYSTEM = 3
ENTRY_EXTERNAL_ATTR = 0o100644 << 16
ENTRY_COMPRESSION = zipfile.ZIP_DEFLATED
COMPRESSION_LEVEL = 9
ENTRY_FIELDS = ("date_time", "create_system", "external_attr", "compress_type",
                "create_version", "extract_version", "internal_attr", "volume",
                "reserved", "comment", "extra")


def entry_info(relative: str) -> zipfile.ZipInfo:
    """One canonical metadata policy, shared by writing and independent checking."""
    info = zipfile.ZipInfo(PREFIX + relative, ENTRY_DATE_TIME)
    info.compress_type = ENTRY_COMPRESSION
    info.create_system = ENTRY_CREATE_SYSTEM
    info.external_attr = ENTRY_EXTERNAL_ATTR
    info.create_version = info.extract_version = 20
    info.internal_attr = info.volume = info.reserved = 0
    info.comment = info.extra = b""
    return info


def package(kit: Path, check_only: bool = False) -> None:
    verify(kit, allow_draft=False)
    manifest = json.loads((kit / "manifest.json").read_text(encoding="utf-8"))
    paths = sorted([*manifest["artifact_files"], "manifest.json"])
    archive = kit.parent / ARCHIVE
    checksum = kit.parent / (ARCHIVE + ".sha256")
    if not check_only:
        with zipfile.ZipFile(archive, "w", compression=ENTRY_COMPRESSION,
                             compresslevel=COMPRESSION_LEVEL) as bundle:
            for relative in paths:
                bundle.writestr(entry_info(relative), (kit / relative).read_bytes(),
                                compresslevel=COMPRESSION_LEVEL)
        checksum.write_text(hashlib.sha256(archive.read_bytes()).hexdigest() +
                            "  " + ARCHIVE + "\n", encoding="ascii", newline="\n")
    expected = hashlib.sha256(archive.read_bytes()).hexdigest() + "  " + ARCHIVE + "\n"
    if checksum.read_text(encoding="ascii") != expected:
        raise ValueError("Archive checksum mismatch")
    with zipfile.ZipFile(archive) as bundle:
        if bundle.comment != b"":
            raise ValueError("Archive comment differs from the deterministic metadata")
        names = [PREFIX + relative for relative in paths]
        if bundle.namelist() != names:
            raise ValueError("Archive entry set/order differs from the verified inventory")
        for relative in paths:
            payload = (kit / relative).read_bytes()
            entry = bundle.getinfo(PREFIX + relative)
            expected_info = entry_info(relative)
            for field in ENTRY_FIELDS:
                if getattr(entry, field) != getattr(expected_info, field):
                    raise ValueError("Archive metadata mismatch: " + relative + ": " + field)
            expected_flags = 0 if entry.filename.isascii() else 0x800
            if entry.flag_bits != expected_flags:
                raise ValueError("Archive metadata mismatch: " + relative + ": flag_bits")
            if entry.file_size != len(payload) or bundle.read(entry) != payload:
                raise ValueError("Archive payload mismatch: " + relative)
    print("Research archive verification PASS: " + str(len(paths)) + " inventoried entries")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="Check the existing archive without writing")
    args = parser.parse_args()
    package(Path(__file__).resolve().parent, args.verify)
