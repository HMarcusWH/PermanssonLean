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


def package(kit: Path, check_only: bool = False) -> None:
    verify(kit, allow_draft=False)
    manifest = json.loads((kit / "manifest.json").read_text(encoding="utf-8"))
    paths = sorted([*manifest["artifact_files"], "manifest.json"])
    archive = kit.parent / ARCHIVE
    checksum = kit.parent / (ARCHIVE + ".sha256")
    if not check_only:
        with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED,
                             compresslevel=9) as bundle:
            for relative in paths:
                info = zipfile.ZipInfo(PREFIX + relative, (2026, 10, 17, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                bundle.writestr(info, (kit / relative).read_bytes(), compresslevel=9)
        checksum.write_text(hashlib.sha256(archive.read_bytes()).hexdigest() +
                            "  " + ARCHIVE + "\n", encoding="ascii", newline="\n")
    expected = hashlib.sha256(archive.read_bytes()).hexdigest() + "  " + ARCHIVE + "\n"
    if checksum.read_text(encoding="ascii") != expected:
        raise ValueError("Archive checksum mismatch")
    with zipfile.ZipFile(archive) as bundle:
        names = [PREFIX + relative for relative in paths]
        if bundle.namelist() != names:
            raise ValueError("Archive entry set/order differs from the verified inventory")
        for relative in paths:
            payload = (kit / relative).read_bytes()
            entry = bundle.getinfo(PREFIX + relative)
            if entry.file_size != len(payload) or bundle.read(entry) != payload:
                raise ValueError("Archive payload mismatch: " + relative)
    print("Research archive verification PASS: " + str(len(paths)) + " inventoried entries")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="Check the existing archive without writing")
    args = parser.parse_args()
    package(Path(__file__).resolve().parent, args.verify)
