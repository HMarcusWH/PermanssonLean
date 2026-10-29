"""Pin exact native provider bytes; a hash is integrity, not independent acceptance."""
from hashlib import sha256
from pathlib import Path
from .errors import AppError


def check_source(source_root: Path, pinned: dict[str, str]):
    if not source_root.is_dir():
        raise AppError("SOURCE_UNVERIFIED", "repository root is missing")
    record = {}
    root = source_root.resolve()
    for rel, expected in sorted(pinned.items()):
        bits = Path(rel)
        if bits.is_absolute() or ".." in bits.parts:
            raise AppError("REGISTRY", "unsafe source pin")
        candidate = root
        for part in bits.parts:
            candidate /= part
            if candidate.is_symlink():
                raise AppError("SOURCE_UNVERIFIED", "source path contains a symlink")
        if not candidate.is_file() or root not in candidate.resolve().parents:
            raise AppError("SOURCE_UNVERIFIED", "missing provider: " + rel)
        actual = sha256(candidate.read_bytes()).hexdigest()
        if actual != expected:
            raise AppError("SOURCE_UNVERIFIED", "provider bytes differ: " + rel)
        record[rel] = actual
    return record
