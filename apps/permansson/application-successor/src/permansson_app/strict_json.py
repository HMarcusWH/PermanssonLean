"""Bounded wire JSON; deliberately distinct from semantic-schema validation."""
from __future__ import annotations
import json
from pathlib import Path
from .errors import AppError

MAX_BYTES = 131072
# Generated files (receipts, candidate metadata, native outputs) grow with the
# result, not with the request. They are read back with the whole-run output
# budget's per-file limit, so every file a budgeted run may write can be read.
MAX_RESULT_BYTES = 32 * 1024 ** 2


def _pairs(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise ValueError(f"duplicate JSON key: {k!r}")
        out[k] = v
    return out


def _reject(value):
    if isinstance(value, str):
        if any(0xD800 <= ord(c) <= 0xDFFF for c in value):
            raise ValueError("unpaired Unicode surrogate")
    elif isinstance(value, list):
        for child in value: _reject(child)
    elif isinstance(value, dict):
        for k, child in value.items():
            _reject(k)
            _reject(child)


def strict_loads(raw: bytes, *, max_bytes: int = MAX_BYTES):
    if not isinstance(raw, bytes) or len(raw) > max_bytes:
        raise AppError("INPUT_SIZE", "input exceeds supported byte limit")
    if raw.startswith(b"\xef\xbb\xbf"):
        raise AppError("INPUT_ENCODING", "UTF-8 BOM is unsupported")
    try:
        obj = json.loads(raw.decode("utf-8"), object_pairs_hook=_pairs,
                         parse_float=lambda _: (_ for _ in ()).throw(ValueError("JSON float is unsupported")),
                         parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite JSON constant")))
        _reject(obj)
        return obj
    except (ValueError, UnicodeError) as exc:
        raise AppError("INPUT_JSON", str(exc)) from exc


def strict_read(path: Path, *, max_bytes: int = MAX_BYTES):
    if path.is_symlink() or not path.is_file():
        raise AppError("INPUT_PATH", "input must be an ordinary file, not a symlink")
    try:
        with path.open("rb") as handle:
            raw = handle.read(max_bytes + 1)
    except OSError as exc:
        raise AppError("INPUT_PATH", str(exc)) from exc
    return raw, strict_loads(raw, max_bytes=max_bytes)


def read_result(path: Path):
    """Read a generated JSON file (a receipt or candidate metadata), not a request."""
    return strict_read(path, max_bytes=MAX_RESULT_BYTES)
