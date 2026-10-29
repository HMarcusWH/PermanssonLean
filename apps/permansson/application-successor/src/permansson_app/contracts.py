"""Typed numeric request and result scope, not a scientific application certificate."""
from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from .errors import AppError

FORMAT = "Permansson.App.NumericRequest.v1"

@dataclass(frozen=True)
class NumericRequest:
    capability: str
    model_path: Path


def parse_request(value: object, *, request_file: Path) -> NumericRequest:
    if type(value) is not dict or set(value) != {"format", "capability", "input_file"}:
        raise AppError("REQUEST_SCOPE", "request must contain exactly format, capability, input_file")
    if value["format"] != FORMAT or type(value["capability"]) is not str:
        raise AppError("REQUEST_SCOPE", "unsupported request format or capability")
    rel_str = value["input_file"]
    if type(rel_str) is not str or not rel_str or "\\" in rel_str:
        raise AppError("REQUEST_PATH", "model path must be a relative POSIX file path")
    rel = Path(rel_str)
    if rel.is_absolute() or any(part in ("..", ".") for part in rel.parts):
        raise AppError("REQUEST_PATH", "model path cannot escape request directory")
    parent = request_file.parent.resolve()
    current = parent
    for part in rel.parts:
        current = current / part
        if current.is_symlink():
            raise AppError("REQUEST_PATH", "model path contains a symlink")
    resolved = current.resolve()
    if parent not in resolved.parents:
        raise AppError("REQUEST_PATH", "model path must be under request directory")
    if not resolved.is_file():
        raise AppError("REQUEST_PATH", "model input file is missing")
    return NumericRequest(value["capability"], resolved)
