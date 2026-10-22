"""Passive, opt-in recorder for Lean subprocess calls in legacy unittest routes.

Installed only via an explicitly generated sitecustomize.py in a detached
test subprocess, and only when PR113_CAPTURE_DIR is supplied. The true
subprocess.run implementation receives the original arguments unchanged.
Recordings are UNREVIEWED observations, never independent approval.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import os
from pathlib import Path
import subprocess

MAX_SOURCE = 4 * 1024 * 1024
MAX_OUTPUT = 4 * 1024 * 1024
_COUNTER = itertools.count()


def _bytes(value):
    if value is None:
        return None
    if isinstance(value, bytes):
        return value
    if isinstance(value, str):
        return value.encode("utf-8", errors="replace")
    return None


def _source(argv, cwd):
    # Callers may use /usr/bin/lake, lake env lean, or a pinned lean binary.
    # Never execute or rewrite a compiler command in the recorder.
    parts = [str(x) for x in argv] if isinstance(argv, (list, tuple)) else []
    if not parts:
        return None
    exe = Path(parts[0]).name
    if not ((exe == "lake" and len(parts) >= 3 and parts[1:3] == ["env", "lean"])
            or exe in ("lean", "lean.exe")):
        return None
    sources = [x for x in parts[1:] if x.endswith(".lean")]
    if len(sources) != 1:
        return (parts, None, None)
    original = Path(sources[0])
    root = Path(cwd or os.getcwd())
    path = original if original.is_absolute() else root / original
    try:
        if not path.is_file() or path.is_symlink():
            return (parts, str(path), None)
        if path.stat().st_size > MAX_SOURCE:
            return (parts, str(path), None)
        return (parts, str(path), path.read_bytes())
    except OSError:
        return (parts, str(path), None)


def _record(directory, cmd, source_path, source, outcome=None, error=None):
    event = Path(directory) / ("event-%d-%06d" % (os.getpid(), next(_COUNTER)))
    event.mkdir(parents=True, exist_ok=False)
    stdout = _bytes(getattr(outcome, "stdout", None))
    stderr = _bytes(getattr(outcome, "stderr", None))
    for label, raw in (("source.lean", source), ("stdout.log", stdout),
                       ("stderr.log", stderr)):
        if raw is not None and len(raw) <= (MAX_SOURCE if label == "source.lean"
                                            else MAX_OUTPUT):
            (event / label).write_bytes(raw)
    meta = {
        "format": "Permansson.LegacyLeanCompilerObservation.v1",
        "status": "RAW_UNREVIEWED",
        "case_id_unverified": os.environ.get("PR113_CASE_ID"),
        "selected_method_unverified": os.environ.get("PR113_SELECTED_METHOD"),
        "command": cmd,
        "original_input_path_untrusted": source_path,
        "returncode": getattr(outcome, "returncode", None),
        "exception": str(error) if error is not None else None,
        "source_sha256": hashlib.sha256(source).hexdigest() if source is not None else None,
        "stdout_sha256": hashlib.sha256(stdout).hexdigest() if stdout is not None else None,
        "stderr_sha256": hashlib.sha256(stderr).hexdigest() if stderr is not None else None,
        "source_retained": source is not None and len(source) <= MAX_SOURCE,
        "stdout_retained": stdout is not None and len(stdout) <= MAX_OUTPUT,
        "stderr_retained": stderr is not None and len(stderr) <= MAX_OUTPUT,
        "independent_review": False,
        "ci_check_run_id": None,
    }
    (event / "observation.json").write_text(
        json.dumps(meta, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def install():
    """Patch only the current opted-in Python interpreter, not project files."""
    directory = os.environ.get("PR113_CAPTURE_DIR")
    if not directory:
        return
    if not Path(directory).is_dir():
        raise RuntimeError("requested detached compiler observation directory unavailable")
    original_run = subprocess.run
    if getattr(original_run, "_pr113_capture_installed", False):
        return

    def observed_run(*args, **kwargs):
        argv = args[0] if args else kwargs.get("args")
        observation = _source(argv, kwargs.get("cwd"))
        if observation is None:
            return original_run(*args, **kwargs)
        command, path, source = observation
        try:
            result = original_run(*args, **kwargs)
        except BaseException as exc:
            _record(directory, command, path, source, error=exc)
            raise
        _record(directory, command, path, source, outcome=result)
        return result

    observed_run._pr113_capture_installed = True
    subprocess.run = observed_run
