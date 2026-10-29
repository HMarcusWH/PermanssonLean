"""Bounded, retained T/T2 child diagnostics; never a security approval.

Keep restore scratch OUTSIDE the uploaded evidence directory. Empty raw logs
are represented in a nonempty JSON sidecar, not zero-byte artifact members.
The strict historical ZIP reader rejects zero-byte files and directories.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import tempfile
import time

FORMAT = "Permansson.PR113.T2ChildExecution.v1"
MAX_LOG_BYTES = 4 * 1024 * 1024


class EvidenceExecutionError(ValueError):
    pass


def require(value, message):
    if not value:
        raise EvidenceExecutionError(message)


def evidence_root(path):
    root = Path(path).absolute()
    require(not root.is_symlink()
            and not any(parent.is_symlink() for parent in root.parents)
            and root.is_dir(), "evidence root must be an existing unsymlinked directory")
    return root.resolve(strict=True)


def _stop(process):
    """Stop the process group so timeout children cannot keep writing."""
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        else:
            process.kill()
    except ProcessLookupError:
        pass
    process.wait(timeout=10)


def execute_logged(argv, cwd, environment, output, label, *, timeout=1800,
                   max_log_bytes=MAX_LOG_BYTES):
    """Execute a real child and retain diagnostics before raising on failure.

    The caller supplies a scrubbed environment and independently validates the
    actual verification reports. Exit zero alone never constitutes acceptance.
    """
    root = evidence_root(output)
    require(isinstance(label, str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]{0,47}", label),
            "invalid evidence log label")
    require(type(timeout) in (int, float) and 0 < timeout <= 7200
            and type(max_log_bytes) is int and 0 < max_log_bytes <= MAX_LOG_BYTES,
            "invalid child timeout or log budget")
    require(isinstance(argv, list) and argv
            and all(isinstance(arg, str) and "\0" not in arg for arg in argv),
            "invalid child argument vector")
    names = [label + suffix for suffix in (".stdout.log", ".stderr.log", ".execution.json")]
    require(all(not (root / name).exists() and not (root / name).is_symlink()
                for name in names), "existing evidence must not be overwritten")
    started = time.monotonic()
    failure = None
    process = None
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        try:
            process = subprocess.Popen(
                argv, cwd=cwd, env=environment, stdin=subprocess.DEVNULL,
                stdout=stdout, stderr=stderr, close_fds=True,
                start_new_session=(os.name == "posix"))
            while process.poll() is None:
                if any(os.fstat(stream.fileno()).st_size > max_log_bytes
                       for stream in (stdout, stderr)):
                    failure = "LOG_BUDGET_EXCEEDED"
                    _stop(process)
                    break
                if time.monotonic() - started > timeout:
                    failure = "TIMEOUT"
                    _stop(process)
                    break
                time.sleep(0.02)
            if failure is None and any(
                    os.fstat(stream.fileno()).st_size > max_log_bytes
                    for stream in (stdout, stderr)):
                failure = "LOG_BUDGET_EXCEEDED"
            if failure is None and process.returncode != 0:
                failure = "NONZERO_EXIT"
        except OSError as exc:
            failure = "LAUNCH_ERROR"
            stderr.write((type(exc).__name__ + ": " + str(exc)).encode("utf-8", "replace"))
        except BaseException:
            if process is not None and process.poll() is None:
                _stop(process)
            raise
        logs = {}
        content = {}
        for stream_name, stream in (("stdout", stdout), ("stderr", stderr)):
            stream.seek(0)
            data = stream.read(max_log_bytes)
            byte_count = os.fstat(stream.fileno()).st_size
            filename = label + "." + stream_name + ".log" if data else None
            if filename:
                with (root / filename).open("xb") as destination:
                    destination.write(data)
            logs[stream_name] = {
                "file": filename, "bytes": len(data),
                "sha256": hashlib.sha256(data).hexdigest(),
                "observed_bytes": byte_count, "truncated": byte_count > len(data),
            }
            content[stream_name] = data.decode("utf-8", "replace")
    receipt = {
        "format": FORMAT,
        "status": "CHILD_EXIT_ZERO_REPORTS_UNVERIFIED" if failure is None else "CHILD_FAILED",
        "label": label, "argv": argv, "cwd": str(Path(cwd).resolve()),
        "returncode": process.returncode if process is not None else None,
        "failure_kind": failure, "timeout_seconds": timeout,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "logs": logs, "independent_security_review": False,
        "required_ci_accepted": False, "merge_authorized": False,
    }
    with (root / names[2]).open("x", encoding="utf-8") as destination:
        json.dump(receipt, destination, sort_keys=True, indent=2)
        destination.write("\n")
    if failure is not None:
        reason = (content["stdout"] + content["stderr"])[-1800:]
        raise EvidenceExecutionError(
            label + " " + failure + " (exit " + str(receipt["returncode"])
            + "); retained " + str(root / names[2]) + ": " + reason)
    return subprocess.CompletedProcess(argv, 0, content["stdout"], content["stderr"])


def evidence_files(output, required=()):
    """Reject restore trees, symlinks and empty/oversize artifact members."""
    root = evidence_root(output)
    items = list(root.iterdir())
    require(1 <= len(items) <= 500, "unbounded evidence member inventory")
    result = {}
    total = 0
    for item in items:
        info = item.lstat()
        require(stat.S_ISREG(info.st_mode) and not item.is_symlink(),
                "restoration scratch or nonregular member in evidence: " + item.name)
        require(0 < info.st_size <= 64 * 1024 * 1024,
                "empty or oversized evidence member: " + item.name)
        total += info.st_size
        require(total <= 320 * 1024 * 1024, "oversized evidence total")
        require(item.name.casefold() not in result, "case-colliding evidence members")
        result[item.name.casefold()] = item
    require(set(required) <= {item.name for item in items}, "required evidence report missing")
    return sorted(item.name for item in items)


def read_report(path):
    """Read one bounded regular source report without accepting duplicate JSON."""
    from pr113_boundary_io import strict_json_object
    file = Path(path)
    require(file.is_file() and not file.is_symlink()
            and not any(parent.is_symlink() for parent in file.absolute().parents),
            "verification report is not a regular unsymlinked file")
    require(0 < file.stat().st_size <= MAX_LOG_BYTES, "verification report size out of bounds")
    with file.open("rb") as stream:
        data = stream.read(MAX_LOG_BYTES + 1)
    return strict_json_object(data, max_bytes=MAX_LOG_BYTES)
