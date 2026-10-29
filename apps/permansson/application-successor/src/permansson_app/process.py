"""Linux-tested, bounded single merged-output subprocess driver."""
from __future__ import annotations
import os
import selectors
import subprocess
import sys
import time
from pathlib import Path
from .errors import AppError


def run_bounded(args: list[str], cwd: Path, log: Path, *, timeout: float = 45.0, max_output: int = 131072):
    if sys.platform == "win32":
        raise AppError("PLATFORM_UNQUALIFIED", "this development subprocess controller was only qualified on POSIX")
    env = {k: v for k, v in os.environ.items() if k not in ("PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP")}
    env["PYTHONNOUSERSITE"] = "1"
    try:
        proc = subprocess.Popen(args, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, env=env, close_fds=True)
    except OSError as exc:
        raise AppError("PROCESS_FAILED", str(exc)) from exc
    size = 0
    limit_at = time.monotonic() + timeout
    selector = selectors.DefaultSelector()
    assert proc.stdout is not None
    selector.register(proc.stdout.fileno(), selectors.EVENT_READ)
    try:
        with log.open("wb") as dest:
            while selector.get_map():
                remaining = limit_at - time.monotonic()
                if remaining <= 0:
                    raise AppError("PROCESS_TIMEOUT", "process exceeded its deadline")
                for key, _ in selector.select(min(0.25, remaining)):
                    buf = os.read(key.fileobj, 8192)
                    if not buf:
                        selector.unregister(key.fileobj)
                        continue
                    size += len(buf)
                    if size > max_output:
                        raise AppError("PROCESS_OUTPUT", "process exceeded output limit")
                    dest.write(buf)
        remaining = limit_at - time.monotonic()
        if remaining <= 0:
            raise AppError("PROCESS_TIMEOUT", "process exceeded its deadline")
        code = proc.wait(timeout=remaining)
        if code:
            raise AppError("PROCESS_FAILED", f"provider/checker process exited {code}")
        return {"exit_code": code, "stdout_stderr_bytes": size}
    except subprocess.TimeoutExpired as exc:
        raise AppError("PROCESS_TIMEOUT", "process exceeded its deadline") from exc
    finally:
        selector.close()
        if proc.stdout is not None:
            proc.stdout.close()
        if proc.poll() is None:
            proc.kill()
        proc.wait()
