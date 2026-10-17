"""Bounded, atomic machine reports and explicit verification failures."""
from __future__ import annotations

import argparse
import dataclasses
import json
import os
from pathlib import Path
import platform
import tempfile


class HardeningError(Exception):
    def __init__(self, code: str, message: str, exit_code: int = 1):
        super().__init__(message)
        self.code, self.message, self.exit_code = code, message, exit_code


def strict_json(data: bytes | str, code: str = "E_MANIFEST_FORMAT"):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise HardeningError(code, f"Duplicate JSON key: {key!r}")
            result[key] = value
        return result
    try:
        return json.loads(data, object_pairs_hook=pairs,
                          parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    except (ValueError, UnicodeError, TypeError) as exc:
        raise HardeningError(code, f"Invalid JSON: {str(exc)[:300]}") from exc


def write_report(path, payload):
    target = Path(path).resolve()
    for ancestor in target.parents:
        if (ancestor / ".git").exists():
            relative = target.relative_to(ancestor)
            # Reports are scratch outputs. Keep them outside source directories;
            # resolving first also catches a scratch-directory symlink into source.
            if relative.parts[0] not in {".hardening-reports", "artifacts"}:
                raise HardeningError("E_REPORT", "Use external scratch or a repository scratch-output directory", 2)
            break
    target.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False) + "\n").encode()
    if len(encoded) > 8 * 1024 * 1024:
        raise HardeningError("E_LIMIT", "Report exceeds 8 MiB")
    fd, temporary = tempfile.mkstemp(prefix=".report-", dir=target.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, target)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def check_report(check, context=None, status="PASS", error=None, **details):
    ctx = dataclasses.asdict(context) if dataclasses.is_dataclass(context) else (context or {})
    return {"format": "Permansson.Hardening.Check.v1", "schema_version": 1,
            "check": check, "status": status,
            "error_code": getattr(error, "code", None),
            "message": str(error)[:4000] if error else None,
            "context": ctx, "runtime": {"python": platform.python_version(), "platform": platform.system()},
            **details}


def run_cli(check, argv, verify_callback):
    from .git_objects import GitRepo
    from .ci_context import capture_context
    parser = argparse.ArgumentParser(description=check)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--report", required=True)
    args = parser.parse_args(argv)
    context = None
    try:
        repo = GitRepo(args.repo)
        context = capture_context(repo, args.candidate)
        result = verify_callback(repo, args.candidate)
        if dataclasses.is_dataclass(result):
            result = dataclasses.asdict(result)
        payload = check_report(check, context, completed_stages=["context", "verification"], details=result)
        code = 0
    except HardeningError as exc:
        payload = check_report(check, context, "BLOCKED" if exc.exit_code == 3 else "FAIL", exc,
                               details=getattr(exc, "details", {}))
        code = exc.exit_code
    except Exception as exc:
        payload = check_report(check, context, "FAIL", HardeningError("E_UNEXPECTED", str(exc)))
        code = 1
    write_report(args.report, payload)
    print(f"{check}: {payload['status']}" + (f" {payload['error_code']}" if payload['error_code'] else ""))
    return code
