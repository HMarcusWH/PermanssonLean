"""HARDENING.F2: execute the pinned exporter, then compare canonical TeX bytes.

This predicate is independent of preservation. It certifies faithful export,
not mathematical truth, PDF visual quality, or fresh proof execution.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading

from . import policy
from .reports import HardeningError, run_cli

TEX_PATH = b"release/v0.2.0/output/pdf/Permansson_Research_Companion_v0.2.0.tex"
INPUT_PATHS = {"builder": b"release/v0.2.0/build_release.py",
               "verifier": b"release/v0.2.0/verify_release.py",
               "manuscript": b"release/v0.2.0/manuscript.json"}
INPUT_NAMES = {"builder": "build_release.py", "verifier": "verify_release.py",
               "manuscript": "manuscript.json"}
MAX_OUTPUT = policy.TEX_OUTPUT_LIMIT
TIMEOUT = policy.TEX_TIMEOUT


@dataclass(frozen=True)
class _Reference:
    """Internal fixture seam; production entry points always use fixed policy."""
    accepted: str
    tree: str
    revision: str
    input_hashes: tuple[tuple[str, str], ...]
    tex_hash: str
    tex_size: int


def _production_reference():
    return _Reference(policy.ACCEPTED_RELEASE, policy.ACCEPTED_RELEASE_TREE, policy.RESEARCH_SOURCE,
                      tuple((key, policy.SHA256_PINS[key]) for key in INPUT_PATHS),
                      policy.SHA256_PINS["tex"], policy.TEX_EXPECTED_SIZE)


def _read_inputs(repo, reference):
    try:
        commit = repo.commit(reference.accepted)
    except HardeningError as exc:
        raise HardeningError("E_REFERENCE_MISSING", "Accepted exporter commit is unavailable") from exc
    if commit.tree != reference.tree:
        raise HardeningError("E_REFERENCE_ID", "Accepted exporter tree disagrees with fixed policy")
    entries = repo.tree(reference.accepted)
    inputs = {}
    for name, path in INPUT_PATHS.items():
        entry = entries.get(path)
        if entry is None:
            raise HardeningError("E_REFERENCE_MISSING", f"Missing accepted export input: {path.decode()}")
        if entry.object_type != "blob" or entry.mode != "100644":
            raise HardeningError("E_EXPORT_REFERENCE", f"Accepted export input is not a normal source file: {name}")
        inputs[name] = repo.blob(entry.oid, limit=MAX_OUTPUT)
    return inputs


def _bounded_worker(command, *, cwd, env, timeout=TIMEOUT, limit=MAX_OUTPUT):
    """Bound both pipes while reading; kill on overflow rather than buffer it."""
    try:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, close_fds=True)
    except OSError as exc:
        raise HardeningError("E_DEPENDENCY_MISSING", "Cannot launch isolated Python worker", 3) from exc
    buffers = {"stdout": bytearray(), "stderr": bytearray()}
    overflow = threading.Event()
    reader_errors = []

    def read_pipe(name, stream, budget):
        try:
            while True:
                chunk = stream.read(16384)
                if not chunk:
                    break
                remaining = budget - len(buffers[name])
                buffers[name].extend(chunk[:max(remaining, 0)])
                if len(chunk) > remaining:
                    overflow.set()
                    process.kill()
                    break
        except (OSError, ValueError) as exc:
            reader_errors.append(str(exc))
        finally:
            stream.close()

    readers = [threading.Thread(target=read_pipe, args=("stdout", process.stdout, limit), daemon=True),
               threading.Thread(target=read_pipe, args=("stderr", process.stderr, 8192), daemon=True)]
    for reader in readers:
        reader.start()
    timed_out = False
    try:
        process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        process.kill()
        process.wait()
    for reader in readers:
        reader.join(timeout=5)
    if any(reader.is_alive() for reader in readers):
        raise HardeningError("E_COMMAND_TIMEOUT", "Worker output pipes did not close")
    if timed_out:
        raise HardeningError("E_COMMAND_TIMEOUT", "Isolated exporter exceeded its time budget")
    if overflow.is_set():
        raise HardeningError("E_LIMIT", "Isolated exporter exceeded its stdout/stderr budget")
    if reader_errors:
        raise HardeningError("E_EXPORT_REFERENCE", "Could not read isolated exporter output")
    diagnostic = bytes(buffers["stderr"]).decode("utf-8", "replace")
    if process.returncode:
        prefix = "PERMANSSON_TEX_ERROR "
        if diagnostic.startswith(prefix):
            try:
                error = json.loads(diagnostic[len(prefix):])
                if error.get("code") in {"E_IMPORT_ORIGIN", "E_REFERENCE_MISSING", "E_EXPORT_REFERENCE"}:
                    raise HardeningError(error["code"], str(error["message"])[:2000])
            except (ValueError, KeyError, TypeError):
                pass
        raise HardeningError("E_EXPORT_REFERENCE", "Isolated exporter failed: " + diagnostic[:2000])
    if diagnostic:
        raise HardeningError("E_EXPORT_REFERENCE", "Isolated exporter emitted unexpected diagnostics: " + diagnostic[:2000])
    return bytes(buffers["stdout"])


def _render_trusted_inputs(inputs, reference, *, worker=None, timeout=TIMEOUT, cwd=None, environment=None):
    expected = dict(reference.input_hashes)
    if set(inputs) != set(INPUT_NAMES):
        raise HardeningError("E_REFERENCE_MISSING", "Trusted exporter dependency closure is incomplete")
    for name, data in inputs.items():
        if len(data) > MAX_OUTPUT:
            raise HardeningError("E_LIMIT", "Trusted input exceeds export input budget")
        if hashlib.sha256(data).hexdigest() != expected.get(name):
            raise HardeningError("E_EXPORT_REFERENCE", f"Trusted {name} digest disagrees with fixed policy")
    with tempfile.TemporaryDirectory(prefix="permansson-trusted-tex-") as directory:
        trusted = Path(directory).resolve()
        for name, filename in INPUT_NAMES.items():
            (trusted / filename).write_bytes(inputs[name])
        worker_path = Path(worker).resolve() if worker is not None else Path(__file__).with_name("_tex_worker.py").resolve()
        command = [sys.executable, "-I", "-S", "-B", str(worker_path), str(trusted), reference.revision,
                   expected["manuscript"], expected["builder"], expected["verifier"], INPUT_NAMES["manuscript"]]
        # Isolated interpreter flags are the import boundary. Sanitization also
        # prevents unrelated startup/debug/encoding settings affecting execution.
        env = dict(os.environ if environment is None else environment)
        env = {key: value for key, value in env.items() if not key.upper().startswith("PYTHON")}
        result = _bounded_worker(command, cwd=str(cwd or trusted), env=env, timeout=timeout)
    if len(result) != reference.tex_size or hashlib.sha256(result).hexdigest() != reference.tex_hash:
        raise HardeningError("E_EXPORT_REFERENCE", "Trusted export differs from the independently pinned size/digest")
    return result


def render_accepted_tex(repo):
    reference = _production_reference()
    return _render_trusted_inputs(_read_inputs(repo, reference), reference)


def _compare_tex(repo, candidate, reference):
    repo.validate_candidate(candidate, accepted_sha=reference.accepted, accepted_tree=reference.tree)
    expected = _render_trusted_inputs(_read_inputs(repo, reference), reference)
    entry = repo.tree(candidate).get(TEX_PATH)
    if entry is None or entry.object_type != "blob" or entry.mode != "100644":
        raise HardeningError("E_TEX_TYPE", "Candidate TeX must be a committed normal nonexecutable file")
    actual = repo.blob(entry.oid, limit=MAX_OUTPUT)
    result = {"scope": "canonical_commit_objects", "expected_sha256": hashlib.sha256(expected).hexdigest(),
              "actual_sha256": hashlib.sha256(actual).hexdigest(), "expected_size": len(expected),
              "actual_size": len(actual), "equation_records": expected.count(b"\n\\companionEquation{"),
              "reference_revision": reference.revision,
              "completed_stages": ["trusted_input_hashes", "isolated_reference_render", "reference_output_pin", "candidate_byte_comparison"]}
    if actual != expected:
        offset = next((index for index, pair in enumerate(zip(expected, actual)) if pair[0] != pair[1]), min(len(expected), len(actual)))
        error = HardeningError("E_TEX_MISMATCH", "Candidate TeX does not exactly reproduce trusted export: " +
                               json.dumps({**{key: result[key] for key in ("expected_sha256", "actual_sha256", "expected_size", "actual_size")},
                                           "first_differing_byte": offset}, sort_keys=True))
        error.details = {**result, "first_differing_byte": offset}
        raise error
    return result


def compare_tex(repo, candidate):
    return _compare_tex(repo, candidate, _production_reference())


def verify_tex(repo, candidate, event_file=None):
    from .ci_context import capture_context
    capture_context(repo, candidate, event_file=event_file)
    return compare_tex(repo, candidate)


def main(argv=None):
    return run_cli("release-export-integrity", argv, verify_tex)


if __name__ == "__main__":
    raise SystemExit(main())
