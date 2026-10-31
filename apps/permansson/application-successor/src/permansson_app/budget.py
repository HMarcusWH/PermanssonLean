"""Whole-run budget for the exact additive profiles (PKG-04).

Each additive profile command runs in a child process under one cumulative
budget for the whole request: parsing, the computation, the independent check
and writing the outputs. The limits are:

- wall clock: the whole process group is killed on expiry;
- CPU seconds (RLIMIT_CPU);
- address space (RLIMIT_AS), which bounds intermediate constructions. The
  child starts under the default 2 GiB ceiling and lowers its own limit to the
  configured value once the interpreter and the application's code are loaded,
  before the request is read (`enter_child`). The limit is on total address
  space, so everything the request causes stays within it, while a lowered
  limit cannot make interpreter startup or code loading fail in ways that do
  not report as memory exhaustion;
- bytes per output file (RLIMIT_FSIZE) and in total;
- captured standard output and error.

The child writes into a private staging directory. Its files reach the
requested output directory only after the child finished within every limit.
An exhausted budget therefore never leaves a receipt or a partial output.

`PERMANSSON_RUN_BUDGET` may lower the limits (a JSON object with a subset of
the field names below) but never raise them. Linux is the only qualified
platform for this release; other platforms are refused.
"""
from __future__ import annotations

from dataclasses import dataclass, fields
import errno
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile

from .errors import AppError

ENV_LIMITS = 'PERMANSSON_RUN_BUDGET'
# Internal: set only for the budgeted child, naming its staging output directory.
CHILD_ENV = 'PERMANSSON_BUDGET_CHILD_OUTPUT'
# Internal: the address-space limit the budgeted child applies to itself.
CHILD_MEMORY_ENV = 'PERMANSSON_BUDGET_CHILD_MEMORY'
MEMORY_EXIT = 3
# CPython ignores SIGXFSZ, so an oversize write raises OSError(EFBIG) in the child.
OUTPUT_EXIT = 4
# How an exhausted address space shows up when it is not a Python MemoryError:
# the dynamic loader cannot map a shared library (before or during imports),
# or a system call fails with ENOMEM.
_MEMORY_TEXT = ('memoryerror', 'cannot allocate memory', 'failed to map segment from shared object',
                'out of memory')


def is_memory_failure(exc: BaseException) -> bool:
    """True if `exc`, or an exception it was raised from, reports exhausted memory."""
    seen = set()
    while exc is not None and id(exc) not in seen:
        seen.add(id(exc))
        if isinstance(exc, MemoryError) or (isinstance(exc, OSError) and exc.errno == errno.ENOMEM):
            return True
        if any(text in str(exc).lower() for text in _MEMORY_TEXT):
            return True
        exc = exc.__cause__ or exc.__context__
    return False


@dataclass(frozen=True)
class Limits:
    wall_seconds: int = 300
    cpu_seconds: int = 240
    memory_bytes: int = 2 * 1024 ** 3
    output_bytes: int = 32 * 1024 ** 2
    stream_bytes: int = 1024 ** 2

    def receipt(self) -> dict:
        return {'format': 'Permansson.App.WholeRunBudget.v1', **{f.name: getattr(self, f.name) for f in fields(self)}}


DEFAULT = Limits()


def limits_from_env(env=None) -> Limits:
    raw = (os.environ if env is None else env).get(ENV_LIMITS)
    if raw is None:
        return DEFAULT
    try:
        values = json.loads(raw)
    except ValueError as exc:
        raise AppError('BUDGET_INPUT', f'{ENV_LIMITS} must be a JSON object') from exc
    names = {f.name for f in fields(Limits)}
    if type(values) is not dict or not set(values) <= names:
        raise AppError('BUDGET_INPUT', f'{ENV_LIMITS} may only name {sorted(names)}')
    for name, value in values.items():
        if type(value) is not int or not 1 <= value <= getattr(DEFAULT, name):
            raise AppError('BUDGET_INPUT', f'{name} must be an integer between 1 and the default {getattr(DEFAULT, name)}')
    return Limits(**{**DEFAULT.__dict__, **values})


def in_child() -> bool:
    return bool(os.environ.get(CHILD_ENV))


def child_output() -> Path:
    return Path(os.environ[CHILD_ENV])


def enter_child() -> None:
    """In the budgeted child, before the request is read: load the code, then lower RLIMIT_AS."""
    import resource
    try:
        # The schema validator's native extension is program code, not request
        # work; load it under the ceiling. A missing extra is reported later.
        import jsonschema  # noqa: F401
        import referencing  # noqa: F401
    except ImportError:
        pass
    raw = os.environ.get(CHILD_MEMORY_ENV, '')
    if not raw.isdigit() or not 1 <= int(raw) <= DEFAULT.memory_bytes:
        raise AppError('BUDGET_INPUT', 'budgeted child started without a valid memory limit')
    resource.setrlimit(resource.RLIMIT_AS, (int(raw), int(raw)))


def _require_new(path: Path) -> Path:
    out = path.absolute()
    if out.exists() or out.is_symlink() or any(p.is_symlink() for p in (out.parent, *out.parent.parents)):
        raise AppError('OUTPUT_SCOPE', 'output must be new and must not pass through a symlink')
    return out


def _limit_child(limits: Limits, address_space: int):
    import resource

    def apply():
        os.setsid()
        resource.setrlimit(resource.RLIMIT_CPU, (limits.cpu_seconds, limits.cpu_seconds + 1))
        resource.setrlimit(resource.RLIMIT_AS, (address_space, address_space))
        resource.setrlimit(resource.RLIMIT_FSIZE, (limits.output_bytes, limits.output_bytes))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    return apply


def run_child(command: list[str], env: dict, limits: Limits, *,
              startup_address_space: int | None = None) -> tuple[int, bytes, bytes]:
    """Run under every limit; exhaustion raises a BUDGET_* AppError.

    With `startup_address_space`, the process starts under that RLIMIT_AS
    ceiling and is trusted to lower it to `limits.memory_bytes` itself before
    it does any request work (the budgeted CLI child does, in `enter_child`).
    """
    if sys.platform != 'linux':
        raise AppError('PLATFORM_UNQUALIFIED', 'the whole-run budget is qualified on Linux only for this release')
    address_space = limits.memory_bytes if startup_address_space is None else startup_address_space
    if not limits.memory_bytes <= address_space <= DEFAULT.memory_bytes:
        raise AppError('BUDGET_INPUT', 'startup address space must lie between the limit and the default')
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        process = subprocess.Popen(command, env=env, stdin=subprocess.DEVNULL, stdout=out, stderr=err,
                                   close_fds=True, preexec_fn=_limit_child(limits, address_space))
        try:
            process.wait(timeout=limits.wall_seconds)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            raise AppError('BUDGET_TIMEOUT', f'whole-run wall-clock budget of {limits.wall_seconds} s exhausted') from None
        sizes = out.seek(0, 2), err.seek(0, 2)
        if max(sizes) > limits.stream_bytes:
            raise AppError('BUDGET_STREAM', 'whole-run output stream budget exhausted')
        out.seek(0)
        err.seek(0)
        stdout, stderr = out.read(), err.read()
    code = process.returncode
    if code == -signal.SIGXCPU or code == -signal.SIGKILL:
        raise AppError('BUDGET_CPU', f'whole-run CPU budget of {limits.cpu_seconds} s exhausted')
    if code in (-signal.SIGXFSZ, OUTPUT_EXIT) or (code == 1 and b'File too large' in stderr):
        raise AppError('BUDGET_OUTPUT', f'whole-run output budget of {limits.output_bytes} bytes exhausted')
    if code == MEMORY_EXIT or (code not in (0, 2) and any(text in stderr.decode('utf-8', 'replace').lower()
                                                           for text in _MEMORY_TEXT)):
        # Also covers failures before the child's own handlers run: the loader
        # exits 127 when it cannot map a shared library, and an uncaught
        # ENOMEM ends the interpreter with status 1.
        raise AppError('BUDGET_MEMORY', f'whole-run memory budget of {limits.memory_bytes} bytes exhausted')
    if code in (-signal.SIGSEGV, -signal.SIGBUS, -signal.SIGABRT):
        # Under the address-space limit, native code (CPython internals, Rust
        # extensions) can crash or abort on a failed allocation instead of
        # raising MemoryError.
        raise AppError('BUDGET_MEMORY', f'whole-run memory budget of {limits.memory_bytes} bytes exhausted '
                                        f'(native code ended by signal {-code})')
    if code < 0:
        raise AppError('BUDGET_ABORTED', f'budgeted run ended by signal {-code}')
    return code, stdout, stderr


def run_budgeted(argv: list[str], output: Path | None, limits: Limits | None = None) -> int:
    """The parent side: run `permansson-app argv` in a limited child, then publish its outputs."""
    limits = limits_from_env() if limits is None else limits
    final = _require_new(output) if output is not None else None
    package_root = str(Path(__file__).resolve().parents[1])
    staging = Path(tempfile.mkdtemp(prefix='permansson-run-'))
    try:
        child_out = staging / 'out'
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1',
                   **{CHILD_ENV: str(child_out), CHILD_MEMORY_ENV: str(limits.memory_bytes)})
        env['PYTHONPATH'] = os.pathsep.join(p for p in (package_root, env.get('PYTHONPATH', '')) if p)
        code, stdout, stderr = run_child([sys.executable, '-m', 'permansson_app', *argv], env, limits,
                                         startup_address_space=DEFAULT.memory_bytes)
        if code != 0:
            if code == 2:
                sys.stderr.write(stderr.decode('utf-8', 'replace'))
                return 2
            raise AppError('APP_INTERNAL', 'budgeted run failed: ' + stderr.decode('utf-8', 'replace')[-500:])
        files = [p for p in child_out.rglob('*')] if child_out.exists() else []
        if sum(p.stat().st_size for p in files if p.is_file()) > limits.output_bytes:
            raise AppError('BUDGET_OUTPUT', f'whole-run output budget of {limits.output_bytes} bytes exhausted')
        lines = stdout.decode('utf-8').splitlines()
        result = json.loads(lines[0]) if len(lines) == 1 else None
        if type(result) is not dict or result.get('ok') is not True:
            raise AppError('APP_INTERNAL', 'budgeted run returned no single success record')
        if 'output' in result:
            if final is None or result['output'] != str(child_out) or not child_out.is_dir():
                raise AppError('APP_INTERNAL', 'budgeted run wrote outside its staging directory')
            final = _require_new(final)
            final.mkdir(parents=True)
            for item in sorted(child_out.iterdir()):
                shutil.move(str(item), str(final / item.name))
            result['output'] = str(final)
        print(json.dumps(result, sort_keys=True))
        return 0
    finally:
        shutil.rmtree(staging, ignore_errors=True)
