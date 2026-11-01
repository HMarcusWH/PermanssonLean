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

The public command never runs as the child. The parent starts the child
through a separate internal entry point (`permansson_app._budget_child`) and
hands it its staging path and limits. The environment alone can never switch
the public command into child mode, so a caller cannot skip the parent's
limits by setting internal variables. The child also applies the CPU,
address-space, file-size and wall-clock limits to itself, so even a direct
invocation of the internal entry point stays within them.

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
# Internal: the staging path and limits the parent hands its child. Read only
# by the internal child entry point, never by the public command.
CHILD_CONFIG_ENV = 'PERMANSSON_BUDGET_CHILD'
CHILD_MODULE = 'permansson_app._budget_child'
STAGING_PREFIX = 'permansson-run-'
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


def _limits(values: object, source: str, *, partial: bool) -> Limits:
    names = {f.name for f in fields(Limits)}
    if type(values) is not dict or not (set(values) <= names if partial else set(values) == names):
        raise AppError('BUDGET_INPUT', f'{source} may only name {sorted(names)}')
    for name, value in values.items():
        if type(value) is not int or not 1 <= value <= getattr(DEFAULT, name):
            raise AppError('BUDGET_INPUT', f'{name} must be an integer between 1 and the default {getattr(DEFAULT, name)}')
    return Limits(**{**DEFAULT.__dict__, **values})


def limits_from_env(env=None) -> Limits:
    raw = (os.environ if env is None else env).get(ENV_LIMITS)
    if raw is None:
        return DEFAULT
    try:
        values = json.loads(raw)
    except ValueError as exc:
        raise AppError('BUDGET_INPUT', f'{ENV_LIMITS} must be a JSON object') from exc
    return _limits(values, ENV_LIMITS, partial=True)


# Set only by `enter_child`, which only the internal child entry point calls.
_child_output: Path | None = None
_child_limits: Limits | None = None
_child_written = 0


def in_child() -> bool:
    """True only inside the internal child entry point; never derived from the environment."""
    return _child_output is not None


def child_output() -> Path:
    if _child_output is None:
        raise AppError('BUDGET_INTERNAL', 'not running as a budgeted child')
    return _child_output


def child_config(raw: str | None) -> tuple[Path, Limits]:
    """Validate the configuration the parent handed the child.

    The staging directory must be one the parent could have issued: a private
    (mode 0700) directory owned by this user, named with the staging prefix,
    not a symlink, and the output inside it must not exist yet.
    """
    import stat
    if raw is None:
        raise AppError('BUDGET_CHILD', 'the internal child entry point is started only by the budgeted parent')
    try:
        value = json.loads(raw)
    except ValueError as exc:
        raise AppError('BUDGET_CHILD', 'malformed child configuration') from exc
    if type(value) is not dict or set(value) != {'output', 'limits'} or type(value['output']) is not str:
        raise AppError('BUDGET_CHILD', 'malformed child configuration')
    limits = _limits(value['limits'], 'child limits', partial=False)
    out = Path(value['output'])
    if not out.is_absolute() or out.name != 'out' or not out.parent.name.startswith(STAGING_PREFIX):
        raise AppError('BUDGET_CHILD', 'child output is not an issued staging path')
    try:
        info = os.lstat(out.parent)
    except OSError as exc:
        raise AppError('BUDGET_CHILD', 'staging directory is missing') from exc
    if (not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) != 0o700
            or os.path.lexists(out)):
        raise AppError('BUDGET_CHILD', 'staging directory is not private, or its output already exists')
    return out, limits


def _address_space_in_use() -> int:
    with open('/proc/self/status', encoding='ascii') as status:
        for line in status:
            if line.startswith('VmSize:'):
                return int(line.split()[1]) * 1024
    raise AppError('PLATFORM_UNQUALIFIED', 'cannot read the address space in use')


def charge_output(size: int) -> None:
    """In the child, count bytes written; the total may not exceed the output budget."""
    global _child_written
    if _child_limits is not None:
        _child_written += size
        if _child_written > _child_limits.output_bytes:
            raise OSError(errno.EFBIG, 'whole-run output budget exhausted')


def _lower(resource_id: int, soft: int, hard: int) -> None:
    """Lower a resource limit; never raise one that is already tighter."""
    import resource
    cur_soft, cur_hard = resource.getrlimit(resource_id)
    new_hard = hard if cur_hard == resource.RLIM_INFINITY else min(cur_hard, hard)
    new_soft = min(soft, new_hard) if cur_soft == resource.RLIM_INFINITY else min(cur_soft, soft, new_hard)
    resource.setrlimit(resource_id, (new_soft, new_hard))


def enter_child(output: Path, limits: Limits) -> None:
    """In the budgeted child, before the request is read: apply every limit to this process.

    The code (including the schema validator's native extension) is loaded
    first under the parent's address-space ceiling; then RLIMIT_AS is lowered
    to the configured value. CPU, file size, core dumps and a wall-clock timer
    are applied here as well, so the limits hold even without the parent.

    RLIMIT_AS stops new mappings; it does not shrink what is already mapped.
    A memory budget at or below the loaded program's own address space (about
    30 MiB) therefore cannot be honoured and is refused as exhausted here,
    before the request is read.
    """
    global _child_output, _child_limits, _child_written
    import resource
    try:
        import jsonschema  # noqa: F401
        import referencing  # noqa: F401
    except ImportError:
        pass
    _lower(resource.RLIMIT_CPU, limits.cpu_seconds, limits.cpu_seconds + 1)
    _lower(resource.RLIMIT_FSIZE, limits.output_bytes, limits.output_bytes)
    _lower(resource.RLIMIT_CORE, 0, 0)
    remaining = signal.getitimer(signal.ITIMER_REAL)[0]
    signal.setitimer(signal.ITIMER_REAL, limits.wall_seconds if remaining == 0 else min(remaining, limits.wall_seconds))
    in_use = _address_space_in_use()
    if in_use >= limits.memory_bytes:
        raise MemoryError(f'memory budget of {limits.memory_bytes} bytes is below the loaded program '
                          f'({in_use} bytes)')
    _lower(resource.RLIMIT_AS, limits.memory_bytes, limits.memory_bytes)
    _child_output, _child_limits, _child_written = output, limits, 0


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
    if code == -signal.SIGALRM:
        # The child's own wall-clock timer fired before the parent's.
        raise AppError('BUDGET_TIMEOUT', f'whole-run wall-clock budget of {limits.wall_seconds} s exhausted')
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
    staging = Path(tempfile.mkdtemp(prefix=STAGING_PREFIX)).absolute()  # mode 0700
    try:
        child_out = staging / 'out'
        config = json.dumps({'output': str(child_out),
                             'limits': {f.name: getattr(limits, f.name) for f in fields(Limits)}})
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', **{CHILD_CONFIG_ENV: config})
        env['PYTHONPATH'] = os.pathsep.join(p for p in (package_root, env.get('PYTHONPATH', '')) if p)
        code, stdout, stderr = run_child([sys.executable, '-m', CHILD_MODULE, *argv], env, limits,
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
