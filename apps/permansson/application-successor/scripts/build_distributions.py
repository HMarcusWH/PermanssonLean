#!/usr/bin/env python3
"""Build the wheel and sdist reproducibly with the locked build tools.

    python scripts/build_distributions.py --output DIR [--python PATH] [--epoch N]

`--python` is an interpreter with `requirements-build.lock` installed
(`pip install --require-hashes -r requirements-build.lock`). The builder
refuses to run unless every package in that lock is installed there at its
locked version. It then runs the locked `build` frontend without isolation
on a copy of the application, so the checkout gains no build products. Every
timestamp is fixed to SOURCE_DATE_EPOCH, which defaults to the commit time,
and the sdist archive is normalized. The same commit therefore gives
byte-identical artifacts.

DIR/distributions.json records both SHA-256 digests with the source commit
and tree. In a Git checkout the application must be clean (no modified or
untracked files), so the digests belong to that commit. The record is
self-produced: it signs, publishes and authorizes nothing (audit PKG-02).
"""
from __future__ import annotations
import argparse
import gzip
from hashlib import sha256
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

APP = Path(__file__).resolve().parents[1]
BUILD_LOCK = APP / 'requirements-build.lock'
FORMAT = 'Permansson.App.ReproducibleDistributions.v1'


class BuildError(Exception):
    pass


def locked_versions(lock_text: str) -> dict[str, str]:
    pins = dict(re.findall(r'^([A-Za-z0-9_.-]+)==([^\s\\]+)', lock_text, re.M))
    if 'setuptools' not in pins or 'build' not in pins:
        raise BuildError('requirements-build.lock must pin both setuptools and build')
    return pins


def check_tools(installed: dict[str, str | None], lock_text: str) -> dict[str, str]:
    """Every locked build package must be installed at exactly its locked version."""
    pins = locked_versions(lock_text)
    wrong = {name: installed.get(name) for name, version in pins.items() if installed.get(name) != version}
    if wrong:
        raise BuildError(f'build tools differ from requirements-build.lock: {wrong} (locked {pins}); '
                         'install it with --require-hashes')
    return pins


def _git(args: list[str], cwd: Path) -> str:
    return subprocess.run(['git', *args], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


def source_identity(app: Path) -> dict | None:
    """Commit, trees and cleanliness of the application, or None outside Git."""
    try:
        top = Path(_git(['rev-parse', '--show-toplevel'], app))
    except (OSError, subprocess.CalledProcessError):
        return None
    relative = app.resolve().relative_to(top.resolve()).as_posix()
    return {'commit': _git(['rev-parse', 'HEAD'], top),
            'tree': _git(['rev-parse', 'HEAD^{tree}'], top),
            'application_tree': _git(['rev-parse', f'HEAD:{relative}'], top),
            'commit_time': int(_git(['log', '-1', '--format=%ct', 'HEAD'], top)),
            'clean': _git(['status', '--porcelain', '--untracked-files=all', '--', relative], top) == ''}


def normalize_sdist(raw: Path, out: Path, epoch: int) -> None:
    """Same members and bytes; fixed order, timestamps and ownership; no gzip name or time."""
    with tarfile.open(raw) as source:
        members = [(m, source.extractfile(m).read() if m.isfile() else None) for m in source.getmembers()]
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode='w', format=tarfile.PAX_FORMAT) as target:
        for member, data in sorted(members, key=lambda item: item[0].name):
            member.mtime, member.uid, member.gid, member.uname, member.gname = epoch, 0, 0, '', ''
            member.pax_headers = {}
            target.addfile(member, io.BytesIO(data) if data is not None else None)
    with open(out, 'wb') as handle, gzip.GzipFile(filename='', mode='wb', fileobj=handle, mtime=epoch) as packed:
        packed.write(buffer.getvalue())


def _ignore(_directory, names):
    return [n for n in names if n in ('build', 'dist', '__pycache__') or n.endswith('.egg-info')]


def _digest(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def build(output: Path, python: str, epoch: int | None = None, *, require_clean: bool = True) -> dict:
    if output.exists():
        raise BuildError(f'{output} exists; choose a new output directory')
    source = source_identity(APP)
    if source is not None and require_clean and not source['clean']:
        raise BuildError('the application has modified or untracked files; commit them first')
    if epoch is None:
        if source is None:
            raise BuildError('outside a Git checkout pass --epoch explicitly')
        epoch = source['commit_time']
    probe = subprocess.run([python, '-I', '-c', 'import json, sys\nfrom importlib.metadata import version\n'
                            'names = json.loads(sys.argv[1]); out = {}\nfor n in names:\n'
                            '    try: out[n] = version(n)\n    except Exception: out[n] = None\n'
                            'print(json.dumps(out))', json.dumps(sorted(locked_versions(BUILD_LOCK.read_text())))],
                           capture_output=True, text=True, timeout=120)
    if probe.returncode != 0:
        raise BuildError(f'cannot query build tools in {python}: {probe.stderr[-300:]}')
    pins = check_tools(json.loads(probe.stdout), BUILD_LOCK.read_text())
    env = {k: v for k, v in os.environ.items() if k not in ('PYTHONPATH', 'PYTHONHOME')}
    env['SOURCE_DATE_EPOCH'] = str(epoch)
    with tempfile.TemporaryDirectory(prefix='permansson-dist-') as work:
        work = Path(work)
        copy = work / 'source'
        shutil.copytree(APP, copy, ignore=_ignore)
        raw = work / 'raw'
        # Default `build`: the sdist first, then the wheel built from that sdist.
        proc = subprocess.run([python, '-I', '-m', 'build', '--no-isolation', '--outdir', str(raw), str(copy)],
                              cwd=work, env=env, capture_output=True, text=True, timeout=900)
        if proc.returncode != 0:
            raise BuildError(f'build failed: {(proc.stderr or proc.stdout)[-1500:]}')
        wheels, sdists = sorted(raw.glob('*.whl')), sorted(raw.glob('*.tar.gz'))
        if (len(wheels), len(sdists)) != (1, 1):
            raise BuildError(f'expected one wheel and one sdist, got {[p.name for p in raw.iterdir()]}')
        output.mkdir(parents=True)
        wheel = output / wheels[0].name
        shutil.copyfile(wheels[0], wheel)
        sdist = output / sdists[0].name
        normalize_sdist(sdists[0], sdist, epoch)
    record = {'format': FORMAT, 'source': source, 'source_date_epoch': epoch,
              'build_tools': pins, 'python': subprocess.run(
                  [python, '-I', '-c', 'import platform; print(platform.python_version())'],
                  capture_output=True, text=True, timeout=60).stdout.strip(),
              'wheel': {'name': wheel.name, 'sha256': _digest(wheel)},
              'sdist': {'name': sdist.name, 'sha256': _digest(sdist)},
              'evidence_status': 'LOCAL_SELF_PRODUCED_NOT_AUTHENTICATED'}
    (output / 'distributions.json').write_text(json.dumps(record, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    return record


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--output', type=Path, required=True, help='new directory for the artifacts')
    parser.add_argument('--python', default=sys.executable, help='interpreter with requirements-build.lock installed')
    parser.add_argument('--epoch', type=int, help='SOURCE_DATE_EPOCH (default: the commit time)')
    args = parser.parse_args(argv)
    try:
        record = build(args.output, args.python, args.epoch)
    except BuildError as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}), file=sys.stderr)
        return 2
    print(json.dumps(record, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
