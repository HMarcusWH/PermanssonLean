"""C10 v0.1: supported six-state rational input -> original kernel-checked Lean replay.

This is deliberately NOT a generic arbitrary-model theorem certificate. The only
supported input is the existing typed C10 six-state witness and exact menu.
"""
from __future__ import annotations

import argparse
from contextlib import redirect_stderr
from hashlib import sha256
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Callable

ROOT = Path(__file__).resolve().parents[3]
RESEARCH = ROOT / 'verification' / 'research'
if str(RESEARCH) not in sys.path:
    sys.path.insert(0, str(RESEARCH))

from c10_exact_execution import InputError, check_input, execute, strict_object
from c10_golden import six_input
from c10_verify_receipt import ReceiptError, verify_receipt
from c10_emit_golden_bridge import emit_golden_bridge
from c10_release_evidence import axiom_reports

VERSION = 'Permansson.C10.ClosureSuccessor.v0.1.0'
MAX_INPUT_BYTES = 131072
COMPILER_TIMEOUT = 600
SUPPORTED_IDS = ('full', 'half', 'tiny', 'identity', 'u-only', 'b-only')
ERROR_CODES = {
    'INPUT_UNREADABLE', 'INPUT_TOO_LARGE', 'INPUT_NOT_JSON',
    'INPUT_UNSUPPORTED', 'NUMERIC_REPLAY_FAILED', 'SOURCE_UNVERIFIED',
    'LEAN_UNAVAILABLE', 'LEAN_COMPILATION_FAILED', 'LEAN_AXIOM_REJECTED',
    'INTERNAL_REPLAY_ERROR',
}


class AppFailure(Exception):
    def __init__(self, code: str, message: str) -> None:
        assert code in ERROR_CODES
        super().__init__(message)
        self.code = code


def strict_input(path: Path) -> dict:
    try:
        size = path.stat().st_size
    except OSError as e:
        raise AppFailure('INPUT_UNREADABLE', str(e)) from e
    if size > MAX_INPUT_BYTES:
        raise AppFailure('INPUT_TOO_LARGE', f'{size} bytes exceeds limit')
    try:
        raw = path.read_bytes()
        if raw.startswith(b'\xef\xbb\xbf'):
            raise UnicodeError('unexpected BOM')
        value = json.loads(raw.decode('utf-8'), object_pairs_hook=strict_object,
                           parse_float=lambda text: (_ for _ in ()).throw(InputError('floating JSON number')),
                           parse_constant=lambda text: (_ for _ in ()).throw(InputError('nonfinite number')))
    except (OSError, UnicodeError, json.JSONDecodeError, InputError) as e:
        raise AppFailure('INPUT_NOT_JSON', str(e)) from e
    if not isinstance(value, dict):
        raise AppFailure('INPUT_UNSUPPORTED', 'root must be an input object')
    return value


def supported_input(raw: dict) -> dict:
    """Validate both the general rational syntax and actual six-state typed identity."""
    try:
        parsed = check_input(raw)
        actual = parsed.canonical()
        frozen = check_input(six_input()).canonical()
    except (InputError, ValueError, TypeError, KeyError) as e:
        raise AppFailure('INPUT_UNSUPPORTED', str(e)) from e
    if actual != frozen or tuple(x['id'] for x in actual['menu']) != SUPPORTED_IDS:
        raise AppFailure('INPUT_UNSUPPORTED',
                         'no original typed-model/PR certificate for these supplied rows or menu')
    return actual


def exact_replay(raw: dict) -> tuple[dict, str]:
    supported_input(raw)
    try:
        receipt = execute(check_input(raw))
        if not verify_receipt(receipt):
            raise AppFailure('NUMERIC_REPLAY_FAILED', 'independent numeric checker did not pass')
        source = emit_golden_bridge(receipt)
    except AppFailure:
        raise
    except (ReceiptError, InputError, ValueError, ArithmeticError, AssertionError) as e:
        raise AppFailure('NUMERIC_REPLAY_FAILED', str(e)) from e
    # This asserts exactly the original (typed, constructed) six-state model.
    if receipt['selected'] != 'full' or receipt['optimum'] != '1':
        raise AppFailure('NUMERIC_REPLAY_FAILED', 'unexpected frozen six-state optimum')
    return receipt, source


def source_identity(root: Path) -> dict[str, str]:
    """Require the genuine clean repository HEAD and immutable existing providers."""
    def git(*args: str) -> str:
        try:
            p = subprocess.run(['git', *args], cwd=root, capture_output=True,
                               timeout=20, check=False)
        except (FileNotFoundError, subprocess.TimeoutExpired) as e:
            raise AppFailure('SOURCE_UNVERIFIED', 'git unavailable for source binding') from e
        if p.returncode:
            raise AppFailure('SOURCE_UNVERIFIED', 'cannot inspect source: '+p.stderr.decode('utf-8','replace')[-300:])
        return p.stdout.decode('utf-8').strip()
    if Path(git('rev-parse', '--show-toplevel')).resolve() != root.resolve():
        raise AppFailure('SOURCE_UNVERIFIED', 'source directory is not checked-out repository root')
    h = git('rev-parse','HEAD')
    if not re.fullmatch('[0-9a-f]{40}',h):
        raise AppFailure('SOURCE_UNVERIFIED','invalid HEAD')
    if git('status', '--porcelain=v1', '--untracked-files=all'):
        raise AppFailure('SOURCE_UNVERIFIED','repository source is modified or untracked')
    # Pinned interface identity before replay: binds typed-bridge theorem to
    # the reviewed canonical six-state witness, not arbitrary similar inputs.
    immutable = {
        'PermanssonResearch/ReverseSolver/C10SixStateBridge.lean':
            'f2ed30ab9033c987e8bdcadc1e4186ac102a2c4f',
        'PermanssonResearch/ReverseSolver/ExactSixStateC10Execution.lean':
            'd36ea99f1030f408dca3bb13dd8ded40ba14750f',
        'docs/PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md':
            '242af08011bb103c1672897bc4304bd184bfea4f',
    }
    providers = {}
    for path,expected in immutable.items():
        blob=git('rev-parse','HEAD:'+path)
        if expected and blob != expected:
            raise AppFailure('SOURCE_UNVERIFIED', 'canonical supported provider changed: '+path)
        providers[path]=blob
    return {'git_head':h,'git_tree':git('rev-parse','HEAD^{tree}'),
            'provider_blobs':providers}


def run_compiler(source: str, *, out_dir: Path,
                 command: tuple[str,...]=('lake','env','lean'),
                 timeout: int=COMPILER_TIMEOUT,
                 runner: Callable[..., subprocess.CompletedProcess] = subprocess.run) -> dict:
    """Run real pinned Lean kernel and inspect declared transitive axioms."""
    file=out_dir / 'C10ReifiedGolden.lean'
    file.write_text(source, encoding='utf-8', newline='\n')
    # Compile in the actual repository environment; never embed shell commands.
    try:
        r=runner([*command,str(file.resolve())],cwd=ROOT,
                 capture_output=True,text=True,encoding='utf-8',timeout=timeout,check=False)
    except (FileNotFoundError,subprocess.TimeoutExpired,OSError) as e:
        raise AppFailure('LEAN_UNAVAILABLE',str(e)) from e
    (out_dir / 'lean.stdout.txt').write_text(r.stdout,encoding='utf-8')
    (out_dir / 'lean.stderr.txt').write_text(r.stderr,encoding='utf-8')
    if r.returncode!=0 or re.search(r'\berror:|declaration uses .sorry.',r.stdout+r.stderr,re.I):
        raise AppFailure('LEAN_COMPILATION_FAILED', f'Lean exit={r.returncode}: '+(r.stdout+r.stderr)[-1400:])
    try:
        axioms=axiom_reports(r.stdout)
    except Exception as e:
        raise AppFailure('LEAN_AXIOM_REJECTED',str(e)) from e
    return {'lean_status':'KERNEL_CHECKED','axioms':axioms,
            'lean_stdout_sha256':sha256(r.stdout.encode()).hexdigest(),
            'lean_stderr_sha256':sha256(r.stderr.encode()).hexdigest()}


def report_for(raw: dict, *, mode: str, out_dir: Path,
               allow_proof: bool = True) -> dict:
    receipt, source = exact_replay(raw)
    input_digest=sha256(json.dumps(check_input(raw).canonical(),sort_keys=True,
                                   separators=(',',':')).encode('utf-8')).hexdigest()
    result = {'format':VERSION, 'mode':mode, 'supported_profile':'D0.C10.FROZEN_SIX_STATE',
              'input_sha256':input_digest, 'complete_comparison':[1,2],
              'numeric_status':'VERIFIED_EXACT_RATIONAL',
              'numeric_optimum':receipt['optimum'], 'numeric_selected':receipt['selected'],
              'lean_status':'NOT_RUN', 'scientific_claims_verified':False,
              'empirical_identification':'NOT_IDENTIFIED',
              'exact_GR_scope':'CONSTRUCTED_SIX_STATE_WITNESS_ONLY',
              'lean_source_sha256':sha256(source.encode()).hexdigest()}
    if mode=='replay':
        if not allow_proof:
            raise AppFailure('LEAN_UNAVAILABLE','real compiler gate disabled')
        result['source']=source_identity(ROOT)
        result.update(run_compiler(source,out_dir=out_dir))
    return result


def run_cli(argv: list[str]|None=None) -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,help='C10 six-state exact rational input JSON')
    parser.add_argument('--output',type=Path,required=True,help='fresh output directory, outside repository')
    parser.add_argument('--mode',choices=['numeric','replay'],default='replay')
    args=parser.parse_args(argv)
    # Print one machine-readable status on stdout. Errors also fail the exit code.
    try:
        out=args.output.resolve()
        # Protect the source checkout (including the frozen original app), even for numeric mode.
        if out == ROOT or ROOT in out.parents:
            raise AppFailure('SOURCE_UNVERIFIED','output must be outside source repository')
        if out.exists() and (not out.is_dir() or any(out.iterdir())):
            raise AppFailure('SOURCE_UNVERIFIED','output directory must be fresh/empty')
        out.mkdir(parents=True,exist_ok=True)
        raw=strict_input(args.input)
        report=report_for(raw,mode=args.mode,out_dir=out)
        (out/'numeric_receipt.json').write_text(json.dumps(execute(check_input(raw)),sort_keys=True,indent=2)+'\n',encoding='utf-8')
        (out/'result.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({'ok':True,'result_file':str(out/'result.json'),
                          'lean_status':report['lean_status'],
                          'scientific_claims_verified':False},sort_keys=True))
        return 0
    except AppFailure as e:
        print(json.dumps({'ok':False,'error_code':e.code,'message':str(e),
                          'lean_status':'NOT_CERTIFIED','scientific_claims_verified':False},sort_keys=True))
        return 2
    except Exception as e:
        print(json.dumps({'ok':False,'error_code':'INTERNAL_REPLAY_ERROR','message':str(e),
                          'lean_status':'NOT_CERTIFIED','scientific_claims_verified':False},sort_keys=True))
        return 2


if __name__=='__main__':
    raise SystemExit(run_cli())
