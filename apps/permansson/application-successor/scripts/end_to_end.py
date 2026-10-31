"""End-to-end walkthrough of every packaged example, as a third party would run it.

For each registered profile this runs the real `permansson-app` command on the
packaged example, requires its independent check to pass, then (for profiles
with a Lean family) emits the source-bound Lean candidate, rechecks its bytes,
confirms that a tampered copy is rejected and, with `--lean`, compiles the
candidate with the repository's pinned toolchain and audits every theorem's
axioms (only `propext`, `Classical.choice`, `Quot.sound`). Examples beyond a
family's reflection bound are reported as numeric-only, never as failures.

    python scripts/end_to_end.py                       # source tree, no Lean
    python scripts/end_to_end.py --lean                # also compile every candidate
    python scripts/end_to_end.py --app /venv/bin/permansson-app --lean   # installed wheel
    python scripts/end_to_end.py --only finite-private-stage --lean       # selected profiles

Each profile must report its own expected success pair exactly: the CLI's
status field and the independent checker's `status`. The CLI's self-report
never substitutes for the checker, and an unexpected, missing or malformed
status fails the walkthrough. `--lean` audits axioms with the Research
replay harness's reviewed parser (exactly one target-qualified record per
theorem, no extra records, no `error:` or `sorryAx`) and runs the compiler
in its own process group, killed as a whole on timeout.

The walkthrough exits non-zero on any failure and writes a JSON summary with
`--report`. It is a reproducibility aid, not a certification: application
outputs keep `lean_status=NOT_EXECUTED` whatever it prints.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

APP = Path(__file__).resolve().parents[1]
EXAMPLES = APP / 'src/permansson_app/data/examples'

# (command, input files, receipt written by the command, Lean family, (CLI status field, value), checker status)
PROFILES = [
    ('finite-kernel', ['finite_world.v1.model.json'], None, 'finite-world',
     ('numeric_status', 'EXACT_RATIONAL_VERIFIED'), 'PASS'),
    ('finite-survival', ['finite_survival.v1.json'], 'finite_survival_receipt.json', 'survival',
     ('numeric_status', 'FINITE_SURVIVAL_TABLE_VERIFIED'), 'FINITE_SURVIVAL_TABLE_VERIFIED'),
    ('finite-occupation', ['finite_world.v1.model.json'], 'occupation_receipt.json', 'occupation',
     ('numeric_status', 'EXACT_RATIONAL_VERIFIED'), 'PASS'),
    ('finite-exit', ['finite_world.v1.model.json', 'finite_region.v1.json'], 'exit_receipt.json', 'exit',
     ('numeric_status', 'EXACT_RATIONAL_VERIFIED'), 'PASS'),
    ('frozen-menu', ['finite_menu.v1.json'], 'menu_receipt.json', 'menu',
     ('numeric_status', 'FROZEN_MENU_OPTIMUM_VERIFIED'), 'FROZEN_MENU_OPTIMUM_VERIFIED'),
    ('finite-bellman', ['control_hitting.v1.json'], 'bellman_receipt.json', 'control-table',
     ('numeric_status', 'EXACT_FINITE_BELLMAN_CHECKED'), 'PASS'),
    ('finite-safety', ['finite_safety.v1.json'], 'safety_core_receipt.json', 'safety-core',
     ('numeric_status', 'EXACT_ALMOST_SURE_SAFETY_CORE_VERIFIED'), 'PASS'),
    ('finite-perturbation', ['finite_perturbation.v1.json'], 'perturbation_receipt.json', 'perturbation',
     ('numeric_status', 'FINITE_PATH_TV_BOUND_VERIFIED'), 'PASS'),
    ('finite-residence', ['residence.v1.json'], 'residence_receipt.json', 'residence', ('numeric_status', 'PASS'), 'PASS'),
    ('nonlinear-stationary', ['nonlinear.v1.json'], 'nonlinear_receipt.json', 'nonlinear', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-grammar', ['grammar.v1.json'], 'grammar_receipt.json', 'grammar', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-adaptive-grammar', ['adaptive.v1.json'], 'adaptive_receipt.json', 'adaptive', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-quotient', ['quotient.v1.json'], 'quotient_receipt.json', 'quotient', ('numeric_status', 'PASS'), 'PASS'),
    ('one-step-risk', ['risk_occupancy.v1.json'], 'occupancy_receipt.json', 'flow', ('numeric_status', 'PASS'), 'PASS'),
    ('one-step-risk-infeasibility', ['risk_infeasibility.v1.json'], 'infeasibility_receipt.json', 'risk-infeasibility',
     ('numeric_status', 'INFEASIBILITY_VERIFIED'), 'INFEASIBILITY_VERIFIED'),
    ('finite-robust-nature', ['robust_nature.v1.json'], 'nature_receipt.json', 'robust-nature', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-private-stage', ['private_stage.v1.json'], 'private_stage_receipt.json', 'private-stage',
     ('numeric_status', 'PASS'), 'PASS'),
    ('one-step-belief', ['belief.v1.json'], 'belief_receipt.json', 'belief', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-belief-tree', ['belief_tree.v1.json'], 'belief_tree_receipt.json', 'belief', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-cq1', ['cq1.v1.json'], 'cq1_receipt.json', 'cq1', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-cq1-transport', ['cq1_transport.v1.json'], 'cq1_transport_receipt.json', 'cq1-transport',
     ('numeric_status', 'PASS'), 'PASS'),
    ('finite-metric', ['metric.v1.json'], 'metric_receipt.json', 'metric', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-algebra', ['algebra.v1.json'], 'algebra_receipt.json', 'algebra', ('numeric_status', 'PASS'), 'PASS'),
    ('finite-multiagent', ['multiagent.v1.json'], 'multiagent_receipt.json', 'multiagent', ('numeric_status', 'PASS'), 'PASS'),
    ('lp-propose', ['lp.v1.model.json'], 'proposal.json', 'lp', ('status', 'CHECKED_OPTIMAL_CANDIDATE'), 'OPTIMAL_VERIFIED'),
]
NATIVE = [('c10.request.json', 'c10.fixed_six_state.numeric.v1'),
          ('c11.periodic.request.json', 'c11.stationary_1_to_6.numeric.v1'),
          ('c11.multiclass.request.json', 'c11.stationary_1_to_6.numeric.v1')]


class Failure(Exception):
    pass


def find_repository(start: Path = APP) -> Path | None:
    """The enclosing PermanssonLean checkout (pinned toolchain and Lean roots), if any."""
    for candidate in (start, *start.parents):
        if (candidate / 'lean-toolchain').is_file() and (candidate / 'PermanssonResearch.lean').is_file():
            return candidate
    return None


def _app_command(app: str | None) -> tuple[list[str], dict]:
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    if app:
        return [app], env
    env['PYTHONPATH'] = str(APP / 'src')
    return [sys.executable, '-B', '-m', 'permansson_app'], env


def _run(cmd: list[str], env: dict, cwd: Path, timeout: int = 900) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)


def _json_out(proc: subprocess.CompletedProcess, label: str) -> dict:
    if proc.returncode != 0:
        raise Failure(f'{label}: exit {proc.returncode}: {(proc.stderr or proc.stdout)[-400:]}')
    return json.loads(proc.stdout)


def _harness(repo: Path):
    """The Research replay harness of this checkout: its reviewed axiom parser and bounded runner."""
    research = str(repo / 'verification/research')
    if research not in sys.path:
        sys.path.insert(0, research)
    import application_bridge_replay
    return application_bridge_replay


def audit_log(repo: Path, log: str, names: list[str]) -> int:
    """Exactly one target-qualified, standard-axiom record per theorem and nothing else."""
    try:
        return len(_harness(repo).audited_axioms(log, names))
    except AssertionError as exc:
        raise Failure(f'axiom audit: {exc}') from exc


def run_bounded(repo: Path, command: list[str], cwd: Path, timeout: int) -> tuple[int, str]:
    """Run in a new session; on timeout the whole process group is killed."""
    try:
        return _harness(repo).run_bounded(command, cwd, timeout)
    except AssertionError as exc:
        raise Failure(str(exc)) from exc


def _lean(candidate: Path, names: list[str], repo: Path, timeout: int = 1800) -> dict:
    lake = shutil.which('lake')
    if lake is None:
        raise Failure('--lean requested but `lake` is not on PATH (install the pinned toolchain)')
    source = next(candidate.glob('*.lean'))
    start = time.monotonic()
    code, log = run_bounded(repo, [lake, 'env', 'lean', str(source)], repo, timeout)
    if code != 0:
        raise Failure(f'lake env lean exited {code} for {source.name}: {log[-600:]}')
    return {'compiled': True, 'theorems_audited': audit_log(repo, log, names),
            'seconds': round(time.monotonic() - start, 1)}


def _expect(condition: bool, message: str):
    if not condition:
        raise Failure(message)


def check_numeric(command: str, result: dict, out: Path, cli_expected: tuple[str, str], checker_expected: str) -> str:
    """Fail closed: the CLI and the independent checker must each report this profile's exact success value."""
    field, value = cli_expected
    _expect(result.get('ok') is True, f'{command}: CLI did not report ok')
    _expect(result.get(field) == value, f'{command}: CLI {field} {result.get(field)!r}, expected {value!r}')
    _expect(result.get('lean_status', 'NOT_EXECUTED') == 'NOT_EXECUTED', f'{command}: CLI claims Lean execution')
    try:
        check = json.loads((out / 'independent_check.json').read_text(encoding='utf-8'))
    except (OSError, json.JSONDecodeError) as exc:
        raise Failure(f'{command}: unreadable independent check ({exc})') from exc
    _expect(type(check) is dict, f'{command}: independent check is not an object')
    status = check.get('status')
    _expect(type(status) is str and status == checker_expected,
            f'{command}: independent check status {status!r}, expected {checker_expected!r}')
    _expect(check.get('lean_status', 'NOT_EXECUTED') == 'NOT_EXECUTED', f'{command}: checker claims Lean execution')
    _expect(check.get('scientific_claims_verified', False) is False, f'{command}: checker claims scientific verification')
    report = json.loads((out / 'scientific_report.json').read_text(encoding='utf-8'))
    _expect(report.get('scientific_claims_verified') is False and report.get('kernel_checked_proof') == 'NOT_EXECUTED',
            f'{command}: report claims more than a numeric result')
    return status


def _profile(cmd, env, work, command, inputs, receipt_name, family, cli_expected, checker_expected, lean, repo):
    row = {'command': command, 'example': inputs[0], 'family': family}
    out = work / command
    paths = [str(EXAMPLES / name) for name in inputs]
    result = _json_out(_run(cmd + [command, *paths, '--output', str(out)], env, APP), command)
    row['numeric_status'] = check_numeric(command, result, out, cli_expected, checker_expected)
    request = paths[0]
    receipt_args = []
    if receipt_name is not None:
        receipt = out / receipt_name
        if command == 'lp-propose':
            proposal = json.loads(receipt.read_text())
            receipt = out / 'lp_receipt.json'
            receipt.write_text(json.dumps(proposal['receipt']))
            checked = _json_out(_run(cmd + ['lp-check', request, str(receipt), '--output', str(work / 'lp-check')],
                                     env, APP), 'lp-check')
            check_numeric('lp-check', checked, work / 'lp-check', ('status', 'OPTIMAL_VERIFIED'), 'OPTIMAL_VERIFIED')
        receipt_args = [str(receipt)]
    region_args = ['--region', paths[1]] if family == 'exit' else []
    candidate = work / f'{command}.lean-candidate'
    emitted = _run(cmd + ['lean-emit', '--family', family, request, *receipt_args, *region_args,
                          '--output', str(candidate)], env, APP)
    if emitted.returncode != 0:
        try:
            code = json.loads(emitted.stderr)['error']['code']
        except (json.JSONDecodeError, KeyError, TypeError) as exc:
            raise Failure(f'{command}: lean-emit failed without a structured error') from exc
        if code.endswith('_SCOPE'):
            row['lean'] = f'numeric only: outside the reflection bound ({code})'
            return row
        raise Failure(f'{command}: lean-emit {code}')
    rechecked = _json_out(_run(cmd + ['lean-recheck', '--family', family, request, *receipt_args, *region_args,
                                      '--candidate', str(candidate)], env, APP), f'{command} lean-recheck')
    _expect(rechecked.get('ok') is True and rechecked.get('family') == family, f'{command}: malformed lean-recheck reply')
    _expect(rechecked['result'].get('lean_status') == 'NOT_EXECUTED', f'{command}: recheck claims Lean execution')
    tampered = work / f'{command}.tampered'
    shutil.copytree(candidate, tampered)
    source = next(tampered.glob('*.lean'))
    source.write_text(source.read_text(encoding='utf-8') + '\n-- tampered\n', encoding='utf-8')
    if _run(cmd + ['lean-recheck', '--family', family, request, *receipt_args, *region_args,
                   '--candidate', str(tampered)], env, APP).returncode == 0:
        raise Failure(f'{command}: a tampered candidate passed lean-recheck')
    meta = json.loads((candidate / 'source_candidate.json').read_text())
    # The candidate's own `#print axioms` lines are the audited theorem list;
    # every theorem the metadata names must be among them.
    names = re.findall(r'^#print axioms (\S+)$', next(candidate.glob('*.lean')).read_text(encoding='utf-8'), re.M)
    if not names or not {n.rsplit('.', 1)[-1] for n in names} >= set(meta.get('theorem_names', [])):
        raise Failure(f'{command}: candidate does not audit every theorem its metadata names')
    row['lean'] = 'emitted, byte-rechecked, tamper rejected'
    if lean:
        row['lean'] += '; ' + json.dumps(_lean(candidate, names, repo), sort_keys=True)
    return row


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--app', help='installed permansson-app executable (default: run from the source tree)')
    parser.add_argument('--lean', action='store_true', help='compile every emitted candidate with the pinned toolchain')
    parser.add_argument('--report', type=Path, help='write a JSON summary here')
    parser.add_argument('--only', action='append', metavar='COMMAND',
                        help='run only these profile commands (repeatable); native runs are then skipped')
    parser.add_argument('--source-root', type=Path,
                        help='repository checkout for the native C10/C11 runs and Lean (default: the enclosing one)')
    args = parser.parse_args(argv)
    repo = args.source_root.resolve() if args.source_root else find_repository()
    if args.lean and repo is None:
        parser.error('--lean needs a repository checkout with the pinned toolchain (--source-root)')
    known = {row[0] for row in PROFILES}
    if args.only and not set(args.only) <= known:
        parser.error(f'unknown profile command(s): {sorted(set(args.only) - known)}')
    cmd, env = _app_command(args.app)
    rows, failures = [], []
    with tempfile.TemporaryDirectory(prefix='permansson-e2e-') as td:
        work = Path(td)
        for command, inputs, receipt, family, cli_expected, checker_expected in PROFILES:
            if args.only and command not in args.only:
                continue
            try:
                rows.append(_profile(cmd, env, work, command, inputs, receipt, family, cli_expected,
                                     checker_expected, args.lean, repo))
            except (Failure, subprocess.TimeoutExpired, json.JSONDecodeError, OSError, KeyError, TypeError) as exc:
                failures.append({'command': command, 'error': str(exc)})
            print(json.dumps(rows[-1] if not failures or failures[-1]['command'] != command else failures[-1],
                             ensure_ascii=False), flush=True)
        for request, capability in [] if args.only else NATIVE:
            if repo is None:
                rows.append({'command': 'run', 'example': request,
                             'numeric_status': 'skipped: no repository checkout (pass --source-root)'})
                print(json.dumps(rows[-1]), flush=True)
                continue
            try:
                result = _json_out(_run(cmd + ['run', str(EXAMPLES / request), '--source-root', str(repo),
                                               '--output', str(work / request)], env, APP), request)
                native = json.loads(Path(result['result_file']).read_text(encoding='utf-8'))
                _expect(result.get('ok') is True and result.get('numeric_status') == 'EXACT_RATIONAL_VERIFIED',
                        f'run {request}: CLI status {result.get("numeric_status")!r}')
                _expect(native.get('capability') == capability and native.get('lean_status') == 'NOT_EXECUTED'
                        and native.get('scientific_claims_verified') is False,
                        f'run {request}: application result capability/status mismatch')
                rows.append({'command': 'run', 'example': request, 'numeric_status': result['numeric_status']})
                print(json.dumps(rows[-1]), flush=True)
            except (Failure, subprocess.TimeoutExpired, json.JSONDecodeError, OSError, KeyError) as exc:
                failures.append({'command': f'run {request}', 'error': str(exc)})
                print(json.dumps(failures[-1]), flush=True)
    summary = {'format': 'Permansson.App.EndToEndWalkthrough.v1', 'app': args.app or 'source tree',
               'lean_compiled': args.lean, 'profiles': rows, 'failures': failures,
               'status': 'PASS' if not failures else 'FAIL',
               'note': 'reproducibility aid; application outputs keep lean_status=NOT_EXECUTED'}
    if args.report:
        args.report.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print(json.dumps({'status': summary['status'], 'profiles': len(rows), 'failures': len(failures)}))
    return 0 if not failures else 1


if __name__ == '__main__':
    raise SystemExit(main())
