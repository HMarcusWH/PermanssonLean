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
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

# (command, input files, receipt written by the command, Lean family or None, region-family input)
PROFILES = [
    ('finite-kernel', ['finite_world.v1.model.json'], None, 'finite-world'),
    ('finite-survival', ['finite_survival.v1.json'], 'finite_survival_receipt.json', 'survival'),
    ('finite-occupation', ['finite_world.v1.model.json'], 'occupation_receipt.json', 'occupation'),
    ('finite-exit', ['finite_world.v1.model.json', 'finite_region.v1.json'], 'exit_receipt.json', 'exit'),
    ('frozen-menu', ['finite_menu.v1.json'], 'menu_receipt.json', 'menu'),
    ('finite-bellman', ['control_hitting.v1.json'], 'bellman_receipt.json', 'control-table'),
    ('finite-safety', ['finite_safety.v1.json'], 'safety_core_receipt.json', 'safety-core'),
    ('finite-perturbation', ['finite_perturbation.v1.json'], 'perturbation_receipt.json', 'perturbation'),
    ('finite-residence', ['residence.v1.json'], 'residence_receipt.json', 'residence'),
    ('nonlinear-stationary', ['nonlinear.v1.json'], 'nonlinear_receipt.json', 'nonlinear'),
    ('finite-grammar', ['grammar.v1.json'], 'grammar_receipt.json', 'grammar'),
    ('finite-adaptive-grammar', ['adaptive.v1.json'], 'adaptive_receipt.json', 'adaptive'),
    ('finite-quotient', ['quotient.v1.json'], 'quotient_receipt.json', 'quotient'),
    ('one-step-risk', ['risk_occupancy.v1.json'], 'occupancy_receipt.json', 'flow'),
    ('one-step-risk-infeasibility', ['risk_infeasibility.v1.json'], 'infeasibility_receipt.json', 'risk-infeasibility'),
    ('finite-robust-nature', ['robust_nature.v1.json'], 'nature_receipt.json', 'robust-nature'),
    ('finite-private-stage', ['private_stage.v1.json'], 'private_stage_receipt.json', 'private-stage'),
    ('one-step-belief', ['belief.v1.json'], 'belief_receipt.json', 'belief'),
    ('finite-belief-tree', ['belief_tree.v1.json'], 'belief_tree_receipt.json', 'belief'),
    ('finite-cq1', ['cq1.v1.json'], 'cq1_receipt.json', 'cq1'),
    ('finite-cq1-transport', ['cq1_transport.v1.json'], 'cq1_transport_receipt.json', 'cq1-transport'),
    ('finite-metric', ['metric.v1.json'], 'metric_receipt.json', 'metric'),
    ('finite-algebra', ['algebra.v1.json'], 'algebra_receipt.json', 'algebra'),
    ('finite-multiagent', ['multiagent.v1.json'], 'multiagent_receipt.json', 'multiagent'),
    ('lp-propose', ['lp.v1.model.json'], 'proposal.json', 'lp'),
]
NATIVE = [('c10.request.json', 'c10'), ('c11.periodic.request.json', 'c11-periodic'),
          ('c11.multiclass.request.json', 'c11-multiclass')]


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


def _audit(log: str, names: list[str]) -> int:
    """Every `#print axioms` theorem appears with only the standard axioms."""
    seen = 0
    for name in names:
        match = re.search(re.escape(f"'{name}' depends on axioms: [") + r'([^\]]*)\]', log)
        if match is None:
            if f"'{name}' does not depend on any axioms" in log:
                seen += 1
                continue
            raise Failure(f'no axiom report for {name}')
        axioms = {a.strip() for a in match.group(1).replace('\n', ' ').split(',') if a.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise Failure(f'{name} depends on {sorted(axioms - ALLOWED_AXIOMS)}')
        seen += 1
    return seen


def _lean(candidate: Path, names: list[str], repo: Path) -> dict:
    lake = shutil.which('lake')
    if lake is None:
        raise Failure('--lean requested but `lake` is not on PATH (install the pinned toolchain)')
    source = next(candidate.glob('*.lean'))
    start = time.monotonic()
    proc = _run([lake, 'env', 'lean', str(source)], os.environ.copy(), repo, timeout=1800)
    log = proc.stdout + proc.stderr
    if proc.returncode != 0 or re.search(r': error', log):
        raise Failure(f'lake env lean failed for {source.name}: {log[-600:]}')
    return {'compiled': True, 'theorems_audited': _audit(log, names), 'seconds': round(time.monotonic() - start, 1)}


def _profile(cmd, env, work, command, inputs, receipt_name, family, lean, repo):
    row = {'command': command, 'example': inputs[0], 'family': family}
    out = work / command
    paths = [str(EXAMPLES / name) for name in inputs]
    result = _json_out(_run(cmd + [command, *paths, '--output', str(out)], env, APP), command)
    check = json.loads((out / 'independent_check.json').read_text())
    row['numeric_status'] = check.get('status')
    if check.get('status') not in ('PASS', 'OPTIMAL_VERIFIED', 'INFEASIBILITY_VERIFIED',
                                   'FINITE_SURVIVAL_TABLE_VERIFIED', 'FROZEN_MENU_OPTIMUM_VERIFIED') \
            and result.get('numeric_status') is None:
        raise Failure(f'{command}: independent check status {check.get("status")}')
    report = json.loads((out / 'scientific_report.json').read_text())
    if report.get('scientific_claims_verified') is not False or report.get('kernel_checked_proof') != 'NOT_EXECUTED':
        raise Failure(f'{command}: report claims more than a numeric result')
    if family is None:
        return row
    request = paths[0]
    receipt_args = []
    if receipt_name is not None:
        receipt = out / receipt_name
        if command == 'lp-propose':
            proposal = json.loads(receipt.read_text())
            receipt = out / 'lp_receipt.json'
            receipt.write_text(json.dumps(proposal['receipt']))
            _json_out(_run(cmd + ['lp-check', request, str(receipt), '--output', str(work / 'lp-check')], env, APP),
                      'lp-check')
        receipt_args = [str(receipt)]
    region_args = ['--region', paths[1]] if family == 'exit' else []
    candidate = work / f'{command}.lean-candidate'
    emitted = _run(cmd + ['lean-emit', '--family', family, request, *receipt_args, *region_args,
                          '--output', str(candidate)], env, APP)
    if emitted.returncode != 0:
        code = json.loads(emitted.stderr)['error']['code']
        if code.endswith('_SCOPE'):
            row['lean'] = f'numeric only: outside the reflection bound ({code})'
            return row
        raise Failure(f'{command}: lean-emit {code}')
    rechecked = _json_out(_run(cmd + ['lean-recheck', '--family', family, request, *receipt_args, *region_args,
                                      '--candidate', str(candidate)], env, APP), f'{command} lean-recheck')
    if rechecked['result'].get('lean_status') != 'NOT_EXECUTED':
        raise Failure(f'{command}: recheck claims Lean execution')
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
    parser.add_argument('--source-root', type=Path,
                        help='repository checkout for the native C10/C11 runs and Lean (default: the enclosing one)')
    args = parser.parse_args(argv)
    repo = args.source_root.resolve() if args.source_root else find_repository()
    if args.lean and repo is None:
        parser.error('--lean needs a repository checkout with the pinned toolchain (--source-root)')
    cmd, env = _app_command(args.app)
    rows, failures = [], []
    with tempfile.TemporaryDirectory(prefix='permansson-e2e-') as td:
        work = Path(td)
        for command, inputs, receipt, family in PROFILES:
            try:
                rows.append(_profile(cmd, env, work, command, inputs, receipt, family, args.lean, repo))
            except (Failure, subprocess.TimeoutExpired, json.JSONDecodeError, OSError, KeyError) as exc:
                failures.append({'command': command, 'error': str(exc)})
            print(json.dumps(rows[-1] if not failures or failures[-1]['command'] != command else failures[-1],
                             ensure_ascii=False), flush=True)
        for request, label in NATIVE:
            if repo is None:
                rows.append({'command': 'run', 'example': request,
                             'numeric_status': 'skipped: no repository checkout (pass --source-root)'})
                print(json.dumps(rows[-1]), flush=True)
                continue
            try:
                result = _json_out(_run(cmd + ['run', str(EXAMPLES / request), '--source-root', str(repo),
                                               '--output', str(work / label)], env, APP), label)
                rows.append({'command': 'run', 'example': request, 'numeric_status': result.get('numeric_status')})
                print(json.dumps(rows[-1]), flush=True)
            except (Failure, subprocess.TimeoutExpired, json.JSONDecodeError, OSError) as exc:
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
