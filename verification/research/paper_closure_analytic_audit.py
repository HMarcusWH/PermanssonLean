"""Reproduce source/axiom evidence for the additive analytic closure modules.

This is compiler evidence in the exported scope, not a claim that every atlas
contract is closed. A private helper is audited transitively through exports.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
MODULES = [
    'Probability.ProjectedCommonSubkernel', 'Quotient.GeometricPrefix',
    'Quotient.GeometricQuotient', 'Quotient.GeometricMargin',
    'Probability.LocalizedHistoryTV', 'Probability.SummablePathScores',
    'Probability.CouplingDualBound', 'Perturbation.DirectDualContraction',
    'Perturbation.PrimitiveProductTV', 'Perturbation.PrimitiveMetricBudget',
    'GrammarRobust.CompatibleOverlap', 'GrammarRobust.OverlapKernelAssembly',
    'GrammarRobust.OverlapCanonicalBridge', 'GrammarRobust.LowerSetTransport',
    'GrammarRobust.OriginalLowerSetTransport',
    'MultiAgent.FeasibleAnchors', 'MultiAgent.CorrelatedMediator', 'MultiAgent.FiniteMediation',
    'ReverseSolver.AdaptiveGrammarControl',
    'Specialized.SeamReduction', 'Specialized.FiniteDetection',
    'Specialized.ShellSchur', 'Specialized.ShellResolvent', 'Specialized.SingularCompatibility',
    'Specialized.GramSeparation',
]
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
DECL = re.compile(r'(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+'
                  r'([^\s:({\[]+)')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def axiom_names(group):
    # Full universe printing annotates constant names; it does not create a
    # distinct axiom. Keep the actual constant identifier for allowlist checks.
    plain = re.sub(r'\.\{[^}]*\}', '', group)
    return sorted({x.strip() for x in plain.replace('\n', ' ').split(',') if x.strip()})


def declarations(source):
    source = re.sub(r'/\-.*?\-/|--[^\n]*', '', source, flags=re.S)
    stack, result = [], []
    for line in source.splitlines():
        if match := re.match(r'^namespace\s+(\S+)', line):
            stack.append(match.group(1))
        elif (match := re.match(r'^end\s+(\S+)', line)) and stack and stack[-1] == match.group(1):
            stack.pop()
        elif match := DECL.match(line):
            result.append('.'.join(stack + [match.group(1)]))
    return result


def main():
    builder_sha256 = sha(Path(__file__))
    parser = argparse.ArgumentParser()
    parser.add_argument('--compiler')
    parser.add_argument('--output', default='research/paper_closures/analytic_receipt.json')
    parser.add_argument('--recheck', action='store_true', help='Recompile every scoped module')
    args = parser.parse_args()
    command = [args.compiler] if args.compiler else ['lake', 'env', 'lean']
    version = subprocess.run(command + ['--version'], cwd=ROOT, capture_output=True,
                             encoding='utf-8', errors='replace', timeout=120)
    expected = (ROOT / 'lean-toolchain').read_text().strip().rsplit(':v', 1)[-1]
    actual = re.search(r'\bversion\s+([0-9.]+)', version.stdout)
    if version.returncode or not actual or actual.group(1) != expected:
        raise RuntimeError('Pinned compiler mismatch: ' + version.stdout + version.stderr)
    files, exports = {}, []
    for short in MODULES:
        module = 'PermanssonResearch.' + short
        relative = module.replace('.', '/') + '.lean'
        path = ROOT / relative
        source = path.read_text(encoding='utf-8-sig')
        code = re.sub(r'/\-.*?\-/|--[^\n]*', '', source, flags=re.S)
        if re.search(r'\b(?:sorry|admit|native_decide)\b|(?m:^\s*axiom\s)', code):
            raise RuntimeError('Forbidden source declaration: ' + relative)
        journal = ROOT / '.lake/closure-build' / (module + '.json')
        status = json.loads(journal.read_text()) if journal.is_file() else {}
        artifact = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
        fresh = artifact.is_file() and artifact.stat().st_mtime_ns >= path.stat().st_mtime_ns
        if (args.recheck or status.get('status') != 'PASS' or status.get('returncode') != 0
                or not fresh or status.get('source_sha256') != sha(path)):
            print('Elaborating', module, flush=True)
            if status.get('status') == 'RUNNING' and time.time() - status.get('started', 0) < 600:
                raise RuntimeError('Another module check is running: ' + module)
            journal.parent.mkdir(parents=True, exist_ok=True)
            artifact.parent.mkdir(parents=True, exist_ok=True)
            before = sha(path)
            start = time.time()
            journal.write_text(json.dumps({'module': module, 'started': start,
                               'status': 'RUNNING', 'source_sha256': before}) + '\n', encoding='utf-8')
            run = subprocess.run(command + ['-o', str(artifact), relative], cwd=ROOT,
                                 capture_output=True, encoding='utf-8', errors='replace', timeout=600)
            journal.with_suffix('.out').write_text(run.stdout + run.stderr, encoding='utf-8')
            status = {'module': module, 'started': start, 'elapsed': time.time() - start,
                      'status': 'PASS' if run.returncode == 0 and before == sha(path) else 'FAIL',
                      'returncode': run.returncode, 'source_sha256': before}
            journal.write_text(json.dumps(status) + '\n', encoding='utf-8')
            if status['status'] != 'PASS':
                raise RuntimeError('Compiler/source-stability check failed: ' + module)
            print('PASS', module, flush=True)
        files[relative] = {'sha256': sha(path), 'artifact_sha256': sha(artifact), 'compiler': status}
        exports.extend(declarations(source))
    audit = ROOT / '.lake/closure-build/AnalyticAxiomAudit.lean'
    audit.write_text(''.join('import PermanssonResearch.' + m + '\n' for m in MODULES) +
                     'set_option pp.universes true\nset_option pp.fullNames true\n' +
                     ''.join('#check ' + n + '\n#print axioms ' + n + '\n' for n in exports), encoding='utf-8')
    run = subprocess.run(command + [str(audit)], cwd=ROOT, capture_output=True,
                         encoding='utf-8', errors='replace', timeout=600)
    log = audit.with_suffix('.out')
    log.write_text(run.stdout + run.stderr, encoding='utf-8')
    reports = {}
    for name, group in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", run.stdout, re.S):
        reports[name] = axiom_names(group)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", run.stdout):
        reports[name] = []
    missing = sorted(set(exports) - set(reports))
    bad = {name: axioms for name, axioms in reports.items() if not set(axioms) <= ALLOW}
    if run.returncode or missing or bad:
        raise RuntimeError((run.returncode, missing, bad, str(log)))
    for relative, record in files.items():
        artifact = ROOT / '.lake/build/lib/lean' / relative.replace('.lean', '.olean')
        if sha(ROOT / relative) != record['sha256'] or sha(artifact) != record['artifact_sha256']:
            raise RuntimeError('Input or compiled artifact changed during audit: ' + relative)
    if sha(Path(__file__)) != builder_sha256:
        raise RuntimeError('Audit driver changed during execution')
    receipt = {'status': 'PASS', 'evidence_kind': 'LOCAL_COMPILER_AND_TRANSITIVE_AXIOM_AUDIT',
               'receipt_builder_sha256': builder_sha256,
               'compiler': version.stdout.strip(), 'lean_toolchain': expected,
               'source_scope': files, 'declaration_count': len(exports), 'declarations': reports,
               'axiom_allowlist': sorted(ALLOW), 'compiler_returncode': run.returncode,
               'audit_stdout_sha256': sha(log),
               'residual': 'Scope and unfinished atlas obligations are recorded separately. '
                           'This receipt does not supply genuine PR-head/synthetic-merge CI evidence.'}
    destination = ROOT / args.output
    destination.parent.mkdir(parents=True, exist_ok=True)
    signatures = destination.with_name('analytic_signatures_axioms.txt')
    signatures.write_text(run.stdout + run.stderr, encoding='utf-8')
    receipt['signature_and_axiom_output'] = {
        'path': signatures.relative_to(ROOT).as_posix(), 'sha256': sha(signatures)}
    destination.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print('Analytic closure audit PASS:', len(exports), 'exports;', destination)


if __name__ == '__main__':
    main()
