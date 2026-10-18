"""Reproduce the U03 declaration audit and source-bound evidence receipt.

Default execution uses the repository's pinned Lake environment. `--compiler`
permits a direct pinned compiler when LEAN_PATH is supplied externally.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
UNIT = 'U03'
AUDIT_STEM = 'StrategyAxiomAudit'
OUTPUT = 'verification/research/paper_closure_strategy_receipt_2026-10-18.json'
RESIDUAL = ('Private random-seed behavioralization is represented by the behavioral-rule interface; '
            'risk-sensitive or opponent-correlated deviations are outside the selected information/payoff '
            'structure. No best-response or equilibrium uniqueness is claimed.')
MODULES = [
    'PermanssonResearch/StrategicWorld/ActionTrace.lean',
    'PermanssonResearch/StrategicWorld/ActionTraceCanonical.lean',
    'PermanssonResearch/StrategicWorld/ActionTraceStatePrefix.lean',
    'PermanssonResearch/StrategicWorld/ActionTraceInitialLaw.lean',
    'PermanssonResearch/StrategicWorld/ActionTraceOriginalBridge.lean',
    'PermanssonResearch/Games/DiscountedVerification.lean',
    'PermanssonResearch/Games/DiscountedTraceExpectation.lean',
    'PermanssonResearch/X1/FullStrategyCertificate.lean',
    'PermanssonResearch/X1/FullStrategyTrace.lean',
    'PermanssonResearch/X1/StrategyRegression.lean',
    'PermanssonResearch/X1/StrategyOriginalBridge.lean',
]
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
ATTR = r'(?:@\[[^\]]*\]\s*)?'
MODS = r'(?:(?:noncomputable|protected)\s+)*'
DECL = re.compile(ATTR + MODS + r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)')


def declarations(source):
    source = re.sub(r'/\-.*?\-/|--[^\n]*', '', source, flags=re.S)
    stack, result = [], []
    for line in source.splitlines():
        if m := re.match(r'^namespace\s+(\S+)', line):
            stack.append(m.group(1))
        elif (m := re.match(r'^end\s+(\S+)', line)) and stack and stack[-1] == m.group(1):
            stack.pop()
        elif re.match(ATTR + r'private\s', line):
            raise AssertionError('Private declaration cannot be addressed for audit: ' + line)
        elif re.match(r'^example\b', line):
            raise AssertionError('Anonymous example cannot be addressed for audit: ' + line)
        elif re.match(ATTR + MODS + r'instance\s*(?::|\(|\[|\{)', line):
            raise AssertionError('Anonymous instance cannot be addressed for audit: ' + line)
        elif m := DECL.match(line):
            result.append('.'.join(stack + [m.group(1)]))
    return result


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--compiler')
    parser.add_argument('--output', default=OUTPUT)
    args = parser.parse_args()
    sources = {rel: (ROOT / rel).read_text(encoding='utf-8-sig') for rel in MODULES}
    for rel, content in sources.items():
        code = re.sub(r'/\-.*?\-/|--[^\n]*', '', content, flags=re.S)
        assert not re.search(r'\b(?:sorry|admit|native_decide)\b|(?m:^\s*axiom\s)', code), rel
    names = [name for source in sources.values() for name in declarations(source)]
    imports = [rel.removesuffix('.lean').replace('/', '.') for rel in MODULES]
    audit = ROOT / ('.lake/closure-build/' + AUDIT_STEM + '.lean')
    audit.parent.mkdir(parents=True, exist_ok=True)
    audit.write_text(''.join('import ' + name + '\n' for name in imports) +
                     ''.join('#print axioms ' + name + '\n' for name in names), encoding='utf-8')
    command = [args.compiler] if args.compiler else ['lake', 'env', 'lean']
    result = subprocess.run(command + [str(audit)], cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, encoding='utf-8', timeout=600)
    log = audit.with_suffix('.out')
    log.write_text(result.stdout, encoding='utf-8')
    reports = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout, re.S):
        reports[name] = sorted({a.strip() for a in axioms.replace('\n', ' ').split(',') if a.strip()})
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        reports[name] = []
    missing = sorted(set(names) - set(reports))
    bad = {name: axioms for name, axioms in reports.items() if not set(axioms) <= ALLOW}
    assert result.returncode == 0 and not missing and not bad, (result.returncode, missing, bad, str(log))
    version = subprocess.run(([args.compiler] if args.compiler else ['lake', 'env', 'lean']) + ['--version'],
                             cwd=ROOT, capture_output=True, text=True, timeout=120)
    receipt = {
        'unit': UNIT, 'source_scope': MODULES, 'source_sha256': {rel: sha(ROOT / rel) for rel in MODULES},
        'compiler': version.stdout.strip(), 'declaration_count': len(names),
        'axiom_allowlist': sorted(ALLOW), 'declarations': reports,
        'audit_source_sha256': sha(audit), 'audit_stdout_sha256': sha(log),
        'compiler_returncode': result.returncode, 'status': 'PASS',
        'residual': RESIDUAL,
    }
    (ROOT / args.output).write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(UNIT + ' axiom/source audit PASS:', len(names), 'declarations;', args.output)
    return 0


if __name__ == '__main__':
    sys.exit(main())
