"""Mandatory post-build U03, U17 and finite-A3 source/axiom audits.

The full Research CI discovers this module after building the research root.
Subprocesses run sequentially and write only test-local receipts under .lake.
"""
import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
AUDITS = [
    ('strategy', 'paper_closure_strategy_audit.py'),
    ('economic', 'paper_closure_economic_audit.py'),
    ('finite-occupation', 'paper_closure_finite_occupation_audit.py'),
]


class PaperStrategyEconomicIntegration(unittest.TestCase):
    def test_source_bound_transitive_axioms(self):
        scratch = ROOT / '.lake/closure-build'
        scratch.mkdir(parents=True, exist_ok=True)
        pinned = os.environ.get('PERMANSSON_PAPER_LEAN') or os.environ.get('PERMANSSON_X1_LEAN')
        timeout = int(os.environ.get('PERMANSSON_PAPER_CHECK_TIMEOUT', '600')) + 180
        for label, script in AUDITS:
            with self.subTest(unit=label):
                output = '.lake/closure-build/unittest-' + label + '-receipt.json'
                command = [sys.executable, str(ROOT / 'verification/research' / script),
                           '--output', output]
                if pinned:
                    command += ['--compiler', pinned]
                log = scratch / ('unittest-' + label + '-audit.out')
                try:
                    run = subprocess.run(command, cwd=ROOT, capture_output=True,
                                         text=True, encoding='utf-8', errors='replace',
                                         timeout=timeout)
                except (subprocess.TimeoutExpired, OSError) as exc:
                    log.write_text(str(exc), encoding='utf-8')
                    self.fail(str(log) + '\n' + str(exc))
                log.write_text(run.stdout + run.stderr, encoding='utf-8')
                self.assertEqual(run.returncode, 0,
                                 str(log) + '\n' + run.stdout[-2000:] + run.stderr[-2000:])


if __name__ == '__main__':
    unittest.main()
