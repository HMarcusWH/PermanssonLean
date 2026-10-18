"""Mandatory post-build analytic, typed-block and causal-model proof audits.

The existing full Research CI discovers these tests after building its complete
root. Test-local reports stay under .lake and never relabel the supplied spec.
"""
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]


class PaperAnalyticIntegration(unittest.TestCase):
    def run_script(self, name, *args, timeout=1800):
        command = [sys.executable, str(ROOT / 'verification/research' / name), *args]
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                             encoding='utf-8', errors='replace', timeout=timeout)
        scratch = ROOT / '.lake/closure-build'
        scratch.mkdir(parents=True, exist_ok=True)
        log = scratch / (name + '.unittest.out')
        log.write_text(run.stdout + run.stderr, encoding='utf-8')
        self.assertEqual(run.returncode, 0, str(log) + '\n' + run.stdout[-2000:] + run.stderr[-2000:])

    def test_canonical_source_blobs(self):
        self.run_script('paper_closure_source_audit.py', '--output',
                        '.lake/closure-build/unittest-source-audit.json', timeout=120)

    def test_every_research_module_is_imported(self):
        self.run_script('paper_closure_imports.py', timeout=120)

    def test_named_exports_and_transitive_axioms(self):
        args = ['--output', '.lake/closure-build/unittest-analytic-receipt.json']
        pinned = os.environ.get('PERMANSSON_PAPER_LEAN')
        if pinned:
            args += ['--compiler', pinned]
        self.run_script('paper_closure_analytic_audit.py', *args)


if __name__ == '__main__':
    unittest.main()
