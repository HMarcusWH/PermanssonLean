"""Discovered post-build audit of constructed first-moment completeness."""
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]


class PaperCompletenessIntegration(unittest.TestCase):
    def test_source_bound_transitive_axioms(self):
        scratch = ROOT / '.lake/closure-build'
        scratch.mkdir(parents=True, exist_ok=True)
        command = [sys.executable,
                   str(ROOT / 'verification/research/paper_closure_completeness_audit.py'),
                   '--output', '.lake/closure-build/unittest-completeness-receipt.json']
        pinned = os.environ.get('PERMANSSON_PAPER_LEAN') or os.environ.get('PERMANSSON_X1_LEAN')
        if pinned:
            command += ['--compiler', pinned]
        log = scratch / 'unittest-completeness-audit.out'
        try:
            run = subprocess.run(command, cwd=ROOT, capture_output=True,
                                 text=True, encoding='utf-8', errors='replace',
                                 timeout=int(os.environ.get('PERMANSSON_PAPER_CHECK_TIMEOUT', '600'))+180)
        except (subprocess.TimeoutExpired, OSError) as exc:
            log.write_text(str(exc), encoding='utf-8')
            self.fail(str(log)+'\n'+str(exc))
        log.write_text(run.stdout+run.stderr, encoding='utf-8')
        self.assertEqual(run.returncode, 0, str(log)+'\n'+run.stdout[-2000:]+run.stderr[-2000:])


if __name__ == '__main__':
    unittest.main()
