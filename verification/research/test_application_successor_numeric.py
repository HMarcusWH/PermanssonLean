"""Source-tree integration smoke for the separately versioned numeric successor."""
from pathlib import Path
import os
import subprocess
import sys
import unittest

BASE = Path(__file__).resolve().parents[2]
APP = BASE / 'apps/permansson/application-successor'

class ApplicationSuccessorNumericTest(unittest.TestCase):
    def test_successor_package_suite(self):
        if not APP.is_dir():
            self.skipTest('application-successor not yet installed')
        env = dict(os.environ)
        env['PERMANSSON_SOURCE_ROOT'] = str(BASE)
        p = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s',
                            str(APP / 'tests'), '-q'], cwd=BASE, env=env,
                           capture_output=True, text=True, timeout=180)
        self.assertEqual(p.returncode, 0, msg=(p.stdout+p.stderr)[-12000:])
