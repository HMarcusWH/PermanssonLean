"""The documented end-to-end walkthrough keeps working (without Lean).

`scripts/end_to_end.py --lean` additionally compiles every candidate; that
needs the pinned toolchain and is exercised outside the unit suite.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

APP=Path(__file__).resolve().parents[1]
SCRIPT=APP/'scripts/end_to_end.py'
sys.path.insert(0,str(APP/'scripts'))
import end_to_end
sys.path.pop(0)
sys.path.insert(0,str(APP/'src'))
from permansson_app.capabilities import registry
from permansson_app.proof.lean_candidates import families


class EndToEndScriptTests(unittest.TestCase):
    def test_walkthrough_covers_every_command_and_family(self):
        commands={entry['cli'] for entry in registry()['exact_profiles'].values()}
        covered={command for command,*_ in end_to_end.PROFILES}|{'lp-check'}
        self.assertEqual(commands,covered)
        self.assertEqual({family for *_,family in end_to_end.PROFILES},set(families()))
        for _,inputs,_,_ in end_to_end.PROFILES:
            for name in inputs:
                self.assertTrue((end_to_end.EXAMPLES/name).is_file(),name)

    def test_walkthrough_passes_from_source(self):
        env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
        with tempfile.TemporaryDirectory() as td:
            report=Path(td)/'report.json'
            p=subprocess.run([sys.executable,'-B',str(SCRIPT),'--report',str(report)],cwd=APP,env=env,
                             text=True,capture_output=True,timeout=900)
            self.assertEqual(p.returncode,0,p.stdout[-3000:]+p.stderr[-3000:])
            summary=json.loads(report.read_text())
        self.assertEqual((summary['status'],summary['failures']),('PASS',[]))
        rows=[row for row in summary['profiles'] if row['command']!='run']
        self.assertEqual(len(rows),len(end_to_end.PROFILES))
        emitted=[row for row in rows if row.get('lean','').startswith('emitted')]
        self.assertGreaterEqual(len(emitted),20)
        for row in rows:
            self.assertTrue(row['lean'].startswith(('emitted','numeric only: outside the reflection bound')),row)
        native=[row for row in summary['profiles'] if row['command']=='run']
        self.assertEqual(len(native),3)
        # Inside a checkout the native providers run; in a detached copy they are skipped, not failed.
        expected='EXACT_RATIONAL_VERIFIED' if end_to_end.find_repository() else 'skipped: no repository checkout (pass --source-root)'
        self.assertTrue(all(row['numeric_status']==expected for row in native),native)


if __name__=='__main__':
    unittest.main()
