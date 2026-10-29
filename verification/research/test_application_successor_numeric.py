"""Source-tree integration with full validated schemas, even on bare Research CI.

No skip/fallback: missing Python schema dependencies must be installed and the
actual tests must pass. The historical Research workflow remains unchanged.
"""
from pathlib import Path
import importlib.util
import os
import subprocess
import sys
import tempfile
import unittest
import venv

BASE=Path(__file__).resolve().parents[2]
APP=BASE/'apps/permansson/application-successor'

class ApplicationSuccessorNumericTest(unittest.TestCase):
    def test_successor_package_suite(self):
        if not APP.is_dir():
            self.fail('successor application package not installed')
        env=dict(os.environ)
        env['PERMANSSON_SOURCE_ROOT']=str(BASE)
        with tempfile.TemporaryDirectory(prefix='permansson-schema-') as workspace:
            interpreter=sys.executable
            if any(importlib.util.find_spec(name) is None for name in ('jsonschema','referencing')):
                venv.EnvBuilder(with_pip=True,system_site_packages=False).create(workspace)
                interpreter=str(Path(workspace)/('Scripts/python.exe' if os.name=='nt' else 'bin/python'))
                install=subprocess.run([interpreter,'-m','pip','install',
                  '--disable-pip-version-check','--no-input',
                  'jsonschema==4.26.0','referencing==0.37.0'],
                  cwd=BASE,env=env,capture_output=True,text=True,timeout=180)
                self.assertEqual(install.returncode,0,msg=(install.stdout+install.stderr)[-8000:])
            p=subprocess.run([interpreter,'-B','-m','unittest','discover',
                 '-s',str(APP/'tests'),'-q'],cwd=BASE,env=env,
                 capture_output=True,text=True,timeout=240)
            self.assertEqual(p.returncode,0,msg=(p.stdout+p.stderr)[-12000:])
