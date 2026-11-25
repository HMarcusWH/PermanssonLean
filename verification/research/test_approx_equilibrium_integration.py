"""Research CLI boundaries and independently checked fixture outputs."""
import json
import subprocess
import sys
import tempfile
from pathlib import Path
import unittest
from test_approx_equilibrium import ROOT,fixture

class ExactEquilibriumIntegrationTests(unittest.TestCase):
    def test_cli_roundtrip(self):
        with tempfile.TemporaryDirectory() as td:
            folder=Path(td)
            for name in ("matching","kite","x1","transport"):
                raw=fixture(name);inp=folder/"input.json";inp.write_text(json.dumps(raw))
                run=[sys.executable,"-m","verification.research.approx_equilibrium"]
                p=subprocess.run(run+[raw["kind"],str(inp)],cwd=ROOT,text=True,capture_output=True,timeout=30)
                self.assertEqual(p.returncode,0,p.stderr);out=json.loads(p.stdout)
                self.assertEqual(out["verification"]["lean_status"],"NOT_EXECUTED")
                receipt=folder/"receipt.json";receipt.write_text(json.dumps(out["receipt"]))
                c=subprocess.run(run+["check",str(inp),str(receipt)],cwd=ROOT,text=True,capture_output=True,timeout=30)
                self.assertEqual(c.returncode,0,c.stderr)
                self.assertEqual(json.loads(c.stdout),out["verification"])
    def test_duplicate_json_key(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/"input.json";p.write_text('{"kind":"regret","kind":"kite"}')
            r=subprocess.run([sys.executable,"-m","verification.research.approx_equilibrium","regret",str(p)],
                             cwd=ROOT,text=True,capture_output=True,timeout=30)
            self.assertEqual(r.returncode,2)

if __name__=="__main__":unittest.main()
