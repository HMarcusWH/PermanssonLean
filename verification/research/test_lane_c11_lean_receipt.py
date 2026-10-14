"""Generated C11 input/receipt literal must compile with genuine Lean kernel."""
from __future__ import annotations
import copy
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
import unittest

from c11_stationary_execution import StationaryError, execute
from c11_emit_stationary_lean import emit_source

ROOT=Path(__file__).resolve().parents[2]

class C11LeanLiteralTests(unittest.TestCase):
    def setUp(self):
        self.example=execute({"n":2,"matrix":[["0","1"],["1","0"]],
                              "descriptor":[False,True]})

    def test_01_reject_forged_share(self):
        bad=copy.deepcopy(self.example)
        bad["classes"][0]["true_share"]="1"
        with self.assertRaises(StationaryError):emit_source(bad)

    def test_02_source_contains_complete_data(self):
        code=emit_source(self.example)
        for text in ["ClassStationaryCandidate 2","checkStationaryFamily",
                     "member0_share","completeFamily_accepted",
                     "#print axioms C11ReifiedFixture.completeFamily_accepted"]:
            self.assertIn(text,code)

    def test_03_genuine_compiled_receipt(self):
        if shutil.which("lake") is None:
            self.skipTest("Lean only available in pinned Research Lean CI")
        with tempfile.TemporaryDirectory() as dirname:
            source=Path(dirname)/"C11ReifiedStationary.lean"
            source.write_text(emit_source(self.example),encoding="utf-8")
            compiled=subprocess.run(["lake","env","lean",str(source)],
                                    cwd=ROOT,stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE,text=True,timeout=600)
            self.assertEqual(compiled.returncode,0,
                             (compiled.stdout+compiled.stderr)[-5000:])
            for name in ("member0_accepted","member0_share",
                         "completeFamily_accepted"):
                report=re.search(
                    rf"'(?:C11ReifiedFixture\.)?{name}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
                    compiled.stdout)
                self.assertIsNotNone(report,compiled.stdout[-3500:])
                axioms={x.strip() for x in (report.group(2) or "").split(",") if x.strip()}
                self.assertLessEqual(axioms,
                        {"propext","Classical.choice","Quot.sound"})

if __name__=="__main__":
    unittest.main()
