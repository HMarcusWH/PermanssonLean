"""Required post-build Research CI checks for the actual multiagent fixtures.

These are positive Lean controls: import failures, timeouts, and proof failures
all fail the regression. The named-source axiom audit is also mandatory.
"""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ["MultiAgentAsymmetry", "MultiAgentPrivateClock", "MultiAgentFiniteProduct"]


class MultiAgentLeanClosure(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = ROOT / ".lake/multiagent-paper-closure"
        scratch.mkdir(parents=True, exist_ok=True)
        cls.receipt_path = scratch / "fixture_receipt.json"
        cls.receipt = {"status": "RUNNING", "fixtures": {}, "source_sha256": {}}
        pinned = os.environ.get("PERMANSSON_PAPER_LEAN") or os.environ.get("PERMANSSON_X1_LEAN")
        lean = [pinned] if pinned else ["lake", "env", "lean"]
        timeout = int(os.environ.get("PERMANSSON_PAPER_CHECK_TIMEOUT", "600"))
        for name in FIXTURES:
            path = ROOT / f"verification/research/{name}.lean"
            cls.receipt["source_sha256"][str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
            started = time.monotonic()
            try:
                run = subprocess.run(lean + [str(path)], cwd=ROOT, capture_output=True,
                                     text=True, encoding="utf-8", timeout=timeout)
                output = run.stdout + run.stderr
                result = {"status": "PASS" if run.returncode == 0 else "FAIL",
                          "returncode": run.returncode, "elapsed": time.monotonic()-started}
            except (subprocess.TimeoutExpired, OSError) as exc:
                output = str(exc)
                result = {"status": "INVALID_TEST", "elapsed": time.monotonic()-started}
            (scratch / f"{name}.out").write_text(output, encoding="utf-8")
            cls.receipt["fixtures"][name] = result
            cls.receipt_path.write_text(json.dumps(cls.receipt, indent=2), encoding="utf-8")
        command = [sys.executable, str(ROOT / "verification/research/audit_multiagent_closure.py"),
                   "--timeout", str(timeout)]
        if pinned:
            command += ["--lean", pinned]
        try:
            run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                 encoding="utf-8", timeout=timeout+30)
            output = run.stdout + run.stderr
            audit = json.loads((scratch / "receipt.json").read_text(encoding="utf-8"))
            cls.receipt["axiom_audit"] = {"status": audit["status"], "returncode": run.returncode,
                                          "declarations": audit.get("declarations", 0)}
        except (subprocess.TimeoutExpired, OSError) as exc:
            output = str(exc)
            cls.receipt["axiom_audit"] = {"status": "INVALID_TEST"}
        (scratch / "unittest_audit.out").write_text(output, encoding="utf-8")
        ok = all(r["status"] == "PASS" for r in cls.receipt["fixtures"].values()) and \
             cls.receipt["axiom_audit"]["status"] == "PASS" and \
             cls.receipt["axiom_audit"]["returncode"] == 0
        cls.receipt["status"] = "PASS" if ok else "FAIL"
        cls.receipt_path.write_text(json.dumps(cls.receipt, indent=2), encoding="utf-8")

    def _fixture(self, name):
        self.assertEqual(self.receipt["fixtures"][name]["status"], "PASS", str(self.receipt_path))

    def test_asymmetric_player_swap(self):
        self._fixture("MultiAgentAsymmetry")

    def test_actual_periodic_private_clock(self):
        self._fixture("MultiAgentPrivateClock")

    def test_three_player_asymmetry(self):
        self._fixture("MultiAgentFiniteProduct")

    def test_transitive_axioms(self):
        self.assertEqual(self.receipt["axiom_audit"]["status"], "PASS", str(self.receipt_path))
        self.assertEqual(self.receipt["axiom_audit"]["returncode"], 0)


if __name__ == "__main__":
    unittest.main()
