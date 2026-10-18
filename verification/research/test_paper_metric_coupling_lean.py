"""Discovered source/signature/axiom audit for actual A3 coupling certificates."""
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]


class MetricCouplingIntegration(unittest.TestCase):
    def test_actual_metric_certificates_and_transitive_axioms(self):
        scratch = ROOT / ".lake/closure-build"
        scratch.mkdir(parents=True, exist_ok=True)
        command = [sys.executable, str(ROOT / "verification/research/paper_closure_metric_coupling_audit.py"),
                   "--output", ".lake/closure-build/unittest-metric-coupling-receipt.json"]
        if pinned := os.environ.get("PERMANSSON_PAPER_LEAN"):
            command += ["--compiler", pinned]
        log = scratch / "unittest-metric-coupling-audit.out"
        try:
            run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                 encoding="utf-8", errors="replace", timeout=6000)
        except (OSError, subprocess.TimeoutExpired) as exc:
            log.write_text(str(exc), encoding="utf-8")
            self.fail(str(log) + "\n" + str(exc))
        log.write_text(run.stdout + run.stderr, encoding="utf-8")
        self.assertEqual(run.returncode, 0, str(log) + "\n" + run.stdout[-2000:] + run.stderr[-2000:])


if __name__ == "__main__":
    unittest.main()
