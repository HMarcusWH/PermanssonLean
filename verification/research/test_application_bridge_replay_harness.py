"""The live-Lean harness must not leak compiler processes on timeout."""
from __future__ import annotations

import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

from application_bridge_replay import run_bounded


@unittest.skipUnless(sys.platform.startswith("linux"), "process-group semantics checked on Linux runners")
class BoundedRunnerTests(unittest.TestCase):
    def test_timeout_kills_forked_children(self):
        with tempfile.TemporaryDirectory() as td:
            marker = Path(td) / "child.pid"
            # The parent shell forks a long-running child, like `lake` forking `lean`.
            script = f"sleep 60 & echo $! > {marker}; wait"
            with self.assertRaises(AssertionError) as raised:
                run_bounded(["sh", "-c", script], Path(td), 1)
            self.assertIn("process group killed", str(raised.exception))
            child = int(marker.read_text().strip())
            for _ in range(50):
                if not Path(f"/proc/{child}").exists():
                    break
                time.sleep(0.1)
            self.assertFalse(Path(f"/proc/{child}").exists(), "forked child outlived the timeout")

    def test_normal_completion_returns_output(self):
        code, out = run_bounded(["sh", "-c", "echo ok; echo err >&2; exit 3"], Path(os.getcwd()), 30)
        self.assertEqual(code, 3)
        self.assertIn("ok", out)
        self.assertIn("err", out)


if __name__ == "__main__":
    unittest.main()
