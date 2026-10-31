"""The live-Lean harness must not leak compiler processes on timeout."""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

import application_bridge_replay
from application_bridge_replay import kill_tree, run_bounded, spawn_options


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


class _Process:
    pid = 4242

    def __init__(self):
        self.killed = False

    def kill(self):
        self.killed = True


class PlatformFallbackTests(unittest.TestCase):
    """The non-POSIX branch, exercised here with its system calls replaced; a real
    Windows run is part of the unqualified platform matrix (PKG-03)."""

    def test_spawn_options(self):
        self.assertEqual(spawn_options(True), {"start_new_session": True})
        self.assertEqual(spawn_options(False),
                         {"creationflags": application_bridge_replay.CREATE_NEW_PROCESS_GROUP})
        self.assertEqual(application_bridge_replay.CREATE_NEW_PROCESS_GROUP,
                         getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0x00000200))

    def test_windows_kill_ends_the_whole_tree(self):
        process = _Process()
        with mock.patch.object(application_bridge_replay.subprocess, "run") as run:
            kill_tree(process, posix=False)
        self.assertEqual(run.call_args.args[0], ["taskkill", "/PID", "4242", "/T", "/F"])
        self.assertTrue(process.killed)

    def test_windows_kill_falls_back_when_taskkill_is_unavailable(self):
        for error in (FileNotFoundError("taskkill"), subprocess.TimeoutExpired("taskkill", 60)):
            process = _Process()
            with self.subTest(error=type(error).__name__), \
                    mock.patch.object(application_bridge_replay.subprocess, "run", side_effect=error):
                kill_tree(process, posix=False)
            self.assertTrue(process.killed)

    def test_posix_group_that_already_exited_is_not_an_error(self):
        with mock.patch.object(application_bridge_replay.os, "killpg", side_effect=ProcessLookupError):
            kill_tree(_Process(), posix=True)


if __name__ == "__main__":
    unittest.main()
