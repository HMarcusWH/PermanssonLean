"""Shared pinned-Lean replay harness for application bridge instance tests.

Compiles generated instance sources with the repository's real `lake env
lean` (no stub or skip), and checks that single-line semantic mutations fail
at the falsified obligation rather than at an import, definition or syntax
position. Axiom records are parsed by the already-reviewed research parser.
"""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from test_application_lp_bridge_live_lean import _audited_axioms

ROOT = Path(__file__).resolve().parents[2]

UNRELATED_FAILURES = ("unknown module", "unknown identifier", "failed to import",
                      "unexpected token", "syntax error", "out of memory",
                      "maximum number of heartbeats", "failed to synthesize",
                      "type mismatch", "timed out", "timeout")


def compile_source(code: str, filename: str, *, timeout: int = 450):
    if shutil.which("lake") is None or not (ROOT / ".lake").is_dir():
        raise AssertionError("Real pinned Research Lean compiler required; no skip/stub")
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake", prefix="app-bridge-") as td:
        source = Path(td) / filename
        source.write_text(code, encoding="utf-8")
        process = subprocess.run(
            ["lake", "env", "lean", str(source)], cwd=ROOT,
            capture_output=True, text=True, timeout=timeout)
    result = process.stdout + "\n" + process.stderr
    if len(result) > 250000:
        raise AssertionError("unbounded Lean compiler output")
    return process.returncode, result


def audited_axioms(log: str, expected: list[str]):
    return _audited_axioms(log, expected)


def change_line(code: str, prefix: str, old: str, new: str) -> str:
    lines = code.splitlines()
    locations = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    if len(locations) != 1:
        raise AssertionError("missing/ambiguous mutation target " + prefix)
    before = lines[locations[0]]
    if before.count(old) != 1:
        raise AssertionError("mutation fragment must occur exactly once: " + old)
    lines[locations[0]] = before.replace(old, new)
    return "\n".join(lines) + "\n"


def theorem_blocks(lines: list[str]) -> dict[str, tuple[int, int]]:
    """Each theorem block runs from its `theorem` line to the next blank line."""
    blocks = {}
    for i, line in enumerate(lines, 1):
        if line.startswith("theorem "):
            end = next((j for j in range(i, len(lines) + 1) if not lines[j - 1].strip()), len(lines))
            blocks[line.split()[1]] = (i, end)
    return blocks


def assert_semantic_rejection(case, original: str, changed: str, theorem: str, filename: str):
    """A mutation of a source that compiled on the same pinned compiler must
    fail inside the targeted theorem; downstream instance theorems may also
    fail, but no definition, import or syntax position may."""
    case.assertNotEqual(sha256(original.encode()).digest(), sha256(changed.encode()).digest())
    lhs, rhs = original.splitlines(), changed.splitlines()
    case.assertEqual(len(lhs), len(rhs))
    case.assertEqual(sum(a != b for a, b in zip(lhs, rhs)), 1,
                     "mutation must change exactly one source line")
    exitcode, log = compile_source(changed, filename)
    case.assertNotEqual(exitcode, 0, "false certificate was accepted")
    lower = log.lower()
    for forbidden in UNRELATED_FAILURES:
        case.assertNotIn(forbidden, lower, "unrelated compiler failure: " + forbidden)
    errors = [int(m.group(1)) for m in re.finditer(
        re.escape(filename) + r":(\d+):\d+: error", log)]
    case.assertTrue(errors, "no source-anchored Lean error:\n" + log[-3000:])
    blocks = theorem_blocks(rhs)
    start, end = blocks[theorem]
    case.assertTrue(any(start <= err <= end for err in errors),
                    f"no error at falsified {theorem}@{start}: {errors}\n" + log[-3000:])
    case.assertTrue(all(any(a <= err <= b for a, b in blocks.values()) for err in errors),
                    f"error outside theorem proofs: {errors}\n" + log[-3000:])
