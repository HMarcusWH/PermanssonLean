"""Versioned C11 finite stationary-family input -> exact rational -> Lean replay.

This certifies a *reified finite rational Markov matrix*, not arbitrary
strategic-world identification, causal transport, PR/Exact GR or empirical fit.
The preexisting generic C11 theorem providers and rational producer/checker
remain unchanged; a real pinned Lean replay is mandatory for `replay` mode.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[3]
RESEARCH = ROOT / "verification" / "research"
if str(RESEARCH) not in sys.path:
    sys.path.insert(0, str(RESEARCH))

from c11_stationary_execution import (StationaryError, StationaryResourceLimit,
    strict_loads, execute, canonical_bytes)
from c11_verify_stationary import verify_report
from c11_emit_stationary_lean import emit_source

FORMAT = "Permansson.C11.ClosureSuccessor.v0.2.0"
MAX_BYTES = 131072
MAX_SUPPORTED_STATES = 6
LEAN_TIMEOUT = 600
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
# Actual previously reviewed provider Git objects from PR79 merged source.
PINNED = {
    "lean-toolchain": "12359f928f18e4a89ebd1444a0310b025931b17d",
    "lakefile.toml": "115d8db722a364cded5214077770990c51dc8973",
    "lake-manifest.json": "e98358df88565d8a4eaf5bd9b3237b102aa7159d",
    "PermanssonResearch/ReverseSolver/C11ObservedStationary.lean":
        "3e823218517c23960ded8e5e2f4b3d1d91c21fac",
    "PermanssonResearch/ReverseSolver/C11StationaryFamily.lean":
        "90fd9bc5f26de5c4e7b55f6b013df6d1ec48205f",
    "PermanssonResearch/ReverseSolver/C11ClassStationaryCertificate.lean":
        "d1e869ec5f9f45f28ecc0dede9e134c785269163",
    "verification/research/c11_stationary_execution.py":
        "213b469bb35ec9785e7a3491d919b84dfd41e71e",
    "verification/research/c11_verify_stationary.py":
        "8b40f9622399181cfbc4fe608d3969c03b87feab",
    "verification/research/c11_emit_stationary_lean.py":
        "e75df59c361c0c657ba2994035e8332990d390b3",
}


class CertificateError(RuntimeError):
    def __init__(self, code: str, explanation: str):
        super().__init__(explanation)
        self.code = code


def strict_input(path: Path) -> dict:
    try:
        if path.stat().st_size > MAX_BYTES:
            raise CertificateError("INPUT_LIMIT", "C11 input exceeds 128 KiB")
        raw = path.read_bytes()
    except CertificateError:
        raise
    except OSError as exc:
        raise CertificateError("INPUT_READ", str(exc)) from exc
    if len(raw) > MAX_BYTES or raw.startswith(b"\xef\xbb\xbf"):
        raise CertificateError("INPUT_LIMIT", "invalid input encoding or byte budget")
    try:
        obj = strict_loads(raw)
    except (StationaryError, StationaryResourceLimit, ValueError) as exc:
        raise CertificateError("INPUT_JSON", str(exc)) from exc
    if type(obj) is not dict or type(obj.get("n")) is not int:
        raise CertificateError("INPUT_SCOPE", "supported input needs integer state count")
    if not (1 <= obj["n"] <= MAX_SUPPORTED_STATES):
        raise CertificateError("INPUT_SCOPE", "C11 v0.2.0 supports 1..6 finite states")
    return obj


def compute(raw: dict) -> tuple[dict, str]:
    try:
        report = execute(raw)
        if not verify_report(report):
            raise CertificateError("NUMERIC_INVALID", "independent C11 checker failed")
        source = emit_source(report)
    except CertificateError:
        raise
    except (StationaryError, StationaryResourceLimit, ValueError, ArithmeticError,
            OverflowError) as exc:
        raise CertificateError("NUMERIC_INVALID", str(exc)) from exc
    if report["normalized_input"]["n"] != raw["n"]:
        raise CertificateError("NUMERIC_INVALID", "input dimension changed")
    if not report["classes"]:
        raise CertificateError("NUMERIC_INVALID", "no certified bottom class")
    return report, source


def _git(*argv: str) -> bytes:
    try:
        p = subprocess.run(["git", *argv], cwd=ROOT, capture_output=True,
                           timeout=30, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise CertificateError("SOURCE_UNVERIFIED", "Git source inspection unavailable") from exc
    if p.returncode:
        raise CertificateError("SOURCE_UNVERIFIED", "Git object inspection failed")
    return p.stdout.strip()


def source_identity() -> dict[str, Any]:
    if Path(_git("rev-parse", "--show-toplevel").decode()).resolve() != ROOT:
        raise CertificateError("SOURCE_UNVERIFIED", "not executing in repository checkout")
    head = _git("rev-parse", "HEAD").decode()
    tree = _git("rev-parse", "HEAD^{tree}").decode()
    if not re.fullmatch("[0-9a-f]{40}", head) or not re.fullmatch("[0-9a-f]{40}", tree):
        raise CertificateError("SOURCE_UNVERIFIED", "invalid Git commit/tree identity")
    # No uncommitted/unknown source is allowed, including staged files.
    if _git("status", "--porcelain=v1", "-z", "--untracked-files=all"):
        raise CertificateError("SOURCE_UNVERIFIED", "dirty source tree")
    for path, expected in PINNED.items():
        if _git("rev-parse", "HEAD:" + path).decode() != expected:
            raise CertificateError("SOURCE_UNVERIFIED", "reviewed provider changed: " + path)
        if _git("hash-object", "--", path).decode() != expected:
            raise CertificateError("SOURCE_UNVERIFIED", "worktree provider changed: " + path)
    return {"head": head, "tree": tree, "pinned_providers": dict(PINNED)}


def expected_axiom_names(class_count: int) -> tuple[str, ...]:
    return tuple(
        [f"C11ReifiedFixture.member{i}_{suffix}"
         for i in range(class_count)
         for suffix in ("accepted", "share", "native", "native_observed")]
        + ["C11ReifiedFixture.completeFamily_accepted"])


def audit_axioms(stdout: str, class_count: int) -> dict[str, list[str]]:
    results = {}
    for name in expected_axiom_names(class_count):
        pattern = (rf"'{re.escape(name)}' "
                   rf"(does not depend on any axioms|depends on axioms: \[([^\]]*)\])")
        matches = re.findall(pattern, stdout)
        if len(matches) != 1:
            raise CertificateError("LEAN_AXIOM", "missing/duplicate axiom report for " + name)
        kind, members = matches[0]
        actual = [] if kind == "does not depend on any axioms" else [
            value.strip() for value in members.split(",") if value.strip()]
        if not set(actual) <= ALLOWED_AXIOMS:
            raise CertificateError("LEAN_AXIOM", "unexpected transitive axiom in " + name)
        results[name] = actual
    if "sorryAx" in stdout:
        raise CertificateError("LEAN_AXIOM", "proof placeholder axiom found")
    return results


def prepare_output(path: Path) -> Path:
    out = path.expanduser().resolve()
    if out == ROOT or ROOT in out.parents:
        raise CertificateError("OUTPUT_UNSAFE", "evidence must live outside repository")
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise CertificateError("OUTPUT_UNSAFE", "output directory must be fresh/empty")
    out.mkdir(parents=True, exist_ok=True)
    return out


def replay(source: str, class_count: int, out: Path) -> dict:
    evidence = source_identity()
    source_file = out / "C11ReifiedStationary.lean"
    source_file.write_text(source, encoding="utf-8")
    try:
        result = subprocess.run(["lake", "env", "lean", str(source_file)],
                                cwd=ROOT, timeout=LEAN_TIMEOUT, text=True,
                                capture_output=True, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise CertificateError("LEAN_UNAVAILABLE", "pinned Lean unavailable or timed out") from exc
    (out / "lean.stdout.txt").write_text(result.stdout, encoding="utf-8")
    (out / "lean.stderr.txt").write_text(result.stderr, encoding="utf-8")
    if result.returncode != 0 or re.search(r"(^|\n)error:", result.stdout + result.stderr):
        raise CertificateError("LEAN_REJECTED", "generated C11 Lean proof did not compile")
    axioms = audit_axioms(result.stdout, class_count)
    if source_identity() != evidence:
        raise CertificateError("SOURCE_UNVERIFIED", "source changed during Lean replay")
    return {"source": evidence, "source_sha256": sha256(source.encode("utf-8")).hexdigest(),
            "axioms": axioms, "compiler_exit": result.returncode}


def run_cli(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input", type=Path, help="strict rational C11 Markov matrix JSON")
    p.add_argument("--mode", choices=("numeric", "replay"), default="replay")
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args(argv)
    try:
        output = prepare_output(args.output)
        raw = strict_input(args.input)
        report, source = compute(raw)
        (output / "numeric_receipt.json").write_bytes(canonical_bytes(report) + b"\n")
        info: dict[str, Any] = {"format": FORMAT, "numeric_status": "EXACT_RATIONAL_VERIFIED",
            "lean_status": "NOT_EXECUTED", "scope": "REIFIED_FINITE_RATIONAL_C11",
            "input_sha256": report["input_sha256"],
            "bottom_classes": len(report["classes"]),
            "scientific_claims_verified": False,
            "empirical_identification": "NOT_IDENTIFIED", "source": None}
        if args.mode == "replay":
            info.update(replay(source, len(report["classes"]), output))
            info["lean_status"] = "KERNEL_CHECKED_REIFIED_STATIONARY_FAMILY"
        (output / "result.json").write_text(
            json.dumps(info, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        print(f"C11 {info['lean_status']} with {len(report['classes'])} genuine bottom classes")
        return 0
    except CertificateError as exc:
        print(f"{exc.code}: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(run_cli())
