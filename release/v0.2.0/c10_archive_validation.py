"""Recheck preserved C10 archive contents without claiming a new Lean run.

The accepted source-bound GitHub workflow remains the execution trust root.
This gate reuses the original independent C10 structural/arithmetic checker,
regenerates both Lean inputs, and rejects inconsistent compiler captures.
It does not compile Lean or turn a self-reported transcript into execution proof.
Publisher ZIPs are read only; canonical Git bytes avoid checkout-EOL dependence.
"""
from __future__ import annotations

from contextlib import contextmanager
from hashlib import sha256
import importlib
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory
import zipfile


class C10ArchiveError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise C10ArchiveError(message)


@contextmanager
def authoritative_checker(root):
    research = Path(root).resolve() / "verification/research"
    sys.path.insert(0, str(research))
    try:
        checker = importlib.import_module("c10_verify_release_evidence")
        evidence = importlib.import_module("c10_release_evidence")
        require(Path(checker.__file__).resolve() == research / "c10_verify_release_evidence.py",
                "C10 structural checker was imported from another source tree")
        require(Path(evidence.__file__).resolve() == research / "c10_release_evidence.py",
                "C10 evidence contract was imported from another source tree")
        yield checker, evidence
    finally:
        sys.path.remove(str(research))


def git_blob(root, revision, path):
    command = ["git", "-C", str(root), "show", f"{revision}:{path}"]
    done = subprocess.run(command, capture_output=True, timeout=30, check=False)
    require(done.returncode == 0, "Cannot read canonical C10 specification Git blob")
    return done.stdout


_REPORT = re.compile(
    r"'([^'\r\n]+)' (?:does not depend on any axioms|depends on axioms: \[[^\]]*\])"
)
_CAPTURED_WARNING = (
    "warning: manifest out of date: git url of dependency 'mathlib' changed; "
    "use `lake update mathlib` to update it\n"
)


def compiler_capture(stdout, stderr, theorems, evidence):
    """Require complete axiom output and no compiler failure/extra diagnostics.

    Empty stderr or the historically captured Lake URL warning are recognized.
    The warning is preserved, never followed as an instruction to update pins.
    Successful execution itself is supplied by the accepted workflow receipt.
    """
    try:
        out, err = stdout.decode("utf-8"), stderr.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise C10ArchiveError("Compiler capture is not UTF-8") from exc
    require(err in {"", _CAPTURED_WARNING}, "Unexpected compiler stderr/failed execution")
    reports = evidence.axiom_reports(out, theorems)
    matches = list(_REPORT.finditer(out))
    require(len(matches) == len(theorems)
            and {match.group(1) for match in matches} == set(theorems),
            "Compiler transcript theorem inventory differs from declared proof")
    require(not _REPORT.sub("", out).strip(),
            "Compiler transcript contains errors or unexpected non-axiom output")
    return reports


def preflight_c10_zip(zipped: zipfile.ZipFile, root: Path) -> set[str]:
    """Check the complete fixed inventory and size budgets before reading data.

    This function inspects central-directory metadata only. Every caller that
    reads C10 ZIP members must run this shared gate before its first member read.
    """
    with authoritative_checker(root) as (_, evidence):
        names = {*evidence.ARTIFACTS, "evidence_manifest.json"}
    entries = zipped.infolist()
    require(len(entries) == len(names) and {entry.filename for entry in entries} == names,
            "C10 ZIP fixed artifact inventory is incomplete, duplicated or extended")
    require(all(not entry.is_dir() and entry.file_size <= 4_000_000 for entry in entries)
            and sum(entry.file_size for entry in entries) <= 16_000_000,
            "C10 ZIP exceeds the bounded six-state evidence size")
    return names


def validate_c10_archive(archive: Path, expected_source: dict, root: Path) -> dict:
    """Validate a publisher ZIP after its independently trusted origin binding.

    ``expected_source`` has repository, pr_number, head_sha, base_sha and
    synthetic_merge_sha. The caller must independently authenticate publisher
    identity/hash/workflow and source parents; archive metadata cannot do that.
    No original ZIP bytes or repository files are rewritten.
    """
    root, archive = Path(root).resolve(), Path(archive)
    require(set(expected_source) == {"repository", "pr_number", "head_sha", "base_sha",
                                     "synthetic_merge_sha"}, "Invalid C10 source context")
    require(expected_source["repository"] == "HMarcusWH/PermanssonLean"
            and type(expected_source["pr_number"]) is int and expected_source["pr_number"] > 0,
            "Invalid C10 repository or PR")
    require(all(re.fullmatch(r"[0-9a-f]{40}", expected_source.get(key, ""))
                for key in ("head_sha", "base_sha", "synthetic_merge_sha")),
            "Invalid C10 source SHA")
    try:
        with authoritative_checker(root) as (checker, evidence):
            with zipfile.ZipFile(archive) as zipped:
                names = preflight_c10_zip(zipped, root)
                payloads = {name: zipped.read(name) for name in names}
            specification = git_blob(root, expected_source["head_sha"], evidence.SPEC_PATH)
            spec_oid = subprocess.run(
                ["git", "-C", str(root), "rev-parse",
                 f"{expected_source['head_sha']}:{evidence.SPEC_PATH}"],
                capture_output=True, text=True, timeout=30, check=False,
            )
            require(spec_oid.returncode == 0 and spec_oid.stdout.strip() == evidence.FROZEN_SPEC_BLOB,
                    "C10 specification differs from the immutable audited Git blob")
            with TemporaryDirectory(prefix="permansson-c10-archive-") as temporary:
                staging = Path(temporary)
                files, canonical_root = staging / "bundle", staging / "source"
                files.mkdir()
                spec_file = canonical_root / evidence.SPEC_PATH
                spec_file.parent.mkdir(parents=True)
                spec_file.write_bytes(specification)
                for name, payload in payloads.items():
                    (files / name).write_bytes(payload)
                # This compares the ENTIRE fixed manifest, independently verifies
                # raw/normalized/receipt/mixed arithmetic, and regenerates BOTH
                # Lean sources. It deliberately does not rerun the compiler.
                checker.verify_bundle_structure(files, expected_source, canonical_root)
                point = compiler_capture(payloads["lean_check.stdout.txt"],
                                         payloads["lean_check.stderr.txt"], evidence.THEOREMS, evidence)
                mixed = compiler_capture(payloads["mixed_check.stdout.txt"],
                                         payloads["mixed_check.stderr.txt"], checker.MIXED_PROOFS, evidence)
            return {"status": "pass", "source": expected_source,
                    "publisher_zip_sha256": sha256(archive.read_bytes()).hexdigest(),
                    "structural_and_exact_arithmetic": "pass",
                    "generated_lean_matches_receipts": "pass",
                    "captured_compiler_result": "consistent_success",
                    "point_theorems": point, "mixed_theorems": mixed,
                    "compiler_rerun": False,
                    "execution_trust_root": "independently accepted source-bound GitHub workflow"}
    except C10ArchiveError:
        raise
    except (ValueError, KeyError, TypeError, OSError, zipfile.BadZipFile,
            subprocess.TimeoutExpired) as exc:
        raise C10ArchiveError(f"C10 archived proof evidence rejected: {exc}") from exc
