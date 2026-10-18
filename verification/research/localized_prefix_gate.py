"""Fresh A2-P02 compiler/signature/axiom/semantic-mutation gate.

Imported by test_localized_prefix_compiler.py in unchanged Research CI discovery.
Also runnable directly. No test discovery is called here (avoids recursive CI).
All evidence is written OUTSIDE the repository into a fresh or empty directory.
No compiler, wrong source, timeout or wrong failure mode => FAIL_CLOSED.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any

if __package__:
    from . import localized_prefix_support as support
else:
    import localized_prefix_support as support

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
DECLS = tuple("PermanssonResearch.Probability." + x for x in (
    "goodHistoryMajorant", "canonicalPrefixKernel", "canonicalPrefixKernel_isMarkov",
    "mixedFinitePrefixLaw", "mixedFinitePrefixLaw_isProbability",
    "goodHistoryMajorant_measurable", "goodHistoryMajorant_nonneg", "goodHistoryMajorant_le_one",
    "goodHistory_lintegral_le", "historyEvolution_tv_le_goodVisits",
    "finitePrefixLaw_tv_le_averaged", "finitePrefixLaw_tv_le_goodVisits",
    "finitePathExpectation_abs_le_goodVisits", "canonicalPrefixKernel_apply",
    "mixedFinitePrefixLaw_dirac", "mixedFinitePrefixLaw_tv_le_initial",
    "finitePrefixLaw_tv_le_goodVisits_initial", "finitePathExpectation_abs_le_goodVisits_initial",
)) + ("PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors",) + tuple("PermanssonResearch.ConstitutiveQuasi.LocalizedProtocolErrors." + x for x in (
    "baselineBudget", "interventionBudget", "baselineBudget_nonneg", "interventionBudget_nonneg", "toConstitutiveOutputErrors",
    "reportedMargin_abs_le", "trueMargin_pos_of_reported", "reportedMargin_pos_of_true",
)) + tuple("PermanssonResearch.ConstitutiveQuasi.LocalizedExamples." + x for x in (
    "reportingProfile", "matchedPair", "reportedEffect_four_fifths", "initialScore",
    "exactLocalizedErrors", "reportedMargin_four_fifths", "localizedBudget_total_one_fifth",
    "originalMargin_ge_three_fifths", "originalMargin_positive",
    "cannot_omit_baseline_report_error", "cannot_omit_treatment_report_error",
    "initialScore_point", "initialMismatch_gap_one",
))
FIXTURE = support.LIBRARIES[-1]
MUTATIONS = {
    "omit_baseline_reporting_error": ("  reportBase := 1 / 10\n", "  reportBase := 0\n"),
    "omit_treated_reporting_error": ("  reportTreated := 1 / 10\n", "  reportTreated := 0\n"),
    "wrong_reported_effect": (
        "perturbedConstitutiveEffect reportingProfile y = 4 / 5 := by",
        "perturbedConstitutiveEffect reportingProfile y = 3 / 4 := by"),
    "omit_zero_horizon_initial_error": (
        "(mixedFinitePrefixLaw (Kernel.id : Kernel Bool Bool) (Measure.dirac true) 0)| = 1 := by",
        "(mixedFinitePrefixLaw (Kernel.id : Kernel Bool Bool) (Measure.dirac true) 0)| = 0 := by"),
}


def parse_version(text: str) -> str:
    found = re.findall(r"\bversion\s+([^,\s)]+)", text)
    if found != ["4.34.0"]:
        raise support.GuardError(f"expected exact Lean release 4.34.0, got {text.strip()!r}")
    return found[0]


def parse_axioms(text: str, names: tuple[str, ...] = DECLS) -> dict[str, list[str]]:
    normalized = re.sub(r"\.\{[^{}\n]*\}", "", text)
    pattern = re.compile(
        r"['`]?([A-Za-z_][A-Za-z0-9_.]*)['`]?\s+"
        r"(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
    out: dict[str, list[str]] = {}
    for match in pattern.finditer(normalized):
        name, atoms = match.groups()
        if name not in names: raise support.GuardError(f"unexpected axiom declaration: {name}")
        if name in out: raise support.GuardError(f"duplicate axiom record: {name}")
        axioms = [] if atoms is None else [a.strip() for a in atoms.split(",") if a.strip()]
        if not set(axioms) <= ALLOWED_AXIOMS:
            raise support.GuardError(f"prohibited transitive axiom for {name}: {axioms}")
        out[name] = sorted(set(axioms))
    if set(out) != set(names):
        raise support.GuardError(f"missing axiom records: {sorted(set(names) - set(out))}")
    return out


def semantic_rejection(returncode: int, output: str) -> bool:
    if returncode == 0: return False
    if returncode < 0: raise support.GuardError("mutant terminated by signal, not a proof rejection")
    bad = ("unknown identifier", "unknown constant", "unknown module", "unknown package",
           "unexpected token", "file not found", "no such file", "object file", "out of memory",
           "maximum recursion depth", "deterministic timeout", "heartbeat", "timed out",
           "failed to synthesize", "failed to import", "invalid import")
    low = output.lower()
    if any(t in low for t in bad):
        raise support.GuardError("mutant failed for parser/import/resource/interface reasons")
    if not re.search(r"unsolved goals|type mismatch|tactic[^\n]*(?:failed|failure)|failed to prove", low):
        raise support.GuardError("mutant lacked a recognized semantic proof diagnostic")
    return True


def mutated_source(source: str, name: str) -> str:
    before, after = MUTATIONS[name]
    if source.count(before) != 1:
        raise support.GuardError(f"semantic mutation target missing or duplicated: {name}")
    return source.replace(before, after, 1)


def check_dependencies(repo: Path) -> dict[str, str]:
    manifest = support.strict_json(support.read_member(repo, "lake-manifest.json").decode("utf-8"))
    if manifest.get("packagesDir") != ".lake/packages":
        raise support.GuardError("unexpected dependency directory")
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        raise support.GuardError("dependency manifest is empty")
    found: dict[str, str] = {}
    for package in packages:
        if package.get("type") != "git": raise support.GuardError("non-Git dependency not supported")
        name, rev = package["name"], package["rev"]
        support.safe_relative(name)
        if "/" in name or name in found: raise support.GuardError("bad/duplicate package name")
        if not re.fullmatch(r"[0-9a-f]{40}", rev): raise support.GuardError("dependency is not commit pinned")
        path = repo / ".lake/packages" / name
        if not path.is_dir(): raise support.GuardError(f"pinned dependency checkout missing: {name}")
        actual = support.git_text(path, "rev-parse", "HEAD")
        if actual != rev: raise support.GuardError(f"dependency revision mismatch: {name}")
        if support.git_bytes(path, "status", "--porcelain=v1", "--untracked-files=all"):
            raise support.GuardError(f"dependency source is dirty: {name}")
        found[name] = actual
    if found.get("mathlib") != support.MATHLIB_REV:
        raise support.GuardError("mathlib is not the audited exact revision")
    return found


def prepare_output(repo: Path, output: Path) -> Path:
    output = output.resolve()
    if output == repo or output.is_relative_to(repo):
        raise support.GuardError("evidence output must be outside the repository")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise support.GuardError("evidence output must be fresh or empty; historical logs are not overwritten")
    output.mkdir(parents=True, exist_ok=True)
    return output


def verify(repo: Path, output: Path, *, mode: str = "full", timeout: int = 3600) -> dict[str, Any]:
    repo = repo.resolve(strict=True)
    output = prepare_output(repo, output)
    report: dict[str, Any] = {"format": "Permansson.A2P02.CompilerReceipt.v2",
        "contract": support.CONTRACT, "mode": mode, "status": "NOT_RUN",
        "started_at": datetime.now(timezone.utc).isoformat(), "commands": [],
        "mutations": {}, "declarations": {}, "event_binding": "LOCAL_NOT_H_B_S_M_CI",
        "scope": "Source/compiler evidence only, not empirical or Exact-GR certification"}
    before: dict[str, Any] | None = None
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["LAKE_NO_CACHE"] = "1"  # no remote project build-cache replacement
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN", "LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN"):
        environment.pop(key, None)

    def run(label: str, args: list[str], *, negative: bool = False, seconds: int = timeout) -> tuple[int, str]:
        started = time.monotonic()
        entry: dict[str, Any] = {"label": label, "argv": args, "timeout_seconds": seconds}
        report["commands"].append(entry)
        try:
            p = subprocess.run(args, cwd=repo, env=environment, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=seconds)
            raw = p.stdout
            code = p.returncode
        except subprocess.TimeoutExpired as exc:
            raw = (exc.stdout or b"") + b"\nGATE_TIMEOUT\n"
            code = -999
        except OSError as exc:
            raw, code = str(exc).encode(), -998
        log = f"{len(report['commands']):02d}_{label}.log"
        (output / log).write_bytes(raw)
        entry.update(returncode=code, log=log, log_sha256=support.sha256(raw),
                     elapsed_seconds=round(time.monotonic() - started, 3))
        text = raw.decode("utf-8", "replace")
        if code in (-999, -998) or (code != 0 and not negative):
            raise support.GuardError(f"{label} failed ({code}): {text[-6000:]}")
        return code, text

    try:
        if mode not in {"full", "focused"}: raise support.GuardError("unsupported gate mode")
        if type(timeout) is not int or timeout <= 0: raise support.GuardError("invalid timeout")
        before = support.inspect_repo(repo)
        report["source"] = {k: v for k, v in before.items() if k != "files"}
        (output / "source_before.json").write_text(json.dumps(before, indent=2, sort_keys=True) + "\n")
        if support.read_member(repo, "lean-toolchain").decode().strip() != support.TOOLCHAIN:
            raise support.GuardError("compiler pin changed")
        if shutil.which("lake") is None:
            raise support.GuardError("Lean/Lake unavailable; no compiler certification performed")
        _, version = run("compiler_version", ["lake", "env", "lean", "--version"], seconds=180)
        report["compiler"] = {"version": parse_version(version), "raw": version.strip()}
        # Do not permit a build to silently substitute already-present dirty dependencies.
        report["dependencies"] = check_dependencies(repo)
        run("research_build", ["lake", "build", "PermanssonResearch"])
        if mode == "full": run("original_default_build", ["lake", "build"])
        # Explicitly elaborate all four final source files, even after an incremental build.
        for i, source in enumerate(support.LIBRARIES, 1):
            run(f"source_{i}", ["lake", "env", "lean", source])
        audit = "import PermanssonResearch\nset_option pp.universes true\n" + "\n".join(
            f"#check @{name}\n#print axioms {name}" for name in DECLS) + "\n"
        audit_file = output / "AuditSignatures.lean"
        audit_file.write_text(audit, encoding="utf-8")
        _, signature_log = run("signatures_axioms", ["lake", "env", "lean", str(audit_file)])
        report["declarations"] = parse_axioms(signature_log)
        # This is a recompiled positive control using the same imports as each mutant.
        source = support.read_member(repo, FIXTURE).decode("utf-8")
        positive = output / "PositiveControl.lean"
        positive.write_text(source, encoding="utf-8")
        run("positive_fixture", ["lake", "env", "lean", str(positive)])
        for name in MUTATIONS:
            mutation = mutated_source(source, name)
            file = output / (name + ".lean")
            file.write_text(mutation, encoding="utf-8")
            code, text = run(name, ["lake", "env", "lean", str(file)], negative=True, seconds=300)
            if not semantic_rejection(code, text):
                raise support.GuardError(f"false mathematical mutation accepted: {name}")
            report["mutations"][name] = {"status": "SEMANTICALLY_REJECTED",
                "positive_source_sha256": support.sha256(source.encode()),
                "mutant_source_sha256": support.sha256(mutation.encode())}
        report["dependencies_after"] = check_dependencies(repo)
        after = support.inspect_repo(repo)
        if any(before[key] != after[key] for key in ("source_digest", "git_head", "git_head_tree", "git_status")):
            raise support.GuardError("source, HEAD or index changed during verification")
        report["source_unchanged"] = True
        report["status"] = "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING"
    except Exception as exc:
        report["status"] = "FAIL_CLOSED"
        report["reason"] = str(exc)
        if before is not None:
            try:
                after = support.inspect_repo(repo)
                report["source_unchanged"] = (before["source_digest"] == after["source_digest"])
            except Exception as post:
                report["source_unchanged"] = False
                report["postcheck_error"] = str(post)
    report["finished_at"] = datetime.now(timezone.utc).isoformat()
    # Receipts name and hash all generated files except themselves (no circular hash).
    report["artifacts"] = {p.name: {"bytes": p.stat().st_size, "sha256": support.sha256(p.read_bytes())}
                           for p in sorted(output.iterdir()) if p.is_file()}
    (output / "receipt.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--mode", choices=("focused", "full"), default="full")
    args = parser.parse_args()
    try:
        report = verify(args.repo, args.output, mode=args.mode)
        print(json.dumps(report, indent=2, sort_keys=True))
    except Exception as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        raise SystemExit(2)
    if report["status"] == "FAIL_CLOSED": raise SystemExit(2)


if __name__ == "__main__":
    main()
