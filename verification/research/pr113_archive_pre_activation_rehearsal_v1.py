"""Preactivation T/H rehearsal. NOT authentic active-30 T2/A2 source evidence.

Historical T runs the unchanged offline verifier; H runs the current 25-file
workflow tests; an independent exact-Git staged audit checks the virtual 30.
No original archive, protected workflow, reviewer or check-run is rewritten.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import sys
import tempfile
import traceback

from pr113_t2_execution_io_v1 import evidence_files, read_report

import pr113_dual_tooling_candidate_v2 as dual
from pr113_boundary_io import detached_destination
from pr113_tooling_migration_v2 import audit as tooling_audit
from pr113_tooling_migration import ROOT, T

FORMAT = "Permansson.PR113.ArchivePreactivationRehearsal.v1"
STATUS = "STAGED_25_T_H_VIRTUAL_30_REHEARSED_UNAPPROVED"
MAX_LOG_BYTES = 4 * 1024 * 1024


class RehearsalError(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise RehearsalError(message)


def _redacted_diagnostic(value):
    # A traceback's escaped source literal can put a word character before
    # a credential label, so matching must not require a leading word boundary.
    sensitive = re.compile(
        r"(?i)(?:(?:GITHUB_TOKEN|GH_TOKEN|ACCESS_TOKEN|API_KEY|"
        r"SECRET|PASSWORD|CREDENTIAL|AUTHORIZATION|COOKIE)\b\s*[:=]|"
        r"bearer\s+\S+|(?:github_pat_|gh[pousr]_)[A-Za-z0-9_]+)")
    return "\n".join(
        "[redacted credential-bearing diagnostic line]"
        if sensitive.search(line) else line for line in value.splitlines())


def validate_reports(old, new, profile, head):
    need(isinstance(profile, dict)
         and profile.get("format") == "Permansson.PR113.ToolingMigrationCandidate.v2"
         and profile.get("status") == "T2_EXACT_SOURCE_REVIEW_PENDING"
         and profile.get("source_commit_sha") == head
         and profile.get("reviewed_workflow_source_mode") == "staged"
         and profile.get("historical_original_workflow_count") == 25
         and profile.get("current_reviewed_workflow_count") == 30
         and profile.get("historical_packaged_tooling_files_verified") == 35
         and profile.get("historical_archive_unchanged") is True
         and profile.get("new_successor_T_approved") is False
         and profile.get("owner_activation_authorized") is False
         and profile.get("independent_security_review") is False,
         "virtual 30 is not a complete original/25-current staged source audit")
    deltas = profile.get("changed_canonical_tooling")
    expected = {"verification/integrity/workflow_contract.py",
                "verification/integrity/tests/test_workflow.py"}
    need(type(deltas) is list and len(deltas) == 2
         and all(type(row) is dict and
                 set(row) == {"path", "T_blob", "H_blob"}
                 and type(row["path"]) is str
                 and type(row["T_blob"]) is str
                 and type(row["H_blob"]) is str
                 and len(row["T_blob"]) == len(row["H_blob"]) == 40
                 and row["T_blob"] != row["H_blob"]
                 for row in deltas)
         and {row["path"] for row in deltas} == expected,
         "rehearsal profile did not bind exactly the two known T/H differences")
    try:
        checked = dual.validate_dual_reports(
            old, new, T_source=T, H_source=head)
    except (dual.DualToolingError, KeyError, TypeError) as exc:
        raise RehearsalError("real separate T and current 25 workflow executions failed") from exc
    need(checked["original_T_archive_offline_restoration_passed"] is True
         and checked["current_H_workflow_test_suite_passed"] is True,
         "one of the independent source legs was not successful")
    return {
        "format": FORMAT, "status": STATUS,
        "historical_T": T, "current_H": head,
        "historical_active_workflows": 25, "actual_active_workflows": 25,
        "virtual_staged_workflows": 30, "original_T_offline_replay": True,
        "current_25_workflow_tests": True, "virtual_30_profile_source_audit": True,
        "historical_supplement_tree": profile["historical_supplement_tree"],
        "historical_manifest_sha256": profile["historical_manifest_sha256"],
        "workflow_profile_sha256": profile["workflow_profile_sha256"],
        "known_two_source_deltas": profile["changed_canonical_tooling"],
        "active_30_reverified": False, "original_T2_producer_zip": False,
        "genuine_required_ci": False, "independent_security_review": False,
        "mathematical_acceptance": False, "owner_activation_authorized": False,
        "merge_authorized": False, "publication_authorized": False,
    }


def _trace(process, argv):
    out = getattr(process, "stdout", None)
    err = getattr(process, "stderr", None)
    need(type(process.returncode) is int and process.returncode == 0
         and type(out) is str and type(err) is str
         and len(out.encode()) <= MAX_LOG_BYTES
         and len(err.encode()) <= MAX_LOG_BYTES,
         "source child exited abnormally or produced unbounded logs")
    from hashlib import sha256
    return {"exit_code": 0, "command": argv,
            "stdout_sha256": sha256(out.encode()).hexdigest(),
            "stderr_sha256": sha256(err.encode()).hexdigest(),
            "non_authorizing": True}, out, err


def execute(original_checkout, current_checkout, head, output, *, stage=None):
    mark = stage if stage is not None else lambda value: None
    mark("SOURCE_CHECKOUTS")
    old = dual.checkout(original_checkout, T)
    current = dual.checkout(current_checkout, head)
    need(old != current and head != T, "T/H checkouts not independent")
    out = detached_destination(output, ROOT)
    need(not out.is_relative_to(old) and not out.is_relative_to(current)
         and not old.is_relative_to(out) and not current.is_relative_to(out),
         "rehearsal output overlaps either source checkout")
    mark("STAGED_PROFILE")
    profile = tooling_audit(current, head, phase="staged")
    need(profile.get("reviewed_workflow_source_mode") == "staged",
         "the archive rehearsal must not claim active 30")
    supplement = current/"archival/v0.2.0/supplement-1"
    need(supplement.is_dir() and not supplement.is_symlink(),
         "unchanged original T supplement unavailable")
    mark("EVIDENCE_PREPARATION")
    out.mkdir(parents=True, exist_ok=False)
    t_file, h_file = out/"historical_T_archive.json", out/"current_H_workflow.json"
    h_args = [sys.executable, "-B", "-m", "verification.integrity.run_tests",
              "--suite", "workflow", "--report", str(h_file)]
    with tempfile.TemporaryDirectory(prefix="pr113-T-rehearsal-") as scratch:
        t_args = [sys.executable, "-B", "-m", "verification.archive.offline_smoke",
                  "--supplement", str(supplement),
                  "--scratch", str(Path(scratch)/"restore"),
                  "--report", str(t_file)]
        mark("HISTORICAL_T")
        t_process = dual.command(t_args, old, historical_artifact=True,
                                 evidence_dir=out,evidence_label="T")
        t_trace, t_stdout, t_stderr = _trace(t_process, t_args)
    mark("CURRENT_H")
    h_process = dual.command(h_args, current, detached_current_suite=True,
                             evidence_dir=out,evidence_label="H")
    h_trace, h_stdout, h_stderr = _trace(h_process, h_args)
    mark("FINAL_SOURCE_AND_REPORT_CHECKS")
    dual.checkout(old, T)
    dual.checkout(current, head)
    need(tooling_audit(current, head, phase="staged") == profile,
         "T/H rehearsal source profile changed during verification")
    t_json = read_report(t_file)
    h_json = read_report(h_file)
    result = validate_reports(t_json, h_json, profile, head)
    result["historical_report_sha256"] = dual.sha_file(t_file)
    result["current_report_sha256"] = dual.sha_file(h_file)
    for name, data in (
        ("T_stdout.log", t_stdout), ("T_stderr.log", t_stderr),
        ("H_stdout.log", h_stdout), ("H_stderr.log", h_stderr),
    ):
        # Keep the legacy readable log names for nonempty output only.
        # The trace hashes still bind empty streams; zero-byte ZIP entries
        # are deliberately invalid at the downstream historical intake.
        if data:
            with (out/name).open("x", encoding="utf-8") as stream:
                stream.write(data)
    with (out/"STAGED_REHEARSAL_NOT_T2_AUTHORITY.json").open("x") as stream:
        json.dump(result, stream, sort_keys=True, indent=2)
        stream.write("\n")
    with (out/"unreviewed_process_trace.json").open("x") as stream:
        json.dump({"T": t_trace, "H": h_trace,
                   "independent_security_review": False}, stream,
                  sort_keys=True, indent=2)
        stream.write("\n")
    evidence_files(out, required=(
        "historical_T_archive.json", "current_H_workflow.json",
        "STAGED_REHEARSAL_NOT_T2_AUTHORITY.json", "unreviewed_process_trace.json"))
    return result


class OuterDiagnostics:
    """Detached startup/failure record, deliberately outside the inner packet."""

    def __init__(self, args, invocation=None):
        output = args.out.absolute().resolve()
        path = args.diagnostics or args.out.with_name(args.out.name + ".diagnostics")
        self.root = detached_destination(path, ROOT, forbidden=(
            args.historical_T_source, args.current_source, output))
        for source in (args.historical_T_source, args.current_source, output):
            need(not Path(source).resolve().is_relative_to(self.root),
                 "outer diagnostics must not contain source or evidence paths")
        self.root.mkdir(parents=True, exist_ok=False)
        self.record = {
            "format": "Permansson.PR113.PreactivationOuterExecution.v1",
            "status": "RUNNING", "stage": "STARTUP", "outer_exit": None,
            "historical_T": T, "declared_current_H": args.head,
            "historical_source": str(args.historical_T_source.resolve()),
            "current_source": str(args.current_source.resolve()),
            "inner_packet": str(output), "children": {},
            "argv": (list(sys.orig_argv) if invocation is None else
                     [sys.executable, str(Path(__file__).resolve()), *invocation]),
            "required_ci_accepted": False, "independent_security_review": False,
            "merge_authorized": False,
        }
        self.write()

    def write(self):
        (self.root / "outer.execution.json").write_text(
            json.dumps(self.record, sort_keys=True, indent=2) + "\n",
            encoding="utf-8")

    def stage(self, value):
        self.record["stage"] = value
        self.write()

    def finish(self, exit_code, error=None):
        self.record.update(outer_exit=exit_code,
                           status="COMPLETED_UNAPPROVED" if exit_code == 0 else "FAILED")
        for label in ("T", "H"):
            sidecar = Path(self.record["inner_packet"]) / (label + ".execution.json")
            if sidecar.is_file():
                try:
                    child = read_report(sidecar)
                    self.record["children"][label] = {
                        key: child.get(key) for key in ("returncode", "status", "failure_kind")}
                except (OSError, ValueError) as exc:
                    self.record["children"][label] = {"sidecar_error": type(exc).__name__}
        if error is not None:
            self.record["exception_type"] = type(error).__name__
            # Record the cause chain, but no environment dump or source locals.
            diagnostic = "".join(traceback.format_exception(
                type(error), error, error.__traceback__, limit=12))[-16384:]
            diagnostic = _redacted_diagnostic(diagnostic) + "\n"
            (self.root / "outer.stderr.log").write_text(diagnostic, encoding="utf-8")
        self.write()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--historical-T-source", type=Path, required=True)
    ap.add_argument("--current-source", type=Path, required=True)
    ap.add_argument("--head", required=True)
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--diagnostics", type=Path,
                    help="fresh detached outer logs (default: OUT.diagnostics)")
    a = ap.parse_args(argv)
    diagnostics = None
    try:
        diagnostics = OuterDiagnostics(a, invocation=argv)
        value = execute(a.historical_T_source, a.current_source, a.head, a.out,
                        stage=diagnostics.stage)
        diagnostics.finish(0)
        print(json.dumps({"status": value["status"], "required_ci_accepted": False},
                         sort_keys=True))
        return 0
    except (RehearsalError, dual.DualToolingError, OSError, ValueError,
            KeyError, TypeError) as exc:
        if diagnostics is not None:
            diagnostics.finish(2, exc)
        print("STAGED_T_H_REHEARSAL_BLOCKED:", _redacted_diagnostic(str(exc)), file=sys.stderr)
        return 2
    except Exception as exc:
        if diagnostics is not None:
            diagnostics.finish(1, exc)
        raise


if __name__ == "__main__":
    raise SystemExit(main())
