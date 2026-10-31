"""Owner-engineering archive successor contract v1 (`archive-reproducibility`).

The original v0.2.0 verifier requires the complete integrity/archive tooling
closure of the current source C to equal the historical snapshot T. Two
integrity files changed after T, so that equality cannot hold again without
rewriting history. This versioned contract replaces that one comparison for
the existing 25-workflow profile. It does not edit the historical verifier,
the archive, any recorded hash or the staged 30-workflow candidate.

1. Historical T: T's own unchanged `verification.archive.offline_smoke` runs
   from a fresh, clean checkout of T in standalone mode, with its own nonroot
   network-namespace isolation, on the committed supplement. Standalone mode
   compares the supplement's packaged tooling with the code that executes, so
   a PASS also shows that T's code ran, not C's.
2. Current C: C is the checkout HEAD with no modified tracked files; T and the
   accepted base B are ancestors; the whole `archival/v0.2.0` tree is the one
   accepted at B; the 35-file packaged T closure is byte-exact; the closure
   differs from T in exactly the two approved files, at exactly the approved
   blobs; the workflow set is the reviewed 25 (`pr113_tooling_migration`); and
   C's own workflow integrity suite passes.
3. Approval: `archive_successor_policy_v1.json` records an owner engineering
   policy that takes effect only through the owner's merge into main. Nothing
   in it is an independent security review, a PR #113 approval or a
   certification. The PR #113 final-head archive failure stays recorded and is
   not required to have succeeded.

Every other difference fails closed.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(1, str(ROOT))

import pr113_tooling_migration as tooling  # noqa: E402
from verification.integrity.reports import (  # noqa: E402
    HardeningError, check_report, strict_json, write_report)

POLICY = Path(__file__).with_name("archive_successor_policy_v1.json")
POLICY_FORMAT = "Permansson.ArchiveSuccessor.OwnerEngineeringPolicy.v1"
CONTRACT = "Permansson.ArchiveSuccessor.Contract.v1"
ARCHIVAL = "archival/v0.2.0"
SHA40 = re.compile(r"^[0-9a-f]{40}$")
# The standalone stage list of the original verifier (no committed publication:
# the publication binding is the archival tree identity with B, checked on C).
STANDALONE_STAGES = ["delivered_inventory", "tooling_closure", "original_evidence", "empty_import",
                     "strict_fsck", "exact_objects_refs", "parents_trees_ancestry", "canonical_checkout",
                     "369_pins", "exact_tex", "legacy_replay", "post_replay_hashes"]
ACCEPTED = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
ACCEPTED_TREE = "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
# Both legs must end, and report, inside the job's 25-minute limit.
HISTORICAL_TIMEOUT = 1200
CURRENT_TIMEOUT = 300
MAX_STREAM = 1 << 20
POLICY_KEYS = {"format", "authority", "owner", "independent_security_review", "effective_by", "statement",
               "scope", "historical_T", "accepted_base_B", "archival_tree_at_B", "workflow_count",
               "approved_tooling_changes", "preactivation_25_head", "approved_workflow_changes",
               "historical_record"}
PREACTIVATION_25_HEAD = "5189f0c4a0db7535d57a9ff2a7aef6a3e76191b6"
ARCHIVE_WORKFLOW = ".github/workflows/research-integrity.yml"
_SECRET = ("TOKEN", "PASSWORD", "COOKIE", "SECRET", "AUTHORIZATION", "CREDENTIAL")


def fail(code: str, message: str, exit_code: int = 1):
    raise HardeningError(code, message, exit_code)


def need(condition: bool, code: str, message: str) -> None:
    if not condition:
        fail(code, message)


def check_policy(policy: object) -> dict:
    """The owner-engineering record: exact shape, never an independent review."""
    need(isinstance(policy, dict) and set(policy) == POLICY_KEYS, "E_SUCCESSOR_POLICY",
         "policy has missing or unknown fields")
    need(policy["format"] == POLICY_FORMAT and policy["authority"] == "OWNER_ENGINEERING_POLICY"
         and policy["owner"] == "HMarcusWH", "E_SUCCESSOR_POLICY", "policy format, authority or owner differs")
    need(policy["independent_security_review"] is False, "E_SUCCESSOR_POLICY",
         "an owner engineering policy cannot claim an independent security review")
    need(policy["historical_T"] == tooling.T and policy["accepted_base_B"] == tooling.B
         and isinstance(policy["archival_tree_at_B"], str) and SHA40.fullmatch(policy["archival_tree_at_B"])
         and policy["workflow_count"] == 25, "E_SUCCESSOR_POLICY", "policy T, B, archival tree or workflow count differs")
    changes = policy["approved_tooling_changes"]
    need(isinstance(changes, list) and all(
        isinstance(row, dict) and set(row) == {"path", "T_blob", "approved_blob"}
        and all(isinstance(row[k], str) and SHA40.fullmatch(row[k]) for k in ("T_blob", "approved_blob"))
        and row["T_blob"] != row["approved_blob"] for row in changes), "E_SUCCESSOR_POLICY",
        "approved tooling changes are malformed")
    paths = [row["path"] for row in changes]
    need(len(paths) == len(set(paths)) and set(paths) == set(tooling.EXPECTED_CHANGES), "E_SUCCESSOR_POLICY",
         "approved tooling changes must name exactly the two reviewed integrity files")
    workflows = policy["approved_workflow_changes"]
    need(policy["preactivation_25_head"] == PREACTIVATION_25_HEAD and isinstance(workflows, list)
         and len(workflows) == 1 and isinstance(workflows[0], dict)
         and set(workflows[0]) == {"path", "preactivation_blob", "approved_blob"}
         and workflows[0]["path"] == ARCHIVE_WORKFLOW
         and all(isinstance(workflows[0][k], str) and SHA40.fullmatch(workflows[0][k])
                 for k in ("preactivation_blob", "approved_blob"))
         and workflows[0]["preactivation_blob"] != workflows[0]["approved_blob"], "E_SUCCESSOR_POLICY",
         "the only approved workflow change must be the archive job in research-integrity.yml")
    need(isinstance(policy["historical_record"], dict) and all(
        isinstance(v, (str, int)) and not isinstance(v, bool) for v in policy["historical_record"].values()),
        "E_SUCCESSOR_POLICY", "historical record must be plain recorded values")
    return {row["path"]: (row["T_blob"], row["approved_blob"]) for row in changes}


def load_policy(path: Path = POLICY) -> tuple[dict, str]:
    raw = path.read_bytes()
    policy = strict_json(raw, "E_SUCCESSOR_POLICY")
    check_policy(policy)
    return policy, sha256(raw).hexdigest()


def _git_env() -> dict:
    # Inherited Git redirection (GIT_DIR, GIT_CONFIG_*, ...) must not choose objects.
    return {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def git(repo: Path, *args: str) -> str:
    done = subprocess.run(["git", *args], cwd=repo, env=_git_env(), capture_output=True, timeout=120)
    need(done.returncode == 0, "E_SUCCESSOR_SOURCE", "git " + " ".join(args[:2]) + " failed: "
         + done.stderr.decode("utf-8", "replace")[-300:])
    return done.stdout.decode("utf-8").strip()


def source_audit(repo: Path, candidate: str, policy: dict) -> dict:
    """Current C, T and B as Git objects; the closure delta is exactly the approved one."""
    approved = check_policy(policy)
    need(isinstance(candidate, str) and SHA40.fullmatch(candidate), "E_SUCCESSOR_SOURCE", "invalid candidate SHA")
    need(git(repo, "rev-parse", "HEAD") == candidate, "E_SUCCESSOR_SOURCE", "candidate is not the checkout HEAD")
    need(git(repo, "status", "--porcelain", "--untracked-files=no") == "", "E_SUCCESSOR_SOURCE",
         "tracked files differ from the candidate commit")
    need(git(repo, "status", "--porcelain", "--untracked-files=all", "--", ARCHIVAL) == "", "E_SUCCESSOR_SOURCE",
         "untracked files inside the archival tree")
    try:
        audit = tooling.audit(repo, candidate)
    except tooling.ToolingMigrationError as exc:
        fail("E_SUCCESSOR_SOURCE", "T/B/C source audit rejected: " + str(exc))
    archival = git(repo, "rev-parse", candidate + ":" + ARCHIVAL)
    need(archival == git(repo, "rev-parse", tooling.B + ":" + ARCHIVAL) == policy["archival_tree_at_B"],
         "E_SUCCESSOR_SOURCE", "archival tree differs from the one accepted at B")
    delta = {row["path"]: (row["T_blob"], row["H_blob"]) for row in audit["changed_canonical_tooling"]}
    need(delta == approved, "E_SUCCESSOR_DELTA",
         "closure delta differs from the owner-approved blobs: " + json.dumps(sorted(delta)))
    need(audit["current_workflow_file_count"] == policy["workflow_count"], "E_SUCCESSOR_SOURCE",
         "workflow inventory differs from the reviewed 25")
    workflow = policy["approved_workflow_changes"][0]
    need(git(repo, "rev-parse", PREACTIVATION_25_HEAD + ":" + ARCHIVE_WORKFLOW) == workflow["preactivation_blob"]
         and git(repo, "rev-parse", candidate + ":" + ARCHIVE_WORKFLOW) == workflow["approved_blob"],
         "E_SUCCESSOR_DELTA", "the archive workflow is not the owner-approved change of the preactivation 25")
    return {"candidate": candidate, "candidate_tree": git(repo, "rev-parse", candidate + "^{tree}"),
            "historical_T": tooling.T, "accepted_base_B": tooling.B, "archival_tree": archival,
            "historical_supplement_tree": audit["historical_supplement_tree"],
            "historical_manifest_sha256": audit["historical_manifest_sha256"],
            "historical_packaged_tooling_files_verified": audit["historical_packaged_tooling_files_verified"],
            "approved_closure_delta": [{"path": p, "T_blob": t, "C_blob": c} for p, (t, c) in sorted(delta.items())],
            "workflow_count": audit["current_workflow_file_count"]}


def historical_environment(base: dict | None = None) -> dict:
    """T runs as an accepted-artifact replay: no CI, Git, token or import redirection."""
    env = {k: v for k, v in (os.environ if base is None else base).items()
           if not k.startswith(("GITHUB_", "GIT_", "GH_", "ACTIONS_", "RUNNER_", "PERMANSSON_"))
           and k not in {"PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP", "CI"}
           and not any(word in k.upper() for word in _SECRET)}
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def run_bounded(command: list[str], cwd: Path, env: dict, timeout: int) -> tuple[int, bytes, bytes]:
    """A new session; on timeout the whole process group is killed."""
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=out,
                                   stderr=err, close_fds=True, start_new_session=True)
        try:
            process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            fail("E_SUCCESSOR_TIMEOUT", f"{command[3] if len(command) > 3 else command[0]} exceeded {timeout} s")
        out.seek(0)
        err.seek(0)
        return process.returncode, out.read(MAX_STREAM), err.read(MAX_STREAM)


def checkout_historical(repo: Path, destination: Path) -> Path:
    """A fresh, clean, detached checkout of T from the candidate's own object store."""
    need(not destination.exists(), "E_SUCCESSOR_SOURCE", "historical checkout path already exists")
    git(repo, "clone", "--quiet", "--no-checkout", "--no-hardlinks", str(repo), str(destination))
    git(destination, "checkout", "--quiet", "--detach", tooling.T)
    verify_historical_checkout(destination)
    return destination


def verify_historical_checkout(checkout: Path) -> None:
    need(git(checkout, "rev-parse", "HEAD") == tooling.T
         and git(checkout, "rev-parse", "HEAD^{tree}") == git(checkout, "rev-parse", tooling.T + "^{tree}")
         and git(checkout, "status", "--porcelain", "--untracked-files=all") == "",
         "E_SUCCESSOR_HISTORICAL", "historical T checkout is not the clean T commit")


def validate_historical_report(raw: bytes, returncode: int) -> dict:
    """T's own standalone report: PASS, isolated, T-bound, accepted-artifact scope only."""
    report = strict_json(raw, "E_SUCCESSOR_HISTORICAL")
    need(isinstance(report, dict) and report.get("format") == "Permansson.Hardening.Check.v1"
         and report.get("check") == "archive-reproducibility", "E_SUCCESSOR_HISTORICAL",
         "historical T report has the wrong format")
    status = report.get("status")
    if status == "BLOCKED":
        fail(str(report.get("error_code") or "E_OFFLINE_UNAVAILABLE"),
             "historical T replay blocked: " + str(report.get("message"))[:600], 3)
    need(status == "PASS" and report.get("error_code") is None and returncode == 0, "E_SUCCESSOR_HISTORICAL",
         "historical T replay did not pass: " + str(report.get("error_code")) + " " + str(report.get("message"))[:600])
    # check_report nests the verifier's fields under `details`; stages stay top-level.
    details = report.get("details") if isinstance(report.get("details"), dict) else {}
    tool = details.get("tooling") if isinstance(details.get("tooling"), dict) else {}
    isolation = details.get("isolation") if isinstance(details.get("isolation"), dict) else {}
    publication = details.get("publication") if isinstance(details.get("publication"), dict) else {}
    need(report.get("completed_stages") == STANDALONE_STAGES == details.get("completed_stages")
         and details.get("acceptance_scope") == "accepted_artifact_replay_only"
         and details.get("replay_target") == ACCEPTED and details.get("replay_tree") == ACCEPTED_TREE
         and details.get("source_restore") == "PASS" and details.get("artifact_replay") == "PASS"
         and tool.get("binding") == "standalone_content_hashes_only" and tool.get("source_commit") == tooling.T
         and tool.get("files") == 35 and tool.get("reproduction_instructions_match") is True
         and publication.get("status") == "NOT_APPLICABLE"
         and isolation.get("network_isolation") == "ENFORCED", "E_SUCCESSOR_HISTORICAL",
         "historical T report is not an isolated, T-bound standalone replay")
    return {"status": "PASS", "binding": tool["binding"], "source_commit": tool["source_commit"],
            "tooling_files": tool["files"], "completed_stages": report["completed_stages"],
            "network_isolation": isolation["network_isolation"], "replay_target": details["replay_target"],
            "report_sha256": sha256(raw).hexdigest()}


def validate_current_report(raw: bytes, returncode: int) -> dict:
    report = strict_json(raw, "E_SUCCESSOR_CURRENT")
    need(isinstance(report, dict) and report.get("status") == "PASS" and returncode == 0
         and report.get("suite") == "workflow" and isinstance(report.get("methods_run"), int)
         and report["methods_run"] > 0 and report.get("skips") == 0 and report.get("failures") == 0
         and report.get("errors") == 0, "E_SUCCESSOR_CURRENT",
         "current C workflow integrity suite did not pass completely: " + str(report.get("message"))[:600])
    return {"status": "PASS", "suite": "workflow", "methods_run": report["methods_run"],
            "report_sha256": sha256(raw).hexdigest()}


def _fresh(path: Path, others: list[Path], label: str) -> Path:
    path = path.absolute()
    need(not path.is_symlink() and (not path.exists() or (path.is_dir() and not any(path.iterdir()))),
         "E_SUCCESSOR_PATHS", label + " must be a new or empty directory")
    resolved = path.resolve()
    for other in others:
        other = other.resolve()
        need(resolved != other and other not in resolved.parents and resolved not in other.parents,
             "E_SUCCESSOR_PATHS", label + " overlaps the repository, supplement or another output")
    return resolved


def run_gate(repo: Path, candidate: str, supplement: Path, scratch: Path, evidence: Path, *,
             runner=run_bounded, audit=source_audit, checkout=checkout_historical,
             recheck=verify_historical_checkout, policy_path: Path = POLICY) -> dict:
    repo = repo.resolve()
    need(supplement.resolve() == (repo / ARCHIVAL / "supplement-1").resolve(), "E_SUCCESSOR_PATHS",
         "the supplement must be the candidate's committed archival/v0.2.0/supplement-1")
    supplement = supplement.resolve()
    scratch = _fresh(scratch, [repo, supplement], "scratch")
    evidence = _fresh(evidence, [repo, supplement, scratch], "evidence")
    policy, policy_sha = load_policy(policy_path)
    before = audit(repo, candidate, policy)
    scratch.mkdir(parents=True, exist_ok=True)
    evidence.mkdir(parents=True, exist_ok=True)
    historical = checkout(repo, scratch / "historical-T")
    t_report = evidence / "historical_T_report.json"
    code, out, err = runner([sys.executable, "-B", "-m", "verification.archive.offline_smoke",
                             "--supplement", str(supplement), "--scratch", str(scratch / "historical-restore"),
                             "--report", str(t_report)], historical, historical_environment(), HISTORICAL_TIMEOUT)
    (evidence / "historical_T_stdout.log").write_bytes(out)
    (evidence / "historical_T_stderr.log").write_bytes(err)
    need(t_report.is_file() and not t_report.is_symlink(), "E_SUCCESSOR_HISTORICAL",
         "historical T wrote no report: " + (out + err).decode("utf-8", "replace")[-600:])
    historical_result = validate_historical_report(t_report.read_bytes(), code)
    recheck(historical)
    c_report = evidence / "current_C_workflow_suite.json"
    current_env = {k: v for k, v in os.environ.items() if k not in {"PYTHONPATH", "PYTHONHOME"}}
    code, out, err = runner([sys.executable, "-B", "-m", "verification.integrity.run_tests", "--suite",
                             "workflow", "--report", str(c_report)], repo, current_env, CURRENT_TIMEOUT)
    (evidence / "current_C_stdout.log").write_bytes(out)
    (evidence / "current_C_stderr.log").write_bytes(err)
    need(c_report.is_file() and not c_report.is_symlink(), "E_SUCCESSOR_CURRENT",
         "current C suite wrote no report: " + (out + err).decode("utf-8", "replace")[-600:])
    current_result = validate_current_report(c_report.read_bytes(), code)
    need(audit(repo, candidate, policy) == before, "E_SUCCESSOR_SOURCE", "candidate source changed during verification")
    return {"contract": CONTRACT, "source": before, "historical_T": historical_result, "current_C": current_result,
            "approval": {"authority": policy["authority"], "owner": policy["owner"],
                         "independent_security_review": False, "effective_by": policy["effective_by"],
                         "policy_sha256": policy_sha},
            "historical_record": policy["historical_record"],
            "not_claimed": ["independent security review", "PR #113 approval", "mathematical certification",
                            "release acceptance"],
            "completed_stages": ["owner_engineering_policy", "source_audit_T_B_C", "archival_tree_equals_B",
                                 "approved_closure_delta", "historical_T_checkout", "historical_T_isolated_replay",
                                 "current_C_workflow_suite", "post_execution_source_recheck"]}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--repo", required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--supplement", required=True)
    parser.add_argument("--scratch", required=True)
    parser.add_argument("--evidence", required=True)
    parser.add_argument("--report", required=True)
    args = parser.parse_args(argv)
    context = None
    try:
        from verification.archive.offline_smoke import invocation_context
        context = invocation_context(args.repo, args.candidate)
        details = run_gate(Path(args.repo), args.candidate, Path(args.supplement), Path(args.scratch),
                           Path(args.evidence))
        payload = check_report("archive-reproducibility", context, details=details,
                               completed_stages=details["completed_stages"])
        code = 0
    except HardeningError as exc:
        payload = check_report("archive-reproducibility", context, "BLOCKED" if exc.exit_code == 3 else "FAIL", exc)
        code = exc.exit_code
    except Exception as exc:  # noqa: BLE001 - any other error is a failure, never a pass
        payload = check_report("archive-reproducibility", context, "FAIL", HardeningError("E_UNEXPECTED", str(exc)))
        code = 1
    write_report(args.report, payload)
    print("archive-reproducibility: " + payload["status"])
    return code


if __name__ == "__main__":
    raise SystemExit(main())
