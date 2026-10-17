"""Bind reports to canonical local objects or the actual GitHub event checkout."""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import os
from pathlib import Path

from .git_objects import GitRepo, full_oid
from .reports import HardeningError, strict_json, write_report

REPOSITORY = "HMarcusWH/PermanssonLean"


@dataclass(frozen=True)
class CheckContext:
    repository: str
    accepted_release: str
    checked_sha: str
    checked_tree: str
    event: str
    pr_number: int | None = None
    head_sha: str | None = None
    base_sha: str | None = None
    run_id: int | None = None
    run_attempt: int | None = None
    event_sha256: str | None = None
    scope: str = "canonical_commit_objects"


def capture_context(repo, candidate, event_file=None):
    from .policy import ACCEPTED_RELEASE
    full_oid(candidate)
    commit = repo.commit(candidate)
    actual = repo.run("rev-parse", "HEAD").strip().decode("ascii")
    if actual != candidate:
        raise HardeningError("E_CONTEXT", "Checkout HEAD differs from tested candidate")
    if os.environ.get("GITHUB_ACTIONS") != "true":
        if event_file is not None:
            raise HardeningError("E_CONTEXT", "An event file cannot manufacture a genuine CI context")
        return CheckContext(REPOSITORY, ACCEPTED_RELEASE, candidate, commit.tree, "local")
    try:
        if os.environ["GITHUB_REPOSITORY"] != REPOSITORY:
            raise HardeningError("E_CONTEXT", "Unexpected GitHub repository")
        if full_oid(os.environ["GITHUB_SHA"]) != candidate:
            raise HardeningError("E_CONTEXT", "Candidate differs from the event SHA")
        event_path = Path(os.environ["GITHUB_EVENT_PATH"])
        if event_path.stat().st_size > 8 * 1024 * 1024:
            raise HardeningError("E_LIMIT", "Event payload exceeds budget")
        raw = event_path.read_bytes()
        if event_file is not None and Path(event_file).read_bytes() != raw:
            raise HardeningError("E_CONTEXT", "Supplied event differs from the actual event file")
        event = strict_json(raw, "E_CONTEXT")
        name = os.environ["GITHUB_EVENT_NAME"]
        if event.get("repository", {}).get("full_name") != REPOSITORY:
            raise HardeningError("E_CONTEXT", "Event repository disagrees with environment")
        run_id, attempt = int(os.environ["GITHUB_RUN_ID"]), int(os.environ["GITHUB_RUN_ATTEMPT"])
        if run_id <= 0 or attempt <= 0:
            raise ValueError("Invalid run identity")
        values = dict(repository=REPOSITORY, accepted_release=ACCEPTED_RELEASE,
                      checked_sha=candidate, checked_tree=commit.tree, event=name,
                      run_id=run_id, run_attempt=attempt, event_sha256=hashlib.sha256(raw).hexdigest())
        if name == "pull_request":
            pr = event["pull_request"]
            head, base = full_oid(pr["head"]["sha"]), full_oid(pr["base"]["sha"])
            number = event["number"]
            if type(number) is not int or number <= 0:
                raise ValueError("Invalid PR number")
            if pr["base"]["ref"] != "main" or pr["base"]["repo"]["full_name"] != REPOSITORY:
                raise HardeningError("E_CONTEXT", "PR does not target the intended main branch")
            if os.environ["GITHUB_REF"] != f"refs/pull/{number}/merge":
                raise HardeningError("E_CONTEXT", "Checkout is not the genuine PR merge ref")
            if commit.parents != (base, head):
                raise HardeningError("E_CONTEXT", "Synthetic merge ordered parents differ from event base/head")
            values.update(pr_number=number, head_sha=head, base_sha=base)
        elif name == "push":
            if event.get("ref") != "refs/heads/main" or os.environ["GITHUB_REF"] != "refs/heads/main":
                raise HardeningError("E_CONTEXT", "Push is not for main")
            if event.get("after") != candidate:
                raise HardeningError("E_CONTEXT", "Push after SHA differs from candidate")
        elif name != "workflow_dispatch":
            raise HardeningError("E_CONTEXT", "Unsupported CI event")
        return CheckContext(**values)
    except (KeyError, TypeError, ValueError, OSError) as exc:
        raise HardeningError("E_CONTEXT", f"Missing or malformed source binding: {exc}") from exc


def require_pr_acceptance(context, *, head, base, synthetic):
    from .policy import ACCEPTED_RELEASE
    values = asdict(context) if isinstance(context, CheckContext) else context
    if (values.get("repository") != REPOSITORY or values.get("accepted_release") != ACCEPTED_RELEASE
            or values.get("event") != "pull_request" or values.get("head_sha") != head
            or values.get("base_sha") != base or values.get("checked_sha") != synthetic
            or type(values.get("run_id")) is not int or values["run_id"] <= 0
            or type(values.get("run_attempt")) is not int or values["run_attempt"] <= 0
            or type(values.get("pr_number")) is not int or values["pr_number"] <= 0):
        raise HardeningError("E_CONTEXT", "Evidence is not for the current genuine PR head/base/synthetic")


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True)
    parser.add_argument("--event-file", required=True)
    parser.add_argument("--report", required=True)
    args = parser.parse_args(argv)
    try:
        repo = GitRepo(args.repo)
        candidate = repo.run("rev-parse", "HEAD").strip().decode("ascii")
        context = capture_context(repo, candidate, args.event_file)
        if context.event not in {"pull_request", "push"}:
            raise HardeningError("E_CONTEXT", "Required check contexts accept only genuine PR merges or main pushes")
        write_report(args.report, {"format": "Permansson.Hardening.CIContext.v1", **asdict(context)})
        return 0
    except HardeningError as exc:
        write_report(args.report, {"format": "Permansson.Hardening.CIContext.v1", "status": "FAIL", "error_code": exc.code, "message": str(exc)})
        return exc.exit_code


if __name__ == "__main__":
    raise SystemExit(main())
