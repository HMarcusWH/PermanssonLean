"""Genuine required-job source routing for PR113, CERT, and later main.

Only classifies independently authenticated Git/GitHub source identity.
It never approves infrastructure, security review, 45/11 mathematics, merge,
postseal, or publication. Historical migrations need a separate verifier.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import sys

from final_closure_authenticate import git as real_git, live as real_live
from pr113_boundary_io import strict_json_object, detached_destination
from release_target import B113, REPOSITORY

SHA = re.compile(r"^[0-9a-f]{40}$")
JOBS = {"research": "Research Lean",
        "archive-reproducibility": "Research integrity"}
FORMAT = "Permansson.PR113.CurrentRequiredLifecycleSource.v3"


class LifecycleError(ValueError):
    pass


def require(ok, why):
    if not ok:
        raise LifecycleError(why)


def signed(value):
    return isinstance(value, str) and SHA.fullmatch(value) is not None


def merged_113(*, git, live):
    """Verify the live original PR plus its ordered immutable B113/H113/M113."""
    pr = live("/pulls/113")
    require(isinstance(pr, dict) and pr.get("number") == 113
            and pr.get("merged") is True and pr.get("state") == "closed",
            "initial historical infrastructure PR has not been merged")
    H = (pr.get("head") or {}).get("sha")
    M = pr.get("merge_commit_sha")
    require(signed(H) and signed(M)
            and git("cat-file", "-t", H) == "commit"
            and git("cat-file", "-t", M) == "commit"
            and git("show", "-s", "--format=%P", M).split() == [B113, H]
            and git("rev-parse", M + "^{tree}") ==
                git("rev-parse", H + "^{tree}"),
            "reviewed exact B113/H113/M113 Git parent/tree topology invalid")
    return H, M


def actual_source(*, env=None, event_bytes=None, git=real_git, live=real_live):
    env = os.environ if env is None else env
    require(env.get("GITHUB_ACTIONS") == "true"
            and env.get("GITHUB_REPOSITORY") == REPOSITORY
            and env.get("GITHUB_JOB") in JOBS
            and env.get("GITHUB_WORKFLOW") == JOBS[env["GITHUB_JOB"]],
            "genuine original Research/Archive required job absent")
    event_kind = env.get("GITHUB_EVENT_NAME")
    current = env.get("GITHUB_SHA")
    require(event_kind in ("pull_request", "push")
            and signed(current)
            and git("rev-parse", "HEAD") == current
            and git("cat-file", "-t", current) == "commit",
            "actual required job checkout or GitHub head not authentic")
    try:
        run_id = int(env.get("GITHUB_RUN_ID", ""))
        attempt = int(env.get("GITHUB_RUN_ATTEMPT", ""))
    except (ValueError, TypeError) as exc:
        raise LifecycleError("original run identity absent") from exc
    require(run_id > 0 and attempt > 0, "original GitHub attempt invalid")
    if event_bytes is None:
        path = Path(env.get("GITHUB_EVENT_PATH", ""))
        require(path.is_file() and not path.is_symlink()
                and 0 < path.stat().st_size <= 8*1024*1024,
                "authentic required job event file missing")
        event_bytes = path.read_bytes()
    event = strict_json_object(event_bytes, max_bytes=8*1024*1024)
    require((event.get("repository") or {}).get("full_name") == REPOSITORY,
            "event repository does not match required job")
    output = {
        "format": FORMAT,
        "source_commit_sha": current,
        "github_job": env["GITHUB_JOB"],
        "github_run_id": run_id,
        "github_run_attempt": attempt,
        "event_sha256": hashlib.sha256(event_bytes).hexdigest(),
        "historical_migration_accepted": False,
        "required_ci_accepted": False,
        "mathematical_acceptance": False,
        "owner_merge_authorized": False,
        "publication_authorized": False,
    }
    if event_kind == "pull_request":
        try:
            number = event.get("number")
            pr = event.get("pull_request")
            require(type(number) is int and number >= 1 and isinstance(pr, dict),
                    "no original PR number/event")
            base, head = (pr.get("base") or {}), (pr.get("head") or {})
            B, H = base.get("sha"), head.get("sha")
            require(signed(B) and signed(H)
                    and base.get("ref") == "main"
                    and (base.get("repo") or {}).get("full_name") == REPOSITORY
                    and (head.get("repo") or {}).get("full_name") == REPOSITORY
                    and B != H
                    and env.get("GITHUB_REF") == "refs/pull/" + str(number) + "/merge"
                    and git("show", "-s", "--format=%P", current).split() == [B, H]
                    and git("rev-parse", current + "^{tree}") ==
                        git("rev-parse", H + "^{tree}"),
                    "not a genuine current same-repo B/H test-merge source")
            remote = live("/branches/main")
            require((remote.get("commit") or {}).get("sha") == B,
                    "original base differs from current remote main")
            current_pr = live("/pulls/" + str(number))
            require(current_pr.get("number") == number
                    and current_pr.get("merged") is False
                    and (current_pr.get("head") or {}).get("sha") == H
                    and (current_pr.get("base") or {}).get("sha") == B,
                    "remote PR has stale or unrelated B/H identity")
            if number == 113:
                require(B == B113
                        and head.get("ref") == "research/final-mathematical-closure",
                        "PR113 old immutable source/branch changed")
                output["phase"] = "initial_113_pr"
                output["infrastructure_head_sha"] = H
                output["infrastructure_merge_sha"] = None
            else:
                old_H, old_M = merged_113(git=git, live=live)
                require(git("merge-base", "--is-ancestor", old_M, B) == "",
                        "new development/CERT base does not inherit actual M113")
                output["phase"] = "main_descendant_pr"
                output["infrastructure_head_sha"] = old_H
                output["infrastructure_merge_sha"] = old_M
            output.update({"pr_number": number, "base_sha": B,
                           "head_sha": H, "synthetic_sha": current})
        except (KeyError, TypeError, AttributeError) as exc:
            raise LifecycleError("original PR source lacks required structure") from exc
    else:
        require(env.get("GITHUB_REF") == "refs/heads/main"
                and event.get("ref") == "refs/heads/main"
                and event.get("after") == current
                and (live("/branches/main").get("commit") or {}).get("sha") == current,
                "current main push is not source-bound")
        old_H, old_M = merged_113(git=git, live=live)
        require(git("merge-base", "--is-ancestor", old_M, current) == "",
                "main push is not a descendant of the authorized initial migration")
        output["phase"] = ("initial_113_main" if current == old_M
                           else "main_descendant_push")
        output.update({"pr_number": None, "base_sha": B113,
                       "head_sha": current, "synthetic_sha": None,
                       "infrastructure_head_sha": old_H,
                       "infrastructure_merge_sha": old_M})
    return output


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args(argv)
    try:
        report = actual_source()
        out = detached_destination(args.out, Path(__file__).resolve().parents[2])
        out.parent.mkdir(parents=True, exist_ok=True)
        with out.open("x", encoding="utf-8") as f:
            json.dump(report, f, sort_keys=True, indent=2)
            f.write("\n")
        print(json.dumps({"status": report["phase"],
                          "head": report["source_commit_sha"]}))
        return 0
    except (LifecycleError, OSError, KeyError, TypeError, ValueError) as exc:
        print("VERSIONED_REQUIRED_SOURCE_BLOCKED", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
