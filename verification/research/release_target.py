"""Versioned, fail-closed PR113 -> CERT Git/source target authentication.

This module binds source-controlled *intent* to genuine Git/GitHub objects at
execution time. It cannot grant review, CI, merge, or publication authority.
No future certification PR number or commit is hardcoded in checked-in source.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

from final_closure_authenticate import git as real_git, live as real_live

ROOT = Path(__file__).resolve().parents[2]
INTENT_PATH = "research/certification/target_intent.json"
REPOSITORY = "HMarcusWH/PermanssonLean"
B113 = "17c315f7df7abf457eb94d393bd526d46da6f6f4"
T = "71cc34fa0bc4b639c05d2ec5f39f0b88afd56388"
FORMAT = "Permansson.CertificationTargetIntent.v1"
BINDING_FORMAT = "Permansson.DetachedExecutionTarget.v1"
SHA = re.compile(r"^[0-9a-f]{40}$")
INTENT_KEYS = frozenset((
    "format", "repository", "original_base_sha", "historical_T_sha",
    "infrastructure_pr", "certification_pr", "status",
    "independent_security_review", "independent_mathematical_review",
    "publication_authorized",
))
BINDING_KEYS = frozenset((
    "format", "phase", "repository", "pr_number", "branch", "base_sha",
    "head_sha", "synthetic_sha", "infrastructure_merge_sha",
))


class TargetError(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise TargetError(reason)


def is_sha(value):
    return isinstance(value, str) and bool(SHA.fullmatch(value))


def intent_contract(obj):
    """Literal source intent cannot supply dynamic SHA IDs or approvals."""
    require(isinstance(obj, dict) and set(obj) == INTENT_KEYS,
            "target intent has missing or unauthorized fields")
    require(
        obj.get("format") == FORMAT and obj.get("repository") == REPOSITORY
        and obj.get("original_base_sha") == B113
        and obj.get("historical_T_sha") == T
        and type(obj.get("infrastructure_pr")) is int
        and obj["infrastructure_pr"] == 113
        and obj.get("certification_pr") is None
        and obj.get("status") == "CERTIFICATION_NOT_YET_BOUND"
        and obj.get("independent_security_review") is False
        and obj.get("independent_mathematical_review") is False
        and obj.get("publication_authorized") is False,
        "source intent attempted historical retargeting or approval",
    )
    return obj


def exact_intent(head, *, git=real_git):
    """Read source-controlled bytes from Git, never a shadow worktree file."""
    require(is_sha(head), "target source head not a commit SHA")
    require(git("cat-file", "-t", head) == "commit",
            "target source head not an accessible Git commit")
    raw = git("show", head + ":" + INTENT_PATH)
    try:
        parsed = json.loads(raw)
    except (ValueError, TypeError) as exc:
        raise TargetError("invalid Git-committed target intent") from exc
    return intent_contract(parsed)


def candidate_bindings(record):
    require(isinstance(record, dict) and set(record) == BINDING_KEYS,
            "detached target lacks exact required keys")
    require(record.get("format") == BINDING_FORMAT
            and record.get("repository") == REPOSITORY
            and record.get("phase") in (
                "infrastructure_premerge", "certification_premerge"),
            "unknown target record version/repository/phase")
    require(type(record.get("pr_number")) is int
            and record["pr_number"] >= 1
            and isinstance(record.get("branch"), str)
            and record["branch"].startswith("research/")
            and len(record["branch"]) <= 180
            and all(is_sha(record.get(k)) for k in (
                "base_sha", "head_sha", "synthetic_sha")),
            "target has unbound or invalid PR/source identity")
    require(record.get("infrastructure_merge_sha") is None
            if record["phase"] == "infrastructure_premerge"
            else is_sha(record.get("infrastructure_merge_sha")),
            "certification target has missing/early infrastructure merge")
    require(record["base_sha"] != record["head_sha"],
            "target cannot be its own source/base")
    if record["phase"] == "infrastructure_premerge":
        require(record["pr_number"] == 113 and
                record["branch"] == "research/final-mathematical-closure" and
                record["base_sha"] == B113,
                "infrastructure branch or original base was changed")
    else:
        require(record["pr_number"] not in (113, 114) and
                record["pr_number"] > 114 and
                record["branch"] != "research/final-mathematical-closure",
                "CERT must be a newly assigned successor PR, never old #114")
    return record


def git_topology(base, head, synthetic, *, git=real_git):
    for name, sha in (("B", base), ("H", head), ("S", synthetic)):
        require(git("cat-file", "-t", sha) == "commit",
                "missing real " + name + " commit")
    require(git("show", "-s", "--format=%P", synthetic).split() == [base, head],
            "synthetic merge does not have actual ordered base/head parents")
    require(git("rev-parse", synthetic + "^{tree}") ==
            git("rev-parse", head + "^{tree}"),
            "synthetic source tree differs from reviewed head")


def bind(record, *, intent, git=real_git, live=real_live):
    """Authenticate the PR identity; return a *nonaccepted* bound target.

    This is intentionally independent of mathematical acceptance. A source
    binding proves no reviewer independence, historical execution, or CI.
    """
    intent_contract(intent)
    candidate_bindings(record)
    base, head, syn = (record[k] for k in (
        "base_sha", "head_sha", "synthetic_sha"))
    git_topology(base, head, syn, git=git)
    current = live("/branches/main")
    require(isinstance(current, dict) and
            (current.get("commit") or {}).get("sha") == base,
            "remote main does not equal frozen target base")
    pr = live("/pulls/" + str(record["pr_number"]))
    require(isinstance(pr, dict)
            and pr.get("number") == record["pr_number"]
            and pr.get("state") == "open"
            and pr.get("merged") is False
            and pr.get("draft") is True
            and (pr.get("base") or {}).get("ref") == "main"
            and (pr.get("base") or {}).get("sha") == base
            and (pr.get("head") or {}).get("sha") == head
            and (pr.get("head") or {}).get("ref") == record["branch"]
            and (pr.get("head") or {}).get("repo", {}).get("full_name")
                == REPOSITORY,
            "live PR is unrelated, modified, merged or no longer draft")
    # GitHub creates an independent ephemeral test merge with its own
    # committer metadata. Its SHA need not equal a separately constructed
    # synthetic merge S, even when both have the exact ordered [B,H] parents
    # and H's source tree. Authenticate both objects instead of equating
    # their incidental commit-object hashes.
    github_merge_sha = pr.get("merge_commit_sha")
    require(is_sha(github_merge_sha),
            "live PR did not supply a genuine test-merge commit identifier")
    try:
        github_merge = live("/git/commits/" + github_merge_sha)
    except Exception as exc:
        raise TargetError("GitHub test merge unavailable for authentication") from exc
    require(isinstance(github_merge, dict)
            and github_merge.get("sha") == github_merge_sha
            and isinstance(github_merge.get("parents"), list)
            and [row.get("sha") for row in github_merge["parents"]
                 if isinstance(row, dict)] == [base, head]
            and (github_merge.get("tree") or {}).get("sha") ==
                git("rev-parse", head + "^{tree}"),
            "live GitHub test-merge topology or tree differs from exact B/H/S")
    if record["phase"] == "certification_premerge":
        p113 = live("/pulls/113")
        infra_merge = record["infrastructure_merge_sha"]
        require(isinstance(p113, dict) and
                p113.get("merged") is True and
                p113.get("merge_commit_sha") == infra_merge,
                "M113 not independently established by GitHub")
        require(git("cat-file", "-t", infra_merge) == "commit",
                "genuine infrastructure merge not in Git object store")
        require(git("merge-base", "--is-ancestor", infra_merge, base) == "",
                "CERT base is not descendant of real M113")
        require(git("rev-parse", infra_merge + "^{tree}") ==
                git("rev-parse", p113["head"]["sha"] + "^{tree}"),
                "infrastructure merged tree differs from reviewed source")
    else:
        require(record["infrastructure_merge_sha"] is None,
                "unmerged infrastructure cannot cite future M")
    return {
        "format": "Permansson.AuthenticatedTargetBinding.v1",
        "status": "GENUINE_PR_AND_GIT_IDENTITY_BOUND_NOT_REVIEWED",
        "phase": record["phase"],
        "repository": REPOSITORY,
        "pr_number": record["pr_number"],
        "branch": record["branch"],
        "base_sha": base,
        "head_sha": head,
        "synthetic_sha": syn,
        "infrastructure_merge_sha": record["infrastructure_merge_sha"],
        "independent_security_review": False,
        "independent_mathematical_review": False,
        "merge_authorized": False,
        "publication_authorized": False,
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--head", required=True)
    ap.add_argument("--target", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args(argv)
    try:
        out = args.out.absolute()
        require(not out.exists() and not out.is_symlink()
                and not any(p.is_symlink() for p in out.parents)
                and not out.is_relative_to(ROOT.resolve()),
                "execution binding must be a fresh detached record")
        intent = exact_intent(args.head)
        raw = args.target.read_bytes()
        require(0 < len(raw) <= 16 * 1024, "invalid detached target size")
        report = bind(json.loads(raw), intent=intent)
        require(report["head_sha"] == args.head,
                "frozen source does not match target")
        out.parent.mkdir(parents=True, exist_ok=True)
        with out.open("x", encoding="utf-8") as f:
            json.dump(report, f, indent=2, sort_keys=True)
            f.write("\n")
        print(json.dumps({"status": report["status"],
                          "head_sha": report["head_sha"]}, sort_keys=True))
        return 0
    except (TargetError, OSError, KeyError, TypeError, ValueError) as exc:
        print("TARGET NOT BOUND:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
