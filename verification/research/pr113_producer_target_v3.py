"""Authenticate original21 producer branch at real PR113 or successor H.

An operator-supplied future PR ID/branch is an untrusted lookup hint,
never approval. Every ID is checked against current GitHub event, live PR,
real main, immutable reviewed M113, and true Git ancestry.
"""
from __future__ import annotations
import os
import re

from final_closure_authenticate import live as real_live, git as real_git
from release_target import B113, REPOSITORY

BRANCH113 = "research/final-mathematical-closure"
SHA40 = re.compile(r"^[a-f0-9]{40}$")
BRANCH = re.compile(r"^research/[a-zA-Z0-9._/-]{1,160}$")


class ProducerTargetError(ValueError):
    pass


def require(ok, why):
    if not ok:
        raise ProducerTargetError(why)


def authenticated_producer_branch(head, *, env=None,
                                  live=real_live, git=real_git):
    """Verify a genuine source-controlled producer H before trusting its branch."""
    env = os.environ if env is None else env
    require(isinstance(head, str) and SHA40.fullmatch(head),
            "genuine original producer head required")
    require(env.get("GITHUB_ACTIONS") == "true"
            and env.get("GITHUB_REPOSITORY") == REPOSITORY
            and env.get("GITHUB_SHA") == head
            and env.get("GITHUB_EVENT_NAME") in ("push", "workflow_dispatch"),
            "original producer must be running at real GitHub branch head H")
    ref = env.get("GITHUB_REF")
    require(isinstance(ref, str) and ref.startswith("refs/heads/"),
            "branch-pinned GitHub producer event required")
    branch = ref.removeprefix("refs/heads/")
    require(BRANCH.fullmatch(branch) is not None
            and "//" not in branch and ".." not in branch
            and git("rev-parse", "HEAD") == head
            and git("cat-file", "-t", head) == "commit",
            "producer checkout, branch or commit identity invalid")
    if branch == BRANCH113:
        pr = live("/pulls/113")
        require(isinstance(pr, dict) and pr.get("number") == 113
                and pr.get("merged") is False
                and (pr.get("head") or {}).get("sha") == head
                and (pr.get("head") or {}).get("ref") == branch
                and (pr.get("base") or {}).get("sha") == B113,
                "initial original21 source not authentic unmerged PR113")
        return branch

    hint = env.get("PERMANSSON_CERT_PR_NUMBER", "")
    require(isinstance(hint, str) and hint.isdigit()
            and not hint.startswith("0")
            and int(hint) > 114,
            "successor producer needs real future CERT PR number")
    number = int(hint)
    successor = live("/pulls/" + str(number))
    require(isinstance(successor, dict)
            and successor.get("number") == number
            and successor.get("state") == "open"
            and successor.get("merged") is False
            and (successor.get("base") or {}).get("ref") == "main"
            and (successor.get("head") or {}).get("sha") == head
            and (successor.get("head") or {}).get("ref") == branch
            and (successor.get("head") or {}).get("repo", {}).get("full_name")
                == REPOSITORY,
            "future producer H is not current same-repo CERT PR head")
    B = (successor.get("base") or {}).get("sha")
    require(isinstance(B, str) and SHA40.fullmatch(B)
            and (live("/branches/main").get("commit") or {}).get("sha") == B,
            "future CERT PR base differs from real remote main")
    original = live("/pulls/113")
    M = original.get("merge_commit_sha") if isinstance(original, dict) else None
    historical_head = (original.get("head") or {}).get("sha") if isinstance(original, dict) else None
    require(original.get("merged") is True and original.get("state") == "closed"
            and isinstance(M, str) and SHA40.fullmatch(M)
            and isinstance(historical_head, str) and SHA40.fullmatch(historical_head)
            and git("cat-file", "-t", M) == "commit"
            and git("cat-file", "-t", historical_head) == "commit"
            and git("show", "-s", "--format=%P", M).split() ==
                [B113, historical_head]
            and git("rev-parse", M + "^{tree}") ==
                git("rev-parse", historical_head + "^{tree}")
            and git("merge-base", "--is-ancestor", M, B) == ""
            and git("merge-base", "--is-ancestor", B, head) == "",
            "CERT branch not descended from authentic initial approved M113")
    return branch
