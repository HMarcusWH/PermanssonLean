"""Authenticate post-freeze producer branch against actual successor PR/Git.

Original PR113 producer verification retains its existing v1 branch semantics.
A DIFFERENT branch requires real M113, an actual PR >114, ordered Git merge
topology when merged, exact source H and immutable M113 ancestry.
No operator hint, source flag, or reviewer text is accepted as authorization.
"""
from __future__ import annotations

import re

from final_closure_authenticate import live as real_live, git as real_git
from release_target import B113, REPOSITORY

ORIGINAL_BRANCH = "research/final-mathematical-closure"
SHA = re.compile(r"^[0-9a-f]{40}$")
BRANCH = re.compile(r"^research/[A-Za-z0-9._/-]{1,160}$")


class ProducerBranchError(ValueError):
    pass


def need(ok, why):
    if not ok:
        raise ProducerBranchError(why)


def authentic_branch(head, claimed_branch, *, live=real_live, git=real_git):
    need(isinstance(head, str) and SHA.fullmatch(head)
         and isinstance(claimed_branch, str),
         "original producer head or branch missing")
    if claimed_branch == ORIGINAL_BRANCH:
        # Keep the immutable original 21-producer v1 behavior unchanged.
        return claimed_branch
    need(BRANCH.fullmatch(claimed_branch) is not None
         and "//" not in claimed_branch and ".." not in claimed_branch
         and claimed_branch != ORIGINAL_BRANCH,
         "CERT producer branch malformed or aliases original PR113")
    old = live("/pulls/113")
    need(isinstance(old, dict) and old.get("number") == 113
         and old.get("merged") is True and old.get("state") == "closed",
         "CERT cannot borrow unmerged PR113 infrastructure")
    M113 = old.get("merge_commit_sha")
    H113 = (old.get("head") or {}).get("sha")
    need(isinstance(M113, str) and SHA.fullmatch(M113)
         and isinstance(H113, str) and SHA.fullmatch(H113)
         and git("cat-file", "-t", M113) == "commit"
         and git("cat-file", "-t", H113) == "commit"
         and git("show", "-s", "--format=%P", M113).split() == [B113, H113]
         and git("rev-parse", M113+"^{tree}") == git("rev-parse", H113+"^{tree}")
         and git("cat-file", "-t", head) == "commit"
         and git("merge-base", "--is-ancestor", M113, head) == "",
         "CERT producer head not descended from authentic ordered M113")
    candidate = live("/commits/"+head+"/pulls?per_page=100")
    need(isinstance(candidate, list) and len(candidate) < 100,
         "source commit's PR discovery missing/truncated")
    matching = []
    for pr in candidate:
        if not isinstance(pr, dict):
            continue
        number = pr.get("number")
        candidate_head, base = pr.get("head") or {}, pr.get("base") or {}
        if not (type(number) is int and number > 114
                and candidate_head.get("sha") == head
                and candidate_head.get("ref") == claimed_branch
                and (candidate_head.get("repo") or {}).get("full_name") == REPOSITORY
                and base.get("ref") == "main"
                and (base.get("repo") or {}).get("full_name") == REPOSITORY):
            continue
        # The commit-associated PR listing is only discovery, not authority:
        # GET the exact live PR, whose merged flag/parents can be authenticated.
        actual = live("/pulls/" + str(number))
        if (not isinstance(actual, dict) or actual.get("number") != number
                or (actual.get("head") or {}).get("sha") != head
                or (actual.get("head") or {}).get("ref") != claimed_branch
                or (actual.get("head") or {}).get("repo", {}).get("full_name") != REPOSITORY
                or (actual.get("base") or {}).get("ref") != "main"
                or (actual.get("base") or {}).get("repo", {}).get("full_name") != REPOSITORY):
            continue
        if actual.get("merged") is True and actual.get("state") == "closed":
            M = actual.get("merge_commit_sha")
            if not (isinstance(M, str) and SHA.fullmatch(M)
                    and git("cat-file", "-t", M) == "commit"):
                continue
            parents = git("show", "-s", "--format=%P", M).split()
            if len(parents) != 2 or parents[1] != head:
                continue
            B = parents[0]
            # Immutable Git parents, not a subsequently advanced base.sha.
            if git("rev-parse", M+"^{tree}") != git("rev-parse", head+"^{tree}"):
                continue
        elif actual.get("state") == "open" and actual.get("merged") is False:
            B = (actual.get("base") or {}).get("sha")
            main = live("/branches/main")
            if (B != base.get("sha")
                    or (main.get("commit") or {}).get("sha") != B):
                continue
        else:
            continue
        if not (isinstance(B, str) and SHA.fullmatch(B)
                and git("cat-file", "-t", B) == "commit"
                and git("merge-base", "--is-ancestor", M113, B) == ""
                and git("merge-base", "--is-ancestor", B, head) == ""):
            continue
        matching.append(actual)
    need(len(matching) == 1,
         "CERT source head/branch not uniquely bound to genuine GitHub PR")
    # The author, approval and evidence consumers still authenticate their
    # own scope; matching a PR is only a source-location fact.
    return claimed_branch
