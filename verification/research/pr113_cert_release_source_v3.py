"""Resolve actual PR113 or genuinely later CERT PR for review/release gates.

Candidate base/head/merge SHAs are untrusted until GitHub PR identity and
Git ancestry are independently checked. This module never accepts a source
receipt, review, scientific claim, or publication request by itself.
"""
from __future__ import annotations

import re

from release_target import B113, REPOSITORY

SHA = re.compile(r"^[a-f0-9]{40}$")
BRANCH = re.compile(r"^research/[A-Za-z0-9._/-]{1,160}$")


class ReleaseSourceError(ValueError):
    pass


def need(ok, why):
    if not ok:
        raise ReleaseSourceError(why)


def source_pr(base, head, merged=None, *, git, live):
    """Return verified (PR number, live PR), never an approval decision."""
    need(all(isinstance(v, str) and SHA.fullmatch(v)
             for v in (base, head))
         and (merged is None or (
             isinstance(merged, str) and SHA.fullmatch(merged))),
         "unbound B/H/M source identity")
    old = live("/pulls/113")
    need(isinstance(old, dict) and old.get("number") == 113
         and (old.get("head") or {}).get("sha"),
         "original infrastructure PR source not available")
    if (old.get("head") or {}).get("sha") == head:
        need(base == B113,
             "original PR113 base must remain its frozen historical B")
        if merged is None:
            need(old.get("merged") is False and old.get("state") == "open",
                 "original PR113 is not a current unmerged source")
        else:
            need(old.get("merged") is True
                 and old.get("merge_commit_sha") == merged
                 and old.get("state") == "closed",
                 "original PR113 merged source not authenticated")
        return 113, old

    M113 = old.get("merge_commit_sha")
    H113 = (old.get("head") or {}).get("sha")
    need(old.get("merged") is True and old.get("state") == "closed"
         and isinstance(M113, str) and SHA.fullmatch(M113)
         and isinstance(H113, str) and SHA.fullmatch(H113)
         and git("cat-file", "-t", M113) == "commit"
         and git("cat-file", "-t", H113) == "commit"
         and git("show", "-s", "--format=%P", M113).split() == [B113, H113]
         and git("rev-parse", M113+"^{tree}") ==
             git("rev-parse", H113+"^{tree}")
         and git("merge-base", "--is-ancestor", M113, base) == "",
         "CERT base is not descended from a genuine owner-merged M113")
    discovered = live("/commits/"+head+"/pulls?per_page=100")
    need(isinstance(discovered, list) and len(discovered) < 100,
         "GitHub candidate PR inventory missing or truncated")
    found = []
    for row in discovered:
        if not isinstance(row, dict):
            continue
        number = row.get("number")
        if type(number) is not int or number <= 114:
            continue
        pr = live("/pulls/"+str(number))
        if not isinstance(pr, dict) or pr.get("number") != number:
            continue
        b = pr.get("base") or {}
        h = pr.get("head") or {}
        branch = h.get("ref")
        if not (h.get("sha") == head and b.get("sha") == base
                and b.get("ref") == "main"
                and (b.get("repo") or {}).get("full_name") == REPOSITORY
                and (h.get("repo") or {}).get("full_name") == REPOSITORY
                and isinstance(branch, str) and BRANCH.fullmatch(branch)
                and branch != "research/final-mathematical-closure"
                and "//" not in branch and ".." not in branch):
            continue
        if merged is None:
            if pr.get("state") != "open" or pr.get("merged") is not False:
                continue
        elif not (pr.get("state") == "closed"
                  and pr.get("merged") is True
                  and pr.get("merge_commit_sha") == merged):
            continue
        found.append(pr)
    need(len(found) == 1,
         "source not uniquely bound to genuine successor CERT PR")
    return found[0]["number"], found[0]
