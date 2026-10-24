"""Independent GitHub/Git-object authentication for final mathematical release.

Never promote an arbitrary JSON flag, SHA-shaped string, reviewer name or
self-reported CI event. No network or missing objects -> strict rejection.
Offline draft/audit modes never use this module.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import re
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "https://api.github.com/repos/HMarcusWH/PermanssonLean"
BASE = "17c315f7df7abf457eb94d393bd526d46da6f6f4"
SHA = re.compile(r"^[0-9a-f]{40}$")
REQUIRED = frozenset((
    "research", "build", "frozen-source-preservation",
    "multiagent-protocols", "approx-quotient",
    "release-export-integrity", "archive-reproducibility",
    # These independent, applicable source-head checks MUST also be green.
    # A green Research build cannot substitute for a failed executable,
    # application or cross-platform integrity job.
    "executable-verification", "research-release",
    "integrity-portability-windows",
    "Application contract (ubuntu-latest)",
    "Application contract (windows-latest)",
))


class AuthenticationError(ValueError):
    pass


def demand(ok, message):
    if not ok:
        raise AuthenticationError(message)


def git(*args):
    try:
        return subprocess.check_output(["git", *args], cwd=ROOT,
                text=True, stderr=subprocess.DEVNULL, timeout=20).strip()
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise AuthenticationError("missing authentic Git object: " + " ".join(args)) from exc


def live(path):
    """Only literal GitHub repo endpoints constructed by this module."""
    headers = {"User-Agent": "Permansson-Closure-Acceptance/1",
               "Accept": "application/vnd.github+json"}
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = "Bearer " + token
    req = urllib.request.Request(PREFIX+path, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=20) as response:
            return json.load(response)
    except Exception as exc:
        raise AuthenticationError("live GitHub authentication unavailable: " + path) from exc


def verify_source(receipts):
    b,h,s,m = (receipts.get(x) for x in
                ("base_sha","head_sha","synthetic_sha","merged_main_sha"))
    for name,value in zip("BHSM",(b,h,s,m)):
        demand(isinstance(value,str) and SHA.fullmatch(value),
               "missing real "+name+" SHA")
        demand(git("cat-file","-t",value)=="commit",name+" is not a Git commit")
    demand(b==BASE,"wrong original branch base")
    demand(git("show","-s","--format=%P",s).split()==[b,h],
           "synthetic Git parents differ from original B/H")
    demand(git("rev-parse",s+"^{tree}")==git("rev-parse",m+"^{tree}"),
           "synthetic and merged final trees differ")
    git("merge-base","--is-ancestor",b,m)
    git("merge-base","--is-ancestor",h,m)
    pr=live("/pulls/113")
    demand(pr.get("number")==113 and pr.get("merged") is True,
           "the PR must be truly merged for final acceptance")
    # GitHub may display a MOVED base SHA after the merge; B is immutable
    # in the authentic synthetic and merged Git parent objects instead.
    demand(pr["head"]["sha"]==h and pr.get("merge_commit_sha")==m,
           "live GitHub PR H/M differs from claimed receipts")
    demand(git("show","-s","--format=%P",m).split()==[b,h],
           "merged M is not a true ordered [B,H] merge commit")
    runs=live("/commits/"+h+"/check-runs?per_page=100")["check_runs"]
    accepted={x["name"]:x for x in runs if
              x.get("head_sha")==h and x.get("conclusion")=="success"
              and x.get("status")=="completed"}
    demand(REQUIRED <= accepted.keys(),"missing genuine source-bound CI checks")
    given=receipts.get("source_bound_ci",[])
    demand(isinstance(given,list),"CI receipts must be source-bound entries")
    for name in REQUIRED:
        cert=accepted[name]
        demand(any(isinstance(x,dict) and x.get("name")==name
                   and x.get("id")==cert.get("id") and x.get("head_sha")==h
                   for x in given),
               "not a live source-bound CI receipt: "+name)
    approvals=live("/pulls/113/reviews?per_page=100")
    author=(pr.get("user") or {}).get("login")
    reviewer_ids={x.get("id") for x in approvals if
                  x.get("state")=="APPROVED" and x.get("commit_id")==h
                  and x.get("submitted_at") and x.get("user")
                  and x["user"].get("login")!=author}
    reviews=receipts.get("independent_source_reviews",[])
    demand(bool(reviewer_ids) and isinstance(reviews,list) and
           any(isinstance(x,dict) and x.get("id") in reviewer_ids
               for x in reviews),
           "independent reviewer approval on exact H not authenticated")
    return {"B":b,"H":h,"S":s,"M":m,"reviewer_ids":reviewer_ids}


# --- Source-bound premerge and merged-source authentication (v2) ---
#
# The old verify_source remains a postmerge strict compatibility entrypoint;
# neither legacy nor v2 acceptance ever accepts a self-reported review flag.


MAX_PAGES = 20
REVIEWER_POLICY = ROOT / "research/paper_closures/post_merge_112/reviewer_authority.json"


def paginate(resource, *, key=None):
    """Fetch complete GitHub pages; never certify the truncated first page."""
    rows = []
    for page in range(1, MAX_PAGES + 1):
        suffix = "?per_page=100" + (f"&page={page}" if page > 1 else "")
        response = live(resource + suffix)
        batch = response.get(key) if key is not None and isinstance(response, dict) else response
        demand(isinstance(batch, list), "malformed paginated GitHub response")
        rows.extend(batch)
        if len(batch) < 100:
            return rows
    raise AuthenticationError("GitHub evidence exceeds bounded pagination")


def reviewer_authorized(login, role):
    """Explicit owner-versioned reviewer authority; non-author alone is insufficient."""
    demand(role in ("source", "scholarly"), "unknown reviewer role")
    try:
        policy = json.loads(REVIEWER_POLICY.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise AuthenticationError("reviewer authority policy unavailable") from exc
    demand(isinstance(policy, dict) and
           policy.get("format") == "Permansson.ReviewerAuthority.v1",
           "invalid reviewer authority policy")
    if policy.get("status") != "OWNER_AUTHORIZED":
        return False
    rows = policy.get(role + "_reviewers")
    demand(isinstance(rows, list), "reviewer roster absent")
    return any(isinstance(x, dict) and
               x.get("login") == login and
               x.get("independence_disclosed") is True and
               x.get("approved_by") == "HMarcusWH"
               for x in rows)


def current_reviews_by_user(reviews):
    """One effective review per user, including dismissal and later changes requests."""
    latest = {}
    for review in reviews:
        if not isinstance(review, dict):
            raise AuthenticationError("malformed GitHub review")
        user = (review.get("user") or {}).get("login")
        rid = review.get("id")
        stamp = review.get("submitted_at") or review.get("dismissed_at") or ""
        if not user or type(rid) is not int:
            continue
        key = (stamp, rid)
        if user not in latest or key > latest[user][0]:
            latest[user] = (key, review)
    return {name: item[1] for name, item in latest.items()}


REVIEW_PREFIX = "PERMANSSON-REVIEW-V2:"
SHA256 = re.compile(r"^[0-9a-f]{64}$")


def receipt_payload_digest(receipts):
    """Digest exact proof/case/claim overlay excluding unknown future review IDs.

    The reviewer can attest this digest before they submit the GitHub review;
    adding its real review ID to the detached overlay afterward does not
    change the reviewed mathematical/evidence decisions.
    """
    import hashlib
    fields = ("compiler_axiom_receipts", "positive_test_receipts",
              "semantic_negative_receipts", "case_decisions", "claim_decisions")
    payload = {}
    for name in fields:
        rows = receipts.get(name, [])
        demand(isinstance(rows, list), "invalid case/claim review payload")
        payload[name] = [
            {k: v for k, v in row.items() if k != "review_id"}
            for row in rows if isinstance(row, dict)]
        demand(len(payload[name]) == len(rows), "malformed review payload")
    raw = json.dumps(payload, sort_keys=True, ensure_ascii=False,
                     separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def authenticated_checks(head_sha):
    """Select the latest trusted check attempt for every required job.

    Older success cannot mask a newer failed, cancelled, or queued run.
    GitHub check-run IDs are not workflow-run IDs.
    """
    demand(isinstance(head_sha, str) and SHA.fullmatch(head_sha),
           "invalid checked source revision")
    rows = paginate("/commits/" + head_sha + "/check-runs", key="check_runs")
    by_name = {}
    for check in rows:
        if not isinstance(check, dict) or check.get("head_sha") != head_sha:
            continue
        name = check.get("name")
        if name not in REQUIRED:
            continue
        if (check.get("app") or {}).get("slug") != "github-actions":
            continue
        rid = check.get("id")
        demand(type(rid) is int and rid > 0, "bad GitHub check-run ID")
        details = check.get("details_url")
        if details is not None:
            demand(isinstance(details, str) and details.startswith(
                "https://github.com/HMarcusWH/PermanssonLean/actions/runs/"),
                "required check has unexpected execution provenance")
        if name not in by_name or rid > by_name[name]["id"]:
            by_name[name] = check
    demand(REQUIRED <= by_name.keys(), "required GitHub Actions checks absent")
    for name in REQUIRED:
        selected = by_name[name]
        demand(selected.get("status") == "completed" and
               selected.get("conclusion") == "success",
               "latest required check is not successful: " + name)
    return by_name


def authenticate_scoped_reviews(head_sha, author, bundle_sha256, refs,
                                expected_payload_sha256):
    """Parse per-case/claim decisions from exact-H non-author GitHub approvals.

    These scopes are authentic review-body content from GitHub, not the
    caller-supplied JSON overlay. An approval must bind an immutable bundle
    digest to the reviewed exact H. Missing scopes never imply acceptance.
    """
    demand(isinstance(bundle_sha256, str) and SHA256.fullmatch(bundle_sha256),
           "reviewed detached bundle digest required")
    demand(isinstance(refs, list), "independent review receipts malformed")
    registered_ids = {x.get("id") for x in refs if isinstance(x, dict)}
    scopes = {}
    reviews = paginate("/pulls/113/reviews")
    for review in current_reviews_by_user(reviews).values():
        user = (review.get("user") or {}).get("login")
        rid = review.get("id")
        if (review.get("state") != "APPROVED" or
            review.get("commit_id") != head_sha or
            not review.get("submitted_at") or not user or user == author or
            not reviewer_authorized(user, "source") or
            rid not in registered_ids):
            continue
        lines = [x.strip() for x in (review.get("body") or "").splitlines()
                 if x.strip().startswith(REVIEW_PREFIX)]
        demand(len(lines) <= 1, "ambiguous reviewer attestation lines")
        if not lines:
            continue
        try:
            claim = json.loads(lines[0][len(REVIEW_PREFIX):].strip())
        except (ValueError, TypeError) as exc:
            raise AuthenticationError("reviewer attestation is not valid JSON") from exc
        demand(isinstance(claim, dict) and
               claim.get("head_sha") == head_sha and
               claim.get("evidence_bundle_sha256") == bundle_sha256 and
               claim.get("receipt_payload_sha256") == expected_payload_sha256,
               "reviewer's bundle/head/evidence payload does not match")
        cases = claim.get("cases", {})
        ids = claim.get("claims", [])
        demand(isinstance(cases, dict) and isinstance(ids, list) and
               len(ids) == len(set(ids)) and
               set(cases.values()) <= {"VERIFIED_SELECTED_SCOPE", "VERIFIED_NEGATIVE"},
               "malformed explicit case/claim decisions")
        pdf_sha = claim.get("pdf_sha256")
        demand(pdf_sha is None or (isinstance(pdf_sha, str) and
               SHA256.fullmatch(pdf_sha)), "invalid signed paper digest")
        scopes[rid] = {"cases": cases, "claims": ids, "reviewer": user,
                       "pdf_sha256": pdf_sha,
                       "manuscript_approved": claim.get("manuscript_approved") is True}
    return scopes


def verify_premerge(receipts, *, require_independent_review=True):
    """Fail closed before merging; DOES NOT fabricate or require future M."""
    b, h, s = (receipts.get(x) for x in ("base_sha", "head_sha", "synthetic_sha"))
    for name, value in (("B", b), ("H", h), ("S", s)):
        demand(isinstance(value, str) and SHA.fullmatch(value), "missing real " + name)
        demand(git("cat-file", "-t", value) == "commit", name + " not a Git commit")
    demand(b == BASE, "wrong immutable original PR base")
    demand(git("show", "-s", "--format=%P", s).split() == [b, h],
           "synthetic S does not have ordered B/H parents")
    demand(git("rev-parse", s + "^{tree}") ==
           git("rev-parse", h + "^{tree}"),
           "synthetic merge changes the reviewed source tree")
    demand(git("rev-parse", "main") == b,
           "main advanced after branch freeze: rebase/re-review needed")
    pr = live("/pulls/113")
    demand(pr.get("number") == 113 and pr.get("merged") is False and
           pr.get("state") == "open" and
           pr["head"]["sha"] == h and pr["base"]["sha"] == b,
           "PR no longer an authentic unmerged B/H review candidate")
    checks = authenticated_checks(h)
    required = receipts.get("source_bound_ci")
    demand(isinstance(required, list), "source-bound check receipts absent")
    for name in REQUIRED:
        recorded = [x for x in required if
                    isinstance(x, dict) and x.get("name") == name]
        demand(len(recorded) == 1 and
               recorded[0].get("id") == checks[name]["id"] and
               recorded[0].get("head_sha") == h,
               "stale, duplicate or forged check-run: " + name)
    scopes = {}
    if require_independent_review:
        scopes = authenticate_scoped_reviews(
            h, (pr.get("user") or {}).get("login"),
            receipts.get("evidence_bundle_sha256"),
            receipts.get("independent_source_reviews", []),
            receipt_payload_digest(receipts))
        demand(bool(scopes), "independent exact-H GitHub review/scope absent")
    return {"B": b, "H": h, "S": s, "M": None,
            "checks": checks, "review_scopes": scopes}


SCHOLARLY_PREFIX = "PERMANSSON-SCHOLARLY-V2:"


def authentic_scholarly_attestations(pr, head_sha, merged_sha):
    """Postmerge external scientific/PDF review from genuine GitHub comments.

    A machine can authenticate who authored this attestation, what they
    explicitly signed off, and the exact bytes. It cannot independently
    assess that the reviewer's mathematical reasoning was correct.
    """
    merged_at = pr.get("merged_at")
    demand(isinstance(merged_at, str) and bool(merged_at),
           "scholarly approval requires completed genuine GitHub merge")
    author = (pr.get("user") or {}).get("login")
    comments = paginate("/issues/113/comments")
    results = []
    for comment in comments:
        reviewer = (comment.get("user") or {}).get("login")
        stamp = comment.get("created_at")
        if (not reviewer or reviewer == author or
            not reviewer_authorized(reviewer, "scholarly") or
            not stamp or stamp < merged_at):
            continue
        lines = [l.strip() for l in (comment.get("body") or "").splitlines()
                 if l.strip().startswith(SCHOLARLY_PREFIX)]
        demand(len(lines) <= 1, "ambiguous publication attestations")
        if not lines:
            continue
        try:
            data = json.loads(lines[0][len(SCHOLARLY_PREFIX):].strip())
        except (TypeError, ValueError) as exc:
            raise AuthenticationError("invalid scholarly approval JSON") from exc
        if (not isinstance(data, dict) or
            data.get("head_sha") != head_sha or
            data.get("merged_main_sha") != merged_sha):
            continue
        pdf = data.get("pdf_sha256")
        pages = data.get("pages")
        claim_ids = data.get("approved_claim_ids")
        demand(isinstance(pdf, str) and SHA256.fullmatch(pdf) and
               isinstance(pages, dict) and bool(pages) and
               all(isinstance(n, str) and n.startswith("page-") and
                   isinstance(h, str) and SHA256.fullmatch(h)
                   for n, h in pages.items()) and
               isinstance(claim_ids, list) and
               len(claim_ids) == len(set(claim_ids)) and
               data.get("scholarly_review") == "APPROVED" and
               data.get("all_pages_visually_inspected") is True,
               "scholarly PDF attestation lacks real page/claim scope")
        results.append({"id": comment.get("id"), "reviewer": reviewer,
                        "pdf_sha256": pdf, "pages": pages,
                        "claim_ids": claim_ids, "merged_main_sha": merged_sha})
    return results


def verify_merged_v2(receipts):
    """Genuine ordered merge M and integrated main CI; no squash/rebase."""
    b, h, s, m = (receipts.get(x) for x in
                  ("base_sha", "head_sha", "synthetic_sha", "merged_main_sha"))
    for name, value in (("B", b), ("H", h), ("S", s), ("M", m)):
        demand(isinstance(value, str) and SHA.fullmatch(value), "missing merged " + name)
        demand(git("cat-file", "-t", value) == "commit",
               "missing authentic " + name + " Git object")
    demand(b == BASE and
           git("show", "-s", "--format=%P", s).split() == [b, h] and
           git("show", "-s", "--format=%P", m).split() == [b, h],
           "not an exact real [B,H] Git merge")
    demand(git("rev-parse", m + "^{tree}") ==
           git("rev-parse", s + "^{tree}"),
           "merged source tree differs from genuine synthetic merge")
    git("merge-base", "--is-ancestor", b, m)
    git("merge-base", "--is-ancestor", h, m)
    pr = live("/pulls/113")
    demand(pr.get("merged") is True and pr.get("head", {}).get("sha") == h and
           pr.get("merge_commit_sha") == m,
           "live GitHub PR does not authenticate M")
    frozen = authenticated_checks(h)
    integrated = authenticated_checks(m)
    for label, evidence, checks, checked_sha in (
        ("frozen", receipts.get("source_bound_ci"), frozen, h),
        ("integrated", receipts.get("merged_bound_ci"), integrated, m),
    ):
        demand(isinstance(evidence, list), "missing " + label + " CI")
        for name in REQUIRED:
            matched = [x for x in evidence if
                       isinstance(x, dict) and x.get("name") == name and
                       x.get("id") == checks[name]["id"] and
                       x.get("head_sha") == checked_sha]
            demand(len(matched) == 1,
                   label + " check is forged or stale: " + name)
    scopes = authenticate_scoped_reviews(
        h, (pr.get("user") or {}).get("login"),
        receipts.get("evidence_bundle_sha256"),
        receipts.get("independent_source_reviews", []),
        receipt_payload_digest(receipts))
    demand(bool(scopes), "missing authenticated independent exact-H scope reviews")
    scholarly = authentic_scholarly_attestations(pr, h, m)
    return {"B": b, "H": h, "S": s, "M": m,
            "checks": frozen, "integrated_checks": integrated,
            "review_scopes": scopes, "scholarly_reviews": scholarly}
