"""Authenticated detached 20-case legacy-event selection delivery.

The survey must be a successful original exact-H GitHub producing job, and the
human event choices must come from an owner-authorized independent reviewer's
real GitHub PR comment *after* that survey was produced. Static intent cannot
invent runtime event or artifact IDs. No case is mathematically accepted here.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

from final_closure_authenticate import git as real_git, live as real_live
from infrastructure_acceptance import inspect_zip
from pr113_legacy20_runtime_resolution import (
    FORMAT_DECISION, FORMAT_REPORT, decision_to_selection,
)
from release_target import B113, REPOSITORY, T

ROOT = Path(__file__).resolve().parents[2]
POLICY = "research/certification/legacy_event_reviewer_authority.json"
ACTIVE_WORKFLOW = ".github/workflows/pr113-source-controls-v3_1.yml"
PREFIX = "PERMANSSON-LEGACY-EVENT-CHOICES-V1:"
REVIEW_FORMAT = "Permansson.PR113.Legacy20SelectionAttestation.v1"
SHA40 = re.compile(r"^[a-f0-9]{40}$")
SHA256 = re.compile(r"^[a-f0-9]{64}$")
SURVEY_MEMBER = "unreviewed_legacy20_candidates.json"
SURVEY_JOB = "original-legacy20"
SURVEY_ARTIFACT = "pr113-v31-legacy20-observation-candidates"
SOURCE_FIELDS = frozenset((
    "run_id", "run_attempt", "job_id", "check_run_id", "artifact_id",
))
SELECTION_FIELDS = frozenset((
    "case_id", "test_index", "observation_id", "producing_artifact_id",
))
ATTEST_FIELDS = frozenset((
    "format", "head_sha", "survey_zip_sha256", "survey_member_sha256",
    "observation_artifact_id", "status", "cases",
))


class ChoiceDeliveryError(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise ChoiceDeliveryError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def reviewer_policy(head, *, git):
    try:
        policy = json.loads(git("show", head + ":" + POLICY))
    except (OSError, ValueError, TypeError) as exc:
        raise ChoiceDeliveryError("legacy reviewer authority not source-bound") from exc
    require(isinstance(policy, dict)
            and set(policy) == {"format", "status", "owner", "reviewers"}
            and policy.get("format")
                == "Permansson.PR113.LegacyEventReviewerAuthority.v1"
            and policy.get("owner") == "HMarcusWH"
            and policy.get("status") == "OWNER_AUTHORIZED"
            and isinstance(policy.get("reviewers"), list)
            and bool(policy["reviewers"]),
            "independent legacy-event reviewer not owner-authorized")
    return policy


def authenticate_survey(head, ids, survey_bytes, *, live):
    require(isinstance(ids, dict) and set(ids) == SOURCE_FIELDS
            and all(type(ids.get(x)) is int and ids[x] > 0
                    for x in SOURCE_FIELDS),
            "original survey runtime IDs incomplete")
    run_id, attempt, job_id, check_id, artifact_id = (
        ids[k] for k in ("run_id", "run_attempt", "job_id",
                         "check_run_id", "artifact_id"))
    run = live(f"/actions/runs/{run_id}")
    jobs = live(f"/actions/runs/{run_id}/jobs?per_page=100")
    check = live(f"/check-runs/{check_id}")
    artifact = live(f"/actions/artifacts/{artifact_id}")
    require(isinstance(run, dict) and
            run.get("id") == run_id
            and run.get("head_sha") == head
            and run.get("head_branch") == "research/final-mathematical-closure"
            and run.get("event") == "push"
            and run.get("run_attempt") == attempt
            and run.get("status") == "completed"
            and run.get("conclusion") == "success"
            and str(run.get("path", "")).endswith(ACTIVE_WORKFLOW),
            "legacy survey must be a completed exact-H producer, not replay")
    rows = jobs.get("jobs") if isinstance(jobs, dict) else None
    matching = [x for x in rows if isinstance(x, dict)
                and x.get("id") == job_id] if isinstance(rows, list) else []
    require(len(matching) == 1, "legacy producing job not unique")
    job = matching[0]
    require(job.get("run_id") == run_id
            and job.get("run_attempt") == attempt
            and job.get("head_sha") == head
            and job.get("name") == SURVEY_JOB
            and job.get("status") == "completed"
            and job.get("conclusion") == "success"
            and str(job.get("check_run_url", "")).endswith(
                "/check-runs/" + str(check_id)),
            "legacy survey source job failed or is unrelated")
    require(isinstance(check, dict)
            and check.get("id") == check_id
            and check.get("head_sha") == head
            and check.get("name") == SURVEY_JOB
            and check.get("status") == "completed"
            and check.get("conclusion") == "success"
            and (check.get("app") or {}).get("slug") == "github-actions",
            "original survey check-run unauthenticated")
    require(isinstance(artifact, dict)
            and artifact.get("id") == artifact_id
            and artifact.get("name") == SURVEY_ARTIFACT
            and artifact.get("expired") is False
            and artifact.get("digest") == "sha256:" + digest(survey_bytes)
            and (artifact.get("workflow_run") or {}).get("id") == run_id
            and (artifact.get("workflow_run") or {}).get("head_sha") == head,
            "survey ZIP bytes/identity do not match GitHub")
    timestamps = [job.get("started_at"), artifact.get("created_at"),
                  job.get("completed_at")]
    require(all(isinstance(v, str) and
                re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", v)
                for v in timestamps) and
            timestamps[0] <= timestamps[1] <= timestamps[2],
            "original survey artifact not uploaded inside successful job")
    files = inspect_zip(survey_bytes)
    require(SURVEY_MEMBER in files and
            0 < len(files[SURVEY_MEMBER]) <= 4*1024*1024,
            "survey artifact lost the real enumerated event choices")
    survey_raw = files[SURVEY_MEMBER]
    try:
        survey = json.loads(survey_raw)
    except (TypeError, ValueError) as exc:
        raise ChoiceDeliveryError("survey source is invalid JSON") from exc
    require(isinstance(survey, dict) and
            survey.get("format") == FORMAT_REPORT and
            survey.get("status") == "ACTUAL_CAPTURE_OPTIONS_UNREVIEWED" and
            survey.get("source_head") == head and
            survey.get("original_legacy_case_count") == 20 and
            survey.get("all_cases_have_candidates") is True and
            survey.get("independent_case_review") is False and
            survey.get("mathematical_acceptance") is False and
            isinstance(survey.get("cases"), list) and
            len(survey["cases"]) == 20,
            "incomplete or self-approved legacy observed-events survey")
    bycase = {}
    for entry in survey["cases"]:
        require(isinstance(entry, dict)
                and set(entry) == {"case_id", "options"}
                and isinstance(entry["case_id"], str)
                and entry["case_id"] not in bycase
                and isinstance(entry["options"], list)
                and bool(entry["options"]),
                "real survey has duplicate/missing legacy observations")
        bycase[entry["case_id"]] = entry["options"]
    return bycase, digest(survey_raw), artifact["created_at"]


def comment_choices(head, comment_id, policy, survey_zip_sha256,
                    survey_member_sha256, survey_artifact_id, survey_time,
                    candidates, *, live):
    require(type(comment_id) is int and comment_id > 0,
            "reviewer comment must be a real GitHub comment ID")
    comment = live("/issues/comments/" + str(comment_id))
    pr = live("/pulls/113")
    require(isinstance(comment, dict) and
            comment.get("id") == comment_id and
            comment.get("issue_url") ==
                "https://api.github.com/repos/" + REPOSITORY + "/issues/113"
            and isinstance(pr, dict) and
            pr.get("state") == "open" and
            pr.get("merged") is False and
            (pr.get("head") or {}).get("sha") == head,
            "reviewer input belongs to wrong PR or stale head")
    author = (comment.get("user") or {}).get("login")
    # Issue comments are mutable. An edited old comment is NOT the same
    # immutable reviewer selection originally submitted after the producer
    # artifact existed. Refuse edits rather than accept a historical ID that
    # now points at different choices.
    require(isinstance(author, str) and author !=
            (pr.get("user") or {}).get("login") and
            isinstance(comment.get("created_at"), str) and
            comment["created_at"] > survey_time and
            isinstance(comment.get("updated_at"), str) and
            comment["updated_at"] == comment["created_at"],
            "review comment is early, post-edited, or not independent")
    eligible = [entry for entry in policy["reviewers"]
                if isinstance(entry, dict) and
                entry.get("login") == author
                and entry.get("approved_by") == "HMarcusWH"
                and entry.get("independence_disclosed") is True]
    require(len(eligible) == 1, "commenter is not an authorized independent reviewer")
    lines = [line.strip().removeprefix(PREFIX).strip()
             for line in (comment.get("body") or "").splitlines()
             if line.strip().startswith(PREFIX)]
    require(len(lines) == 1,
            "exactly one JSON reviewed choice line required from GitHub")
    try:
        att = json.loads(lines[0])
    except (TypeError, ValueError) as exc:
        raise ChoiceDeliveryError("reviewer selection is invalid JSON") from exc
    require(isinstance(att, dict) and set(att) == ATTEST_FIELDS
            and att.get("format") == REVIEW_FORMAT
            and att.get("status") == "RELEVANCE_CHOICES_ONLY_NOT_CASE_ACCEPTANCE"
            and att.get("head_sha") == head
            and att.get("survey_zip_sha256") == survey_zip_sha256
            and att.get("survey_member_sha256") == survey_member_sha256
            and att.get("observation_artifact_id") == survey_artifact_id
            and isinstance(att.get("cases"), list)
            and len(att["cases"]) == 20,
            "review choices are not bound to real source/head/survey ZIP")
    decisions = {}
    for row in att["cases"]:
        require(isinstance(row, dict) and set(row) == SELECTION_FIELDS
                and isinstance(row.get("case_id"), str)
                and row["case_id"] in candidates
                and row["case_id"] not in decisions
                and type(row.get("test_index")) is int
                and type(row.get("producing_artifact_id")) is int,
                "reviewer supplied malformed or repeated original-case choice")
        matched = [option for option in candidates[row["case_id"]]
                   if all(option.get(k) == val for k, val in row.items())]
        require(len(matched) == 1, "reviewer choice not in observed original capture")
        decisions[row["case_id"]] = row
    require(set(decisions) == set(candidates),
            "not all twenty original legacy cases selected")
    detached = {
        "format": FORMAT_DECISION,
        "head_sha": head,
        "status": "DETACHED_EVENT_CHOICES_UNREVIEWED",
        "independent_case_review": False,
        "mathematical_acceptance": False,
        "cases": [decisions[cid] for cid in sorted(decisions)],
    }
    # Apply the existing original case/method/actual-event binder as-is.
    decision_to_selection(head, candidates, detached)
    return detached, {"review_comment_id": comment_id,
                      "reviewer": author, "survey_zip_sha256": survey_zip_sha256,
                      "survey_member_sha256": survey_member_sha256,
                      "review_comment_created_at": comment["created_at"],
                      "review_comment_body_sha256":
                          digest(comment["body"].encode("utf-8"))}


def deliver(head, ids, original_zip, comment_id, *, git=real_git, live=real_live):
    require(isinstance(head, str) and SHA40.fullmatch(head)
            and git("rev-parse", "HEAD") == head,
            "runtime choice delivery must use frozen actual H")
    reviewer = reviewer_policy(head, git=git)
    candidates, observed_hash, observed_at = authenticate_survey(
        head, ids, original_zip, live=live)
    decisions, reviewer_info = comment_choices(
        head, comment_id, reviewer, digest(original_zip), observed_hash,
        ids["artifact_id"], observed_at, candidates, live=live)
    return {
        "selection": decisions,
        "diagnostic": {
            "format": "Permansson.PR113.LegacyChoiceDelivery.v1",
            "status": "AUTHENTIC_SURVEY_AND_REVIEWER_CHOICE_DELIVERED_UNCERTIFIED",
            "head_sha": head,
            "original_survey_run_id": ids["run_id"],
            "original_survey_job_id": ids["job_id"],
            "original_survey_artifact_id": ids["artifact_id"],
            **reviewer_info,
            "reviewer_selection_count": 20,
            "mathematical_acceptance": False,
            "publication_authorized": False,
            "source_mutated": False,
        }
    }


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head", required=True)
    p.add_argument("--survey-zip", type=Path, required=True)
    for label in ("run-id", "run-attempt", "job-id", "check-run-id",
                  "artifact-id", "review-comment-id"):
        p.add_argument("--" + label, required=True, type=int)
    p.add_argument("--out", type=Path, required=True)
    a = p.parse_args(argv)
    try:
        dest = a.out.absolute()
        require(not dest.exists() and not dest.is_symlink()
                and not dest.is_relative_to(ROOT.resolve())
                and not any(p.is_symlink() for p in dest.parents),
                "detached reviewer choice folder must be new and external")
        raw = a.survey_zip.read_bytes()
        report = deliver(
            a.head,
            {"run_id": a.run_id, "run_attempt": a.run_attempt,
             "job_id": a.job_id, "check_run_id": a.check_run_id,
             "artifact_id": a.artifact_id},
            raw, a.review_comment_id)
        dest.mkdir(parents=True, exist_ok=False)
        (dest / "reviewed_legacy20_runtime_event_choices.json").write_text(
            json.dumps(report["selection"], sort_keys=True, indent=2) + "\n")
        (dest / "choice_transport.json").write_text(
            json.dumps(report["diagnostic"], sort_keys=True, indent=2) + "\n")
        print(json.dumps(report["diagnostic"], sort_keys=True))
        return 0
    except (ChoiceDeliveryError, OSError, TypeError, ValueError,
            KeyError) as exc:
        print("LEGACY EVENT DELIVERY BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
