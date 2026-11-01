# Archive successor contract, policy v2: the application release workflow

**Status:** an owner engineering policy, in effect since the owner merged
pull request #118 into `main` on 2026-11-01. It is **not** an
independent security review, not an approval of PR #113, not mathematical
certification and not release acceptance. It extends
[contract v1](ARCHIVE_SUCCESSOR_CONTRACT_V1.md); everything v1 says still holds
unless this page says otherwise.

## What changes

The repository gains one workflow,
`.github/workflows/application-release.yml`. It releases the successor
application's numeric scope (see
`apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md`). The
repository then has 26 workflows instead of 25.

`verification/research/archive_successor_policy_v2.json` replaces v1 as the
policy the successor gate reads. v1 stays in the repository as history. The
gate rejects it for the current source, because it pins the older integrity
blobs and 25 workflows. Compared with v1, policy v2:

- sets `workflow_count` to 26;
- adds `approved_added_workflows`: exactly one path,
  `.github/workflows/application-release.yml`, at exactly one blob;
- re-pins the two approved closure changes, `workflow_contract.py` and
  `tests/test_workflow.py`, at the blobs that add the release workflow to the
  reviewed workflow contract;
- keeps the one approved change of `research-integrity.yml` unchanged.

Any later edit of the release workflow, or of either integrity file, fails the
archive check with `E_SUCCESSOR_DELTA` until the owner updates and merges the
policy again.

## The reviewed workflow contract

`verification/integrity/workflow_contract.py` names the release workflow in
`APPROVED_WORKFLOWS` with its SHA-256. `validate_release_workflow` checks its
text:

- it runs only on a manual `workflow_dispatch`, never on pull requests,
  pushes, schedules or other events, so it cannot produce a required
  context;
- the default token is `contents: read`, and it runs on GitHub-hosted runners;
- its jobs are exactly `release-build`, `release-qualify-py312`,
  `release-qualify-py313`, `release-gate` and `release-publish`, and no job
  identifier or display name equals a required context;
- only `release-publish` may write repository contents, and that is the only
  write grant in the file;
- it reads no repository secrets and requests no `id-token` or
  `actions: write`;
- every action is pinned to its reviewed commit.

`verification/integrity/tests/test_workflow.py` counts 26 workflows. It also
rejects variants of the release workflow that add a trigger, widen a token,
reuse a required context name or add a second writer.

## What the successor gate checks in addition

`archive_successor_gate_v1.py` reads policy v2 and also requires that:

- the workflow set is exactly the preactivation 25 plus the approved
  additions;
- each addition is at exactly its approved blob;
- the source audit set aside exactly those additions, at those blobs (see
  below).

## Effect on the staged PR #113 checks

The staged PR #113 checks reason about two workflow sets: the original 25,
and the 30 that PR #113 would install. The release workflow belongs to
neither. A workflow is set aside only if it meets both conditions:

- the policy v2 committed at the inspected head names it in
  `approved_added_workflows`;
- it is installed there in mode `100644` at exactly its approved blob.

Every other extra, renamed or changed workflow still counts and still fails
them. Without a committed policy v2, nothing is set aside. The rule is
implemented once, in `pr113_tooling_migration.owner_added_workflows`, and
used by:

- `pr113_tooling_migration.audit`: the original 25 must remain, and the
  report lists the additions it set aside (`owner_approved_added_workflows`);
- `pr113_workflow_profile_v2.py` (`source_phase` and `audit`);
- `pr113_successor_workflow_profile.py`: its allowlisted reader also gains
  exactly the policy v2 path;
- `pr113_atomic_migration_preview.py`;
- `pr113_disposable_transition_rehearsal.py`;
- the tests that count installed workflows directly:
  - `test_pr113_a2_successor_identity_v2.py`
  - `test_pr113_atomic_migration_preview.py`
  - `test_pr113_full_required_workflow_preview.py`
  - `test_pr113_inactive_required_gate_replacement.py`
  - `test_pr113_workflow_proposal_boundary.py`

The disposable 25-to-30 rehearsal rehearses PR #113's own reviewed transition.
Its staged 30-workflow contract does not name the release workflow, so the
disposable checkout leaves the workflow out. A real PR #113 activation would
have to carry the release workflow into its contract. That would be a change
to the staged candidate and would need its own review, like any other change
to it.

The candidate's manifests, staged sources and review packet are unchanged.

## What is not changed or claimed

- `verification/archive/`, the historical bundle, every recorded hash and the
  packaged T snapshot are unchanged. No condition in `verify_bundle.py` is
  relaxed.
- No existing workflow changes. The 24 others keep their v1 bytes, and
  `research-integrity.yml` keeps its v1-approved change.
- The release workflow can publish only after its own gate passes, and only
  when the owner dispatches it with `publish` set. Under the owner-engineering
  release policy that dispatch is the release activation. Nobody else, and no
  automation, may dispatch it.
- No independent review, mathematical certification or release acceptance is
  created by this policy, the gate or a green check.
