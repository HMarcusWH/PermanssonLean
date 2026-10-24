# PR #113 — review-pending exact-H original producer trigger repairs

**These three YAML files are non-executing proposals.** They live under
`docs/operations/`, not `.github/workflows/`, and have no acceptance or
security authority. The original 25 active workflows remain untouched.

## Problem addressed

The original four full compiler shards, nine semantic shards and eight
legacy source-observation shards are necessary original exact-H GitHub
producing artifacts. Their current `push.paths` filters do not reliably run
on verification/release-only commits. The existing `workflow_dispatch`
triggers cannot be relied upon for new workflow files absent from the
default branch. Accordingly, a frozen source H cannot be assumed to have all
21 original producing jobs.

## Review-candidate source transition

Each staged proposed workflow retains the complete active source byte-for-byte
**except for its `on:` trigger**. The revised trigger is:

```yaml
on:
  push:
    branches: [research/final-mathematical-closure]
  workflow_dispatch:
```

This always produces original 4+9+8 source-bound candidate jobs on the exact
research-branch commit H when the replacement is independently authorized
and installed. The exact original matrix shards, job names, Lean build, test
method commands and artifact upload logic are otherwise unchanged.

The versioned `manifest.json` explicitly lists the three active and staged
Git source identities and their 4/9/8 matrix counts. Use
`verification/research/pr113_original_producer_trigger_candidate.py` to
verify that the staged bytes are precisely the trigger-only patches of
**the committed active original source at the checked H** and are not
approved. No dynamic path or workflow hash is accepted.

## Security review and activation boundary

Before any staged YAML replaces a real `.github/workflows/` source:
- Original T→T2 and A2 historical verification transitions require genuine
  independent security review and owner approval.
- Independently review the full old/new workflow set, trigger frequency,
  `contents: read`, checkout/action pins, job/check identity, negative
  controls, artifact provenance, and concurrency/cancellation semantics.
- Approve the complete *final proposed tree* and all other workflow
  additions together; do not approve this in isolation and later mutate
  security-sensitive workflow bytes.
- Install only through an explicitly owner-authorized source commit on the
  same PR #113 branch. Activation changes H and resets source/CI/evidence
  baselines. Re-run all mandatory 12 CI contexts and all 21 original producer
  jobs at the resulting frozen H.
- Never treat compiler success, old-head proof log, source inventory, this
  review document or absence of pending workflows as external mathematical
  acceptance.

**Current status:** candidate YAMLs staged; independent review absent;
not installed; mandatory historical verification unchanged.
