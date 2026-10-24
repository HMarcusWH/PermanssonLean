# PR113 workflow proposal staging (not an approval)

The three new GitHub Actions workflow files introduced during the PR114 repair batch were added to the *active* `.github/workflows/` set before the 25-workflow security contract was independently reviewed. The original review-sensitive workflow contract correctly rejected the 28-file tree. This commit relocates the three candidates **byte-identically** into this non-executing proposal directory, restoring the original 25 active workflow files without changing, overriding or suppressing the historical verifier.

The `manifest.json` records their original Git blob identifiers. The regression suite checks exact Git object equality, not just names or counts. No active trusted workflow is modified. The original archive T, the historical A2 verifier, the original 45 acceptance criteria and Lean sources remain unchanged.

**Review/activation rule:** The workflow candidates must not be placed under `.github/workflows/` or used as a producer of accepted CI evidence until an independent security reviewer and owner authorize the exact complete versioned workflow set (including all three) and the associated historical T→T2 and A2 successor trust migrations. Once approved, activation is an explicit source-changing commit which restarts the exact-head CI/evidence boundary. A passing candidate unit test, a GitHub run, or this manifest does NOT grant such authority.

* `pr113-historical-migration-candidates.yml`: proposed T/A2 separate-history dual-execution candidate.
* `pr113-original-positive-controls-candidate.yml`: proposed authentic 45 original case-positive CI producer.
* `pr113-postseal-replay.yml`: proposed post-M full-candidate archive replay producer.

Until those migrations are approved, the research and archive mandatory gates may still legitimately fail; those failures must not be suppressed. Existing authenticated 4+9+8 original producers remain separately mandatory. The original current Research Lean run is not replaced by the staged candidate.

Acceptance of this staging commit proves only that the **unreviewed workflow files are not active and have not been modified**. It neither executes nor approves any pending mathematical/archival work.

## Additive v3.1 complete-control producer proposal — not installed

The fourth staged file, `pr113-source-controls-v3_1.yml`, is **new proposed
source**, not one of the three preserved earlier-branch workflow blobs. It
consolidates three authentic producing job families under a single versioned
workflow: 45 original source-positive Lean/unittest controls, 20 genuine
original-source-appended legacy negatives using all 21 authenticated original
ZIPs, and 11 claim-specific positive/false Lean pairs. The job names, exact
GitHub source head, artifact run attempt, original member hashes and
reviewed source method selections become explicit CI execution inputs.

The proposed `push` trigger uses the **actual PR #113 research branch**
rather than the closed former #114 branch, and `workflow_dispatch` is only an
optional manually authorized path. This file is intentionally **outside**
`.github/workflows/`. Required reviewed selections under
`research/paper_closures/post_merge_112/` do not yet exist and every job
fails closed until those distinct case/claim choices and false-source files
are legitimately prepared. Do not replace them with generated
`False` fixtures or unreviewed role tags.

Before activation, the owner and a nonauthor security reviewer must authorize
the complete 25+successor workflow set (including triggering semantics,
source OIDs, job/check/artifact identity, script dependencies and original
historical T/A2 trust migrations). Installing these bytes changes final H
and requires **new** exact-H source CI and evidence. This manifest neither
grants approval nor publishes a workflow.
