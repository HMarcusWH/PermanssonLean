# PR113 workflow proposal staging (not an approval)

The three new GitHub Actions workflow files introduced during the PR114 repair batch were added to the *active* `.github/workflows/` set before the 25-workflow security contract was independently reviewed. The original review-sensitive workflow contract correctly rejected the 28-file tree. This commit relocates the three candidates **byte-identically** into this non-executing proposal directory, restoring the original 25 active workflow files without changing, overriding or suppressing the historical verifier.

The `manifest.json` records their original Git blob identifiers. The regression suite checks exact Git object equality, not just names or counts. No active trusted workflow is modified. The original archive T, the historical A2 verifier, the original 45 acceptance criteria and Lean sources remain unchanged.

**Review/activation rule:** The workflow candidates must not be placed under `.github/workflows/` or used as a producer of accepted CI evidence until an independent security reviewer and owner authorize the exact complete versioned workflow set (including all three) and the associated historical T→T2 and A2 successor trust migrations. Once approved, activation is an explicit source-changing commit which restarts the exact-head CI/evidence boundary. A passing candidate unit test, a GitHub run, or this manifest does NOT grant such authority.

* `pr113-historical-migration-candidates.yml`: proposed T/A2 separate-history dual-execution candidate.
* `pr113-original-positive-controls-candidate.yml`: proposed authentic 45 original case-positive CI producer.
* `pr113-postseal-replay.yml`: proposed post-M full-candidate archive replay producer.

Until those migrations are approved, the research and archive mandatory gates may still legitimately fail; those failures must not be suppressed. Existing authenticated 4+9+8 original producers remain separately mandatory. The original current Research Lean run is not replaced by the staged candidate.

Acceptance of this staging commit proves only that the **unreviewed workflow files are not active and have not been modified**. It neither executes nor approves any pending mathematical/archival work.
