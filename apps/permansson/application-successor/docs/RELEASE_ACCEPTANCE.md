# Releasing the finite numeric application

This page is the release procedure for the successor application's numeric
scope. A release publishes a wheel and an sdist; it does not change what any
output claims (see "What a release does not mean" below).

## What is released

| Field | Value |
| --- | --- |
| Distribution | `permansson-application-successor-recovery` |
| Version | `0.2.0` (owner decision, 2026-11-01) |
| Scope | `successor-finite-numeric.v1`: the 26 exact finite profiles of `data/capabilities.json`, numeric only |
| Platforms | `linux-cpython-3.12` and `linux-cpython-3.13`; other platforms are refused with `PLATFORM_UNQUALIFIED` |
| Policy | `data/acceptance_policy.successor_numeric.v1.json`, format `Permansson.App.AcceptancePolicy.v3` |
| Release authority | owner-engineering policy: the owner (`HMarcusWH`) approves and activates a release; **no independent security review is claimed** |
| Not in scope | native C10/C11 (separate default policy), Lean instance replay, Windows and macOS, any scientific or empirical claim |

## How a release is made

The release workflow `.github/workflows/application-release.yml` carries out
the whole procedure. It is added to the repository's reviewed workflow
contract by a separate, owner-approved change; until it is installed, no
release can be activated.

1. **Freeze the source.** The commit to release is on `main`, with the
   version above in `pyproject.toml` and `permansson_app.__version__`.
2. **Activate.** The owner dispatches the workflow on `main` from the Actions
   page and types the version. Under the owner-engineering policy this
   dispatch *is* the release approval. Nobody else, and no automation, may
   dispatch it.
3. **Build** (job `build`). `scripts/build_distributions.py` builds the
   wheel and sdist twice from the clean commit with the hash-locked tools and
   the commit time, and the two builds must be byte-identical.
4. **Qualify** (jobs `qualify linux-cpython-3.12` and `qualify
   linux-cpython-3.13`). On each platform,
   `verification/application_successor/check_installed_package.py`:
   - installs the hash-locked test dependencies and the wheel into a fresh
     environment, and checks `pip check`;
   - checks that the package imports from that environment, reports the
     version and carries byte-identical data;
   - runs the complete application suite against the installed code,
     recording every method's outcome; nothing may fail, and a skip is
     allowed only for a test the policy does not name;
   - runs the 26-profile walkthrough and the native C10/C11 runs through the
     installed CLI;
   - writes evidence records for every capability, derived only from the raw
     results.
5. **Gate** (job `gate`). `verification/application_successor/release_gate.py`
   passes only if every check below holds, and then writes
   `release-manifest.json` and `SHA256SUMS`:
   - the policy is the v3 owner-engineering policy, and it selects exactly
     the 26 registry profiles and exactly the two platforms; the target names
     all of them, once each;
   - the checkout is clean at the run's commit, and the version is final and
     matches the dispatch input;
   - through the GitHub API: the run is this workflow on `main` at this
     commit, dispatched by the owner; the build and both qualification jobs
     of this attempt succeeded; every artifact is downloaded through the API
     and matches the SHA-256 GitHub recorded for it;
   - every evidence record equals the one re-derived from its raw results,
     and the assessment is complete: nothing failing, and nothing missing
     except the owner activation, which the dispatch provides.
6. **Publish** (job `publish`, only after the gate). The workflow creates the
   tag `permansson-app-v<version>` at the commit and a GitHub release with
   exactly four assets: the wheel, the sdist, `SHA256SUMS` and
   `release-manifest.json`. It then runs `release_gate.py verify-published`,
   which downloads the published assets again and checks the tag and every
   hash against the manifest.

Any later change to the source is a different candidate: the procedure
starts again at that commit.

## What the manifest records

`release-manifest.json` binds:

- the source (repository, commit, tree) and the version;
- the scope, the policy path and its SHA-256, the 26 capabilities and two
  platforms;
- the release authority and the activation: run, attempt, event, actor and
  workflow;
- the wheel and sdist names and SHA-256, the build tools and the commit
  time used for the builds;
- per platform, the qualification artifact and its GitHub digest, the job
  and the SHA-256 of the raw results;
- the number of evidence records and the SHA-256 of their pinned digests,
  and the assessment;
- the claims: `lean_status=NOT_EXECUTED`, `independent_security_review=false`,
  `scientific_claims_verified=false`, `empirical_identification=NOT_IDENTIFIED`.

## Checking a published release yourself

```bash
sha256sum -c SHA256SUMS
```

`release-manifest.json` names the commit; a clean checkout of that commit
rebuilds the same wheel and sdist bytes with `scripts/build_distributions.py`
and the hash-locked tools. `release_gate.py verify-published` repeats the
workflow's post-publication check (it needs a GitHub token).

## What a release does not mean

- **No independent security review.** The release authority is an
  owner-engineering policy, decided by the owner and named as such. The
  gate is as strong as GitHub's own records and as control of the owner's
  GitHub account: anyone able to act as that account could also dispatch the
  workflow.
- **Numeric only.** Every output still reports `lean_status=NOT_EXECUTED`,
  `scientific_claims_verified=false` and
  `empirical_identification=NOT_IDENTIFIED`. Lean candidates remain
  development tools; a release does not authenticate any compiler run.
- **No mathematical certification.** The 45-case and 11-claim research CERT,
  empirical identification and publication of results are separate.
- **Historical archive unchanged.** The release does not relax the archive
  gate or any historical check.

## Withdrawing a release

A published release is withdrawn by deleting its GitHub release and tag and
recording why. The commit and the manifest stay in history. A replacement is
a new version made through the same procedure.

## Assessing evidence by hand

`python -m permansson_app.governance_cli release-assess TARGET EVIDENCE EXTERNAL_PINS POLICY --output NEW_DIR`
assesses a target against a policy (see [`ACCEPTANCE.md`](ACCEPTANCE.md)).
It reports evidence completeness only; it never authorizes a release.
