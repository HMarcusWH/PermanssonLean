# Releasing the finite numeric application

This page is the release procedure for the successor application's numeric
scope. A release publishes a wheel and an sdist; it does not change what any
output claims (see "What a release does not mean" below).

## What is released

| Field | Value |
| --- | --- |
| Distribution | `permansson-application-successor-recovery` |
| Version | `0.2.0` (owner decision, 2026-11-01); released 2026-11-01, see [Released versions](#released-versions) |
| Scope | `successor-finite-numeric.v1`: the 26 exact finite profiles of `data/capabilities.json`, numeric only |
| Platforms | `linux-cpython-3.12` and `linux-cpython-3.13`; other platforms are refused with `PLATFORM_UNQUALIFIED` |
| Policy | `data/acceptance_policy.successor_numeric.v1.json`, format `Permansson.App.AcceptancePolicy.v3` |
| Release authority | owner-engineering policy: the owner (`HMarcusWH`) approves and activates a release; **no independent security review is claimed** |
| Not in scope | native C10/C11 (separate default policy), Lean instance replay, Windows and macOS, any scientific or empirical claim |

## How a release is made

The release workflow `.github/workflows/application-release.yml` carries out
the whole procedure. Every job name starts with `release`, so none can stand
in for a required check. It was added to the repository's reviewed workflow
contract by its own owner-approved change (pull request #118; archive
successor policy v2, `docs/operations/ARCHIVE_SUCCESSOR_CONTRACT_V2.md` at the
repository root).

1. **Freeze the source.** The commit to release is on `main`, with the
   version above in `pyproject.toml` and `permansson_app.__version__`.
2. **Activate.** The owner dispatches the workflow on `main` from the Actions
   page and types the version. Under the owner-engineering policy this
   dispatch *is* the release approval. Nobody else, and no automation, may
   dispatch it.
3. **Build** (job `release build`). `scripts/build_distributions.py` builds the
   wheel and sdist twice from the clean commit with the hash-locked tools and
   the commit time, and the two builds must be byte-identical.
4. **Qualify** (jobs `release qualify linux-cpython-3.12` and `release
   qualify linux-cpython-3.13`). On each platform,
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
5. **Gate** (job `release gate`). `verification/application_successor/release_gate.py`
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
6. **Publish** (job `release publish`, only after the gate, and only when the
   owner set `publish` on the dispatch). The workflow creates the
   tag `permansson-app-v<version>` at the commit and a GitHub release with
   exactly four assets: the wheel, the sdist, `SHA256SUMS` and
   `release-manifest.json`. It then runs `release_gate.py verify-published`,
   which downloads the published assets again and checks the tag and every
   hash against the manifest.

Any later change to the source is a different candidate: the procedure
starts again at that commit. A version is released once. Its tag already
exists, so a later candidate needs a new version number.

## Released versions

| Version | Date | Commit | Activation | Wheel SHA-256 | Sdist SHA-256 |
| --- | --- | --- | --- | --- | --- |
| [`0.2.0`](https://github.com/HMarcusWH/PermanssonLean/releases/tag/permansson-app-v0.2.0) | 2026-11-01 | `63a66c82a9ece4361f646ee13b6711192f831406` | run [41313849870](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41313849870), dispatched by `HMarcusWH` | `c119d66a1459535d17e2d688757ab06258d28654a86da4767df87d98783954dd` | `873af692897d6bf4de2cbf6bc728057685fb98a0236649f9693f6721d3e8268d` |

For 0.2.0, `release-manifest.json` has SHA-256
`d556cee5c1ea5e6f4f2cc61f37aaed3bfde83045e70e1e4d015b9ba1b804d0b3` and records
260 evidence records (26 capabilities, five evidence kinds, two platforms).

After publication, 0.2.0 was checked again locally on 2026-11-01. This was
an engineering check made at the owner's request, not an authenticated or
independent review:

- `sha256sum -c SHA256SUMS` passes, and the hashes equal the digests GitHub
  recorded for the assets.
- The tag points at the manifest's commit, and the manifest agrees with that
  source: policy hash, the 26 profiles, both platforms and the recomputed
  release subject.
- Two builds from a clean checkout of the tag, and a wheel built from the
  published sdist, are byte-identical to the published files.
- The qualification runner passes against the published wheel on CPython
  3.12 and 3.13. The 3.13 raw results are byte-identical to the release
  run's; the 3.12 results differ only in the recorded patch version.
- The 260 evidence records, re-derived from the release run's qualification
  artifacts, reproduce the manifest's evidence hash and its assessment
  exactly.
- The end-to-end walkthrough passes against the installed wheel on both
  versions. With `--lean`, all 21 emitted candidates compile with the pinned
  toolchain, and their 202 theorems pass the axiom audit.
- The whole-run budget refuses an undersized memory budget, a raised limit
  and an undersized output budget, and leaves no output. A forged
  child environment is ignored, and the internal child entry point refuses a
  direct start.

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

Check the downloaded files (the application README shows how to download
them):

```bash
sha256sum -c SHA256SUMS
```

Rebuild them from the commit that `release-manifest.json` names. Keep the
downloaded files outside the checkout (here in `$DL`), because the build
requires a clean checkout. At the root of a clean checkout of the repository:

```bash
DL=/path/to/the/downloaded/files
git checkout permansson-app-v0.2.0
python3 -m venv /tmp/permansson-build-tools
/tmp/permansson-build-tools/bin/python -m pip install --require-hashes \
  -r apps/permansson/application-successor/requirements-build.lock
python3 apps/permansson/application-successor/scripts/build_distributions.py \
  --output /tmp/permansson-rebuild --python /tmp/permansson-build-tools/bin/python
for f in permansson_application_successor_recovery-0.2.0-py3-none-any.whl \
         permansson_application_successor_recovery-0.2.0.tar.gz; do
  cmp "/tmp/permansson-rebuild/$f" "$DL/$f" && echo "$f: identical"
done
```

The build uses the commit time, so both files are byte-identical to the
published ones. `release_gate.py verify-published` repeats the workflow's
post-publication check, which downloads the release assets again through the
GitHub API (its command line needs a GitHub token).

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
