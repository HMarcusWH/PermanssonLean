# Archive successor contract v1 (owner engineering policy)

**Status:** the owner-adopted replacement for one comparison in the required
`archive-reproducibility` check, for the existing 25-workflow profile. It took
effect when the owner merged pull request #116 into `main`. It is **not** an
independent security review, not an approval of PR #113, not mathematical
certification and not release acceptance.

> **Policy v2.** [`ARCHIVE_SUCCESSOR_CONTRACT_V2.md`](ARCHIVE_SUCCESSOR_CONTRACT_V2.md)
> adds one owner-approved workflow, the application release workflow, and
> re-pins the two integrity files. The gate now reads policy v2; this page
> describes everything v2 keeps.

## Why the original check can no longer pass

The v0.2.0 verifier (`verification/archive/verify_bundle.py`) binds the
historical tooling snapshot T `71cc34fa` to the current source C by requiring
the complete `verification/integrity/`, `verification/archive/` and guide
closure of C to equal T's. After T, two reviewed integrity files changed:

- `verification/integrity/workflow_contract.py`
- `verification/integrity/tests/test_workflow.py`

From then on every head fails with `E_TOOLING_CLOSURE`, including `main` and
PR #113's own final head `117f4905` (run 40778332081). The archive itself is
not damaged. At the accepted base B `17c315f7` the full check, including the
committed publication, passed (Research integrity run 39513915824).

The staged 30-workflow T2 candidate cannot repair this as it stands. Its
inherited verifier (`pr113_historical_inheritance_v3.py`) requires all twelve
required checks of PR #113's final head to have succeeded. Its security-review
check (`pr113_secure_security_review_v3.py`) requires an `APPROVED` review from
an owner-authorized roster. Neither exists: `archive-reproducibility` failed on
that head, and the roster in
`research/certification/infrastructure_reviewer_authority.json` is
`UNCONFIGURED`. That candidate stays inactive and unchanged.

## What the successor gate verifies

`verification/research/archive_successor_gate_v1.py` replaces only the last
step of the `archive-reproducibility` job. The archive adversaries
(`run_tests --suite archive`) still run first, unchanged.

1. **Owner engineering policy.**
   `verification/research/archive_successor_policy_v1.json` is checked for its
   exact shape:
   - authority `OWNER_ENGINEERING_POLICY`, owner `HMarcusWH`, and
     `independent_security_review: false` (the gate rejects `true`);
   - T, B, the archival tree at B and 25 workflows;
   - the two approved closure changes, each with its T blob and its approved
     blob;
   - the historical record, kept as plain values.
2. **Current source C.** C is the checkout HEAD and has no modified tracked
   files. `pr113_tooling_migration.audit` checks that:
   - T and B are ancestors of C;
   - the supplement is unchanged since B and its manifest pins T;
   - the 35 packaged T files are byte-identical to T;
   - closure membership is unchanged and only the two named files differ;
   - exactly 25 workflows exist.

   The gate also requires the whole `archival/v0.2.0` tree to be the tree
   accepted at B, and each changed file to be at exactly its approved blob. Any
   third change, or any later edit of the two files, fails with
   `E_SUCCESSOR_DELTA` until the policy is updated and merged again by the owner.
3. **Historical T leg.** A fresh clone checked out at T runs T's own unchanged
   `python -B -m verification.archive.offline_smoke` in standalone mode on the
   committed supplement. It uses T's own nonroot `unshare --net` / `setpriv`
   isolation, with GitHub, Git, token and import variables removed. The gate
   accepts only `PASS` with:
   - binding `standalone_content_hashes_only` and source commit T, over 35
     files;
   - the original standalone stage list;
   - the accepted replay target and tree;
   - `accepted_artifact_replay_only` scope and `ENFORCED` network isolation.

   Standalone mode compares the packaged tooling with the code that executes,
   so a pass also proves that T's code ran. A blocked replay stays `BLOCKED`
   (exit 3). Afterwards the T checkout must still be clean at T.
4. **Current C leg.** C's own `run_tests --suite workflow` must pass with no
   skips, failures or errors.
5. **Recheck.** The source audit is repeated and must give the same result.

The job uploads the gate report as `archive-replay.json`, together with T's
original report and logs and the C suite report under `archive-evidence/`.

Every pin that names the two changed files' current bytes moves with this
change and is listed in the same pull request:

- `APPROVED_WORKFLOW_SHA256` and the archive command in
  `workflow_contract.py`;
- the A2 successor identity pins in `pr113_a2_successor_identity.py`.

## Effect on the inactive 30-workflow candidate

The staged PR #113 migration candidate requires the 25 installed workflows to
be the original preactivation bytes (head `5189f0c`) until its own atomic
cutover. This contract changes one of them, `research-integrity.yml`, so those
checks would otherwise reject every later head.

They now accept that change and nothing else:

- The policy names the change in `approved_workflow_changes`, from exactly its
  original preactivation blob to exactly the approved blob.
- `archive_successor_approval_v1.py` parses that field from the policy
  committed at the head being inspected.
- These consumers call it:
  - `pr113_workflow_profile_v2.py`
  - `pr113_successor_workflow_profile.py` (its allowlisted reader gains
    exactly the policy path)
  - `pr113_atomic_migration_preview.py`
  - the tests that compare installed and original workflows
    (`test_pr113_a2_successor_identity_v2.py`,
    `test_pr113_full_required_workflow_preview.py`,
    `test_pr113_inactive_required_gate_replacement.py`)

If the policy is absent at a head, the original strict comparison applies.
Any other workflow difference is still rejected. The candidate's own manifests,
staged sources and review packet are unchanged. It still describes replacing
the *original* archive step, so it would need a new review before any
activation, as before.

## What is not changed or claimed

- `verification/archive/`, the historical bundle, every recorded hash and the
  packaged T snapshot are unchanged. No condition in `verify_bundle.py` is
  relaxed.
- The PR #113 final-head failure stays recorded as a failure. The gate neither
  rewrites it nor requires it to have passed.
- The staged 30-workflow T2 candidate, its inheritance and its security-review
  modules are unchanged and inactive.
- No independent review, mathematical certification or release acceptance is
  created by this policy, the gate or a green check.

## Running it locally

The T leg needs what the CI runner provides:

- Linux, running as a nonroot user;
- passwordless `sudo` for `unshare --net` and `setpriv`;
- Python 3.13 with `pypdf==6.10.0` (`verification/integrity/requirements.txt`);
- a clean checkout with full history.

From the repository root:

```bash
python -B verification/research/archive_successor_gate_v1.py --repo . \
  --candidate "$(git rev-parse HEAD)" --supplement archival/v0.2.0/supplement-1 \
  --scratch /tmp/archive-clean --evidence /tmp/archive-evidence --report /tmp/archive-replay.json
```

As root, or without namespace support, T's launcher reports `BLOCKED`, and so
does the gate. The policy, source-audit, report-validation and orchestration
tests in `verification/research/test_archive_successor_gate_v1.py` run anywhere.
