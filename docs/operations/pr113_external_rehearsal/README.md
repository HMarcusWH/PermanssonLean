# PR113 external preactivation runner

This is a runnable **external GitHub Actions harness template** for the repaired staged25 T/H rehearsal. It remains inactive in this directory. Installing it in a separate harness repository leaves PermanssonLean's protected 25-workflow inventory unchanged. It does not activate the staged historical migration candidate or provide independent security, required-CI, mathematical, merge or publication authority.

The implementation follows the T/H leg of [the staged historical workflow](../pr113_unapproved_workflows/pr113-historical-migration-candidates.yml), with independent full clones instead of shared worktrees. It invokes the **preactivation** command, rather than the active30 producer.

## Installation and invocation

1. Select the separate harness repository covered by the external-runner authorization. Copy `ubuntu24-rehearsal.yml` unchanged to its default branch at **`.github/workflows/ubuntu24-rehearsal.yml`**. Keep its own commit SHA as the orchestrator identity. Do not install this file under PermanssonLean's `.github/workflows`.
2. Ensure Actions is enabled for that repository and that its policy permits the three pinned actions. The workflow needs only `contents: read`, public source downloads, and the GitHub-hosted runner's existing sudo capability. It needs no repository secrets, elevated GitHub token, protected environment or reviewer-policy changes.
3. After the repair is committed and pushed, fetch PR113's actual live head. Dispatch the registered harness **default branch**, supplying that full lowercase 40-character SHA as `current_head`. There is deliberately no stale default SHA in the workflow.
4. Retain the actual external workflow commit, run URL, run attempt, job, artifact ID and transport digest. The workflow rejects an input that differs from the live open PR113 head, and checks freshness again after execution.

For an authenticated GitHub CLI session, the dispatch shape is:

```bash
gh workflow run ubuntu24-rehearsal.yml \
  --repo OWNER/EXTERNAL-HARNESS-REPOSITORY \
  --ref HARNESS_DEFAULT_BRANCH \
  -f current_head=ACTUAL_IMMUTABLE_PR113_REPAIR_SHA
```

Replace the three explicit placeholders with observed values. The command is an interface example, not a record of a run already performed. A workflow must first be registered on the external repository's default branch; copying this template into documentation does not make it dispatchable.

## What the job actually executes

The job uses `ubuntu-24.04` and Python 3.13, captures selected orchestrator/run/environment identities, and reads public PR113 metadata before and after execution. It never dumps the runner environment.

It creates two separate full clones of `HMarcusWH/PermanssonLean`:

- T is detached at `71cc34fa0bc4b639c05d2ec5f39f0b88afd56388`.
- H is detached at the immutable input after matching it to the actual open PR113 branch.

Both sources must remain clean, full and owned by the nonroot runner. Checks reject shared Git metadata, shallow history, alternates, grafts, replacement refs, partial-clone configuration and promisor packs. The pre/post records bind the actual commit and tree. No source checkout is included in the uploaded artifact.

The original T and H dependency requirement bytes must agree. The job downloads the exact `pypdf-6.10.0-py3-none-any.whl`, records its SHA-256, creates a detached Python 3.13 virtual environment and installs only that required dependency before isolation. The original T dependency check still decides whether the interpreter and package versions satisfy the supported profile.

Runner qualification calls **T's unchanged `isolation_attestation`**, through the same supported chain as T's `launch_offline` and real ARCH-21 test:

```text
sudo -n /usr/bin/unshare --net -- /usr/bin/setpriv
  --reuid=NONROOT_UID --regid=NONROOT_GID --clear-groups
  --bounding-set=-all --inh-caps=-all --ambient-caps=-all --no-new-privs
  DETACHED_PYTHON_3_13 -B -c ORIGINAL_T_QUALIFICATION_CALL T_SOURCE PARENT_NETNS
```

Python starts only after privilege dropping. The actual historical function requires a different network namespace, nonzero UID/GID, no supplementary groups, all capability sets zero, `NoNewPrivs`, readable genuine IPv4 and IPv6 routing metadata, no outward routes and a conclusive outbound socket denial. Qualification is recorded as **runner qualification only**, never archive restoration.

After qualification, the job launches the repaired public entrypoint without `PYTHONPATH`:

```bash
"$PYTHON" -B "$H/verification/research/pr113_archive_pre_activation_rehearsal_v1.py" \
  --historical-T-source "$T" \
  --current-source "$H" \
  --head "$ACTUAL_H" \
  --out "$EVIDENCE/packet" \
  --diagnostics "$EVIDENCE/outer"
```

All these paths are populated from the real run. Sources, restore scratch, virtual environment, packet, and outer diagnostics are disjoint. Verification children receive an explicit environment allowlist without credentials, proxy settings, GitHub event variables, Git redirection or Python import overrides. The rehearsal retains its own source checks, original T restoration, current H workflow suite, final checks and nonauthorizing summary.

## Failure and evidence handling

A runner qualification failure makes the harness BLOCKED with exit 3. Its raw qualification command exit and stdout/stderr remain separate. No IPv6 fallback, substitute attestation or modified T is used.

If the actual rehearsal fails, its original wrapper exit remains in `meta/rehearsal.command.json`. A historical child exit 3 stays in `packet/T.execution.json` and its original BLOCKED report; the repaired wrapper's separate exit may be 2. H is not invented or appended after a failed T run. Success requires the actual complete staged summary at the declared H, with all approval/active30 fields still false.

The upload step runs even after a failure and retains this **outer diagnostic bundle**:

```text
meta/       orchestrator, environment, freshness, source, dependency,
            qualification and command records; original bounded command logs
outer/      repaired entrypoint's startup/failure records, when initialized
packet/     actual rehearsal reports and child logs, when the rehearsal reached them
packet.zip  strict inner packet, created only after complete semantic success
SHA256SUMS  checksums of retained files, excluding itself
```

Empty outer log files and directory entries are allowed in this diagnostic transport bundle. **The uploaded GitHub ZIP is not the strict inner producer packet.** After an actual zero rehearsal exit, a fresh subprocess imports the exact H helpers, validates the real T/H reports against the staged source profile, and checks every execution sidecar, original stream byte count/hash, trace and legacy log hash. It then packages only `packet/`'s regular, nonempty report/log members using the unchanged `evidence_files` inventory, reads `packet.zip` through the unchanged `infrastructure_acceptance.inspect_zip` reader, and compares every extracted byte with the original files. Its result and strict-packet digest are retained as `meta/strict-packet-validation.json`. Outer diagnostics, restored source trees, scratch and empty streams do not belong in the strict ZIP. A failed rehearsal retains its original packet directory; it is not converted into semantic success or an active30 receipt.

The artifact upload action returns the real transport ID/digest/URL, which the final step records in the run summary. These identities only exist after upload and are not predicted in source. Selected run/environment records are inspectable provenance, not independent authentication. A reviewer must fetch the real run/attempt/job/artifact through GitHub and bind the original bytes before asserting artifact authenticity.

GitHub's own step logs remain the evidence for failures occurring before the driver starts, such as checkout/setup failures. The initial `meta/setup.log` guarantees a diagnostic artifact can still be retained. No complete source or runner-qualification record is claimed for a setup failure.

The wrapper retains authority over each 1800-second child timeout and its process-group cleanup; the harness does not impose a shorter outer rehearsal timeout. The job has a 90-minute ceiling for both legs and preparation. A manual cancellation, runner loss or native job timeout can interrupt final artifact upload; inspect the native run status and logs, and repeat the whole run on a fresh runner instead of treating an incomplete artifact as a passed rehearsal.

## If the hosted runner cannot qualify

Keep its exact failure artifact. Use a fresh ephemeral self-hosted Linux VM, with:

- Ubuntu 24.04 or an equivalently qualified Linux kernel supporting network namespaces and IPv6 (`CONFIG_NET_NS` and `CONFIG_IPV6`); no `ipv6.disable=1` boot flag.
- Genuine `/proc/self/ns/net`, `/proc/self/status`, `/proc/net/route` and `/proc/net/ipv6_route` inside a new network namespace. Do not fabricate or bind replacement route files.
- A dedicated nonroot runner UID and GID. Existing administrator-authorized passwordless `sudo -n /usr/bin/unshare --net -- /usr/bin/setpriv …` must work; the runner cannot self-grant sudoers permissions.
- A setuid-capable sudo installation, executable util-linux `unshare`/`setpriv`, and permission for root to create a network namespace.
- Network access for exact public clones and dependency preparation before the original offline worker starts; no source sharing, credential injection, package substitutes or fallback online restoration.

Change only the **external harness** `runs-on` selector to an explicit label for that disposable VM, record the new harness commit, and rerun the entire qualification and rehearsal. Do not reuse the hosted qualification result. Destroy or reimage the ephemeral VM after collecting evidence; keep source/evidence identities and artifacts.

## Action source identities

The full commits reused from the staged workflow were verified against the official upstream commit objects on 28 October 2026:

- [actions/checkout `11d5960a326750d5838078e36cf38b85af677262`](https://github.com/actions/checkout/commit/11d5960a326750d5838078e36cf38b85af677262)
- [actions/setup-python `a26af69be951a213d495a4c3e4e4022e16d87065`](https://github.com/actions/setup-python/commit/a26af69be951a213d495a4c3e4e4022e16d87065)
- [actions/upload-artifact `ea165f8d65b6e75b540449e92b4886f43607fa02`](https://github.com/actions/upload-artifact/commit/ea165f8d65b6e75b540449e92b4886f43607fa02)

This prepares an executable external integration. It records no completed new rehearsal, external deployment, authentic producer artifact, reviewer decision, protected-profile activation, or merge.
