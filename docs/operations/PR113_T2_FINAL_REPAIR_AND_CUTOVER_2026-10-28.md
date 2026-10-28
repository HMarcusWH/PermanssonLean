# PR113 — T/T2 artifact repair and remaining cutover

Date: 2026-10-28. Audited parent: `c518fcaaba9a6fd4d7d9892dccec6d00431b92eb`.
This is an engineering plan, not independent review, activation or merge authority.

## Audit scope and baseline

The investigation inspected the full Git tree inventory, current PR and push
workflow inventory, Research/integrity execution results, archive entrypoint,
T/T2 producer, preactivation rehearsal, strict ZIP intake, versioned source
profile, implementation-matrix code, contribution requirements and review state.
This is not a claim that every line of every repository file was independently
audited. Container DNS prevented a GitHub clone; no complete local repository
build or full Research run is claimed by the focused tests below.

At the audited parent all 11 Actions runs completed: ten succeeded, Research
integrity failed only its archive-reproducibility job. Research ran 1,945 methods
successfully and also completed its C10, D0-F, default-target, import-coverage and
proof/axiom-firewall stages. Both push-triggered compiler workflows succeeded.
The current failure is `E_TOOLING_CLOSURE`, not a current Lean proof failure.

The original T verifier compares the entire canonical integrity/archive/guide
closure with current source. The two intentional integrity-tooling changes are
`verification/integrity/workflow_contract.py` and
`verification/integrity/tests/test_workflow.py`. They need the explicit successor
contract, not a rewritten historical package or an expected-failure result.

## Repair found before activation

The versioned T/T2 producer placed `historical_restore/` inside the directory
uploaded as evidence. Offline restoration creates a Git checkout and scratch
members there. The strict `infrastructure_acceptance.inspect_zip` consumer
rejects directories, empty entries and inventories exceeding 500 members.
The preactivation rehearsal repeated the scratch-in-output pattern and emitted
empty stderr files. A producer can therefore finish successfully without its
packet being consumable. The focused before/after reproduction used synthetic
child reports, the original orchestration code, and the unchanged ZIP parser:
old output was rejected; patched output was accepted.

The child-command wrapper also discarded most failure diagnostics before the
producer could persist them. A timed-out or failed real historical verifier
could leave neither an adequate process record nor its complete bounded logs.

## Deployed source repair

- Keep restoration scratch in a separate temporary directory, outside the
  upload directory, with cleanup on successful and failed executions.
- Run child commands with the existing scrubbed environment and retain bounded
  stdout/stderr plus a structured execution sidecar before raising on failure.
  A zero exit is labelled reports-unverified, never independently approved.
- Represent empty streams through their empty-byte SHA-256 in the nonempty
  sidecar, not forbidden zero-byte ZIP members.
- Reject malformed report JSON, duplicate keys, symlinked reports, output
  overlaps, nonregular/empty evidence members and missing required reports.
- Recheck both source checkouts and the exact source profile after execution
  before writing a successful summary. Existing semantic scope checks remain.
- Retain the original stage-specific receipt names: the 25-source rehearsal
  still cannot count as active-30 T2 execution or genuine required CI.
- Include both the preactivation rehearsal suite and new subprocess/packet
  suite in fast preflight: 59 distinct suites after this change.

No installed workflow, historical archive or verifier, mathematical proof,
dependency pin, reviewer roster or branch protection is changed by this patch.

## Evidence and its limits

18 focused methods passed under ordinary and optimized Python in a local harness.
They use real subprocesses, files, timeouts, logs, ZIP creation and strict ZIP/JSON
validation. The historical/current executors and source-audit inputs in these
tests are explicitly SYNTHETIC. The local harness uses extracted unchanged
consumer/parser functions and import adapters because no clone is available;
committed CI tests import the actual repository modules. These results are not
a genuine offline T replay, GitHub artifact authentication or independent review.
The six changed/added Python sources parse. The complete 59-suite preflight,
Lean rebuild and genuine T/T2 production remain separate execution obligations.

## Ordered remaining work

1. Verify this patch at its exact new head. Require Research to remain green,
   all source/profile tests to execute, and the new subprocess/ZIP tests to pass.
   A historical-closure failure in the unchanged archive job is still a failure,
   not waived by the new tests.
2. Run the preactivation rehearsal in an actual environment capable of Python
   3.13, pinned pypdf, nonroot execution, network namespace isolation and zero
   capabilities. Authenticate T and current H as separate clean Git checkouts.
   Use fresh detached output; retain original reports and new process sidecars.
3. Independently review the exact final migration: 23 retained workflows,
   two replaced workflows, five additions and three verifier/test replacements.
   Review the new executor/helper sources and the correct A2 baseline as well.
   Owner-authorized reviewer policy must contain real independent reviewers;
   source-owned flags and this document cannot configure that authority.
4. With separate installation authorization, atomically install the reviewed
   ten-path cutover on the unmerged PR branch. Do not turn the 25-file profile
   into an ad-hoc intermediate profile. Any subsequent edit invalidates affected
   exact-source reviews and requires renewed verification.
5. Execute genuine T/T2 and corrected-baseline A2 producer jobs at that final H.
   Confirm ZIPs contain only the intended report/log packets, not restore trees.
   Independently authenticate repository, workflow blob, run, attempt, job,
   check, artifact IDs and exact bytes. Collect the separate artifact-bound
   security attestation; never borrow artifacts from a different head/attempt.
6. Run the twelve exact-source required contexts. Archive must now demonstrate
   actual original isolated T restoration AND genuine reviewed current-source
   verification through the successor gate, with all downstream Research stages
   executed. Check the effective GitHub protection policy separately.
7. Request the separate owner merge decision only after all required evidence
   is present. Reauthenticate the real ordered main merge and later descendants.
   Independent mathematical certification and publication remain in CERT.

## Stop conditions

Do not silently weaken archive equality, edit immutable historical hashes,
activate unreviewed workflow definitions, import current proof objects into
history, accept partial/mixed-source evidence, mark skipped steps successful,
or invent a reviewer. A failed historical execution must stay failed with its
actual diagnostic. Successful engineering tests do not grant merge authority.

## Post-rehearsal direct-command repair

The genuine rehearsal at `fb89f4dd2e4c51790f15b416b820e7f25ac50f80`
found a shared direct-script import failure before either child started.
The dynamic staged-contract loader now establishes its helper checkout's
package context and rejects cached foreign package sources. Its inspected
checkout may still be a separate disposable active30 fixture. Expected import
failures retain their cause through `ToolingMigrationError`; no substitute
validator or `PYTHONPATH` override is used. Historical children retain their
separate checkout and scrubbed import environment.

The rehearsal CLI creates a fresh detached outer diagnostic directory before
checking sources or loading the profile. It records the command, declared
sources, execution stage and outer exit. Child return codes come only from real
retained execution sidecars. Import failures have no invented T/H reports;
T's original BLOCKED report and exit 3 remain distinct from the wrapper's exit 2.
Unexpected exceptions retain bounded, redacted tracebacks and remain failures.
Outer diagnostics are separate from the strict inner report/log packet.

On a qualified Linux host, from any working directory, use absolute paths:

```bash
env -u PYTHONPATH -u PYTHONHOME python3.13 -B \
  "$H_DIR/verification/research/pr113_archive_pre_activation_rehearsal_v1.py" \
  --historical-T-source "$T_DIR" --current-source "$H_DIR" \
  --head "$H_REPAIR" --out "$EVIDENCE_DIR" \
  --diagnostics "$OUTER_DIAGNOSTICS_DIR"
```

Both output directories must be fresh, unsymlinked and disjoint from both source
trees and each other. Without `--diagnostics`, the outer directory is the sibling
`EVIDENCE_DIR.diagnostics`. The tooling-only CLI uses `--out FILE` and an explicit
`--phase staged` or `active`. The active dual producer instead uses `--output
DIRECTORY` and rejects staged25 source. It is not a preactivation launch route.

Require Python 3.13, exactly `pypdf==6.10.0`, nonroot execution, passwordless sudo
for the supported `unshare --net` / `setpriv` chain, genuine readable IPv4 and
IPv6 route tables inside the new namespace, zero capabilities, no supplementary
groups, NoNewPrivs, no outward routes and conclusive outbound denial. Call T's
unchanged attestation through that chain before restoration. A VM booted with
`ipv6.disable=1` is incompatible; missing IPv6 metadata must still block.

The new direct-CLI subprocess suite is registered in fast preflight and ordinary
Research discovery. It audits real committed staged25 and disposable active30
sources, checks unrelated/foreign-package cwd behavior, wrong head, dirty source,
contract drift and phase rejection, and exercises optimized Python. Synthetic
faults remain labelled fixtures. Measure suite counts at the tested commit;
the earlier 59-suite count above describes its historical patch only.

These research helpers, tests and runbook have no existing exact-byte manifest
bindings. The 35 historical files, installed 25 workflows, staged contract pins
and workflow-only profile digest remain unchanged. Full historical acceptance
still requires a genuine complete T/H run and semantic packet validation. The
old current-source archive tooling-closure failure, 32 mutable-action uses in
13 inherited workflows, T2/A2 activation, artifact authentication and independent
security decisions remain separate open gates. Do not silently waive them.
