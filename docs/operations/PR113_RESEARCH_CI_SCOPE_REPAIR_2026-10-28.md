# PR113 Research CI: separate historical and current source obligations

Baseline inspected: `19d2f29d36bd426e19298a2e59b175affb928df0`.
The completed Research job ran 1,896 tests with one failure: the unchanged
historical A2 verifier was applied to a current checkout containing the
known twelve modified baseline providers. Its rejection preceded compilation.

## Deployed engineering correction

Keep the 25 installed workflow definitions unchanged. Replace the current
unittest integration adapter, not either historical executor, so the
registered `test_actual_final_source_and_semantic_mutations` method does both:

1. Create a fresh detached checkout of original A2
   `f71a76032b169aac7bfe0694aa715339a94d4e05`. Check its original integration
   blob and both executor blobs against their frozen identities. Launch that
   checkout's own `localized_prefix_gate.py` in a separate process.
2. Compile CURRENT source with the source-audited native successor selected
   by `pr113_a2_compiler_route_v3`. Historical success never substitutes for
   current-source compilation. Both outputs must pass the existing complete
   40-declaration/four-mutation receipt and semantic-diagnostic validators.

The second leg is essential: the original P-02 source map references this
same unittest method as compiler evidence. Converting it to a historical-only
check would silently change the case's meaning. The standalone current-source
A2 compiler test also remains mandatory; no source map or acceptance criterion
is deleted or marked approved.

## Dependency and source isolation

The historical worktree starts with no project `.lake/build`. Only dependency
packages may be shared after exact equality of committed `lean-toolchain`,
`lake-manifest.json` and `lakefile.toml`, followed by the original dependency
revision/cleanliness verifier. Every dependency is checked again after both
executions. Current project proof objects are never imported into history.

Both source checkouts must remain clean and at their bound commits. The worktree
is removed on success or failure; original raw receipts and command logs are
emitted by the integration test before its external evidence directory closes.
Missing tools, failed compilers, stale source, dirty dependencies, invalid logs,
missing declarations, missing mutants or wrong receipt identity all fail.

## Source guards and the later 30-workflow transition

The v1 current-source identity profile pins the new integration adapter exactly.
The original integration blob `c0f49038ea9b590720c78be85968eb63f5ac820f` stays
pinned at its historical introducer and preactivation revision. The original
`localized_prefix_gate.py`, `localized_prefix_support.py`, four accepted A2
proof providers, toolchain and dependency pins are not edited.

Preactivation and disposable-active30 guard tests distinguish three real sources:
original historical integration, the current engineering replay adapter, and
the separately staged security-reviewed successor consumer. They never relabel
one as another. The staged 30-workflow manifests and their artifact-authenticated
consumer remain unchanged. This patch does not install or authorize that profile.

## Downstream Research execution

No workflow condition, test skip, expected failure, or continue-on-error is
introduced. Once the genuine dual-source replay and the remaining regression
suite pass, the existing job proceeds to C10 generation and independent checking,
D0 golden reports, the default build, research import coverage, and the source
firewall. C10 must still bind the actual PR event and synthetic commit; historical
checkout activity must not leave tracked/untracked source dirt behind.

A green regression summary alone is insufficient: confirm every applicable
subsequent step in the exact-head Research job, including retained artifacts.

## Verification and authority boundaries

The focused replay test suite exercises real temporary Git/worktree identities,
byte pinning, dependency symlinks and cleanup with explicitly synthetic compiler
and receipt-library adapters. It is registered in fast preflight. Its passing
results are protocol evidence, not actual historical Lean execution.

Actual historical and current Lean results must come from the CI integration.
The new combined report is `HistoricalA2EngineeringReplay.v1`, states both source
identities explicitly, and cannot be used as the separate historical producer ZIP
or an independent security approval. Every approval/acceptance flag remains false.

Archive reproducibility, independent reviewer authority, reviewed workflow
activation, all twelve final checks, merge authorization and CERT certification
are separate obligations. In particular, this repair does not make the historical
T/current-tooling comparison green and does not authorize merging PR113.
