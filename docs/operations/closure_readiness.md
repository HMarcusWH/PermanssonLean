# Mathematical closure operational readiness

**Draft; no deployment authorization.** Baseline main was unprotected at commit `17c315f7df7abf457eb94d393bd526d46da6f6f4`. No ruleset, original source or dependency pin is changed by this PR.

Engineering compilation, theorem approval, independent scholarly review, PDF inspection, empirical identification, archive publication and operations are separate gates. The generated candidate remains unaccepted until actual post-merge M and CI identities and source/reviewer receipts have been authenticated. No release, tag, branch-setting change or production rollout is authorized.


## Current required-check policy (candidate, review pending)

The PR113 v2 source authenticator requires all twelve named, applicable
exact-head checks: Research Lean, original Lean build, frozen-source preservation,
F1, E1, release-export integrity, historical archive reproducibility, executable
verification, research-release, Windows integrity portability and both application
contract OS jobs. Their identities must be authenticated on H and again on genuine
merged M. A global green Research job cannot mask a failing standalone verifier.
The historical verifier and its original T tooling remain unchanged and may still
fail pending a separately authorized successor trust-boundary migration.

## PR #113 candidate execution — not an acceptance receipt

Original acceptance routing now identifies exactly 45 original positive routes
and 45 original semantic-negative routes, but registered routes are not
executed tests or independent review. The detached evidence machinery has
two explicitly different input classes:

| Input class | Cases | Candidate execution mechanism |
|---|---:|---|
| Original-source-preserving appended false Lean assertions | 25 | `final_closure_all_original_semantics.py` and nine-shard candidate workflow |
| Pre-existing original-source unittest false-probe methods | 20 | `final_closure_legacy_semantic_evidence.py`, passive Lean-input/log capture and eight-shard candidate workflow |

The first class preserves original Lean provider bytes, appends a designated
false statement, and requires both compilations to be inspected.
The second class runs the historically registered unittest methods and
captures any real Lean invocations, including those in nested audit drivers,
**before their temporary input files are deleted**. It verifies the designated
test-method source against the frozen Git blob, preserves compiler command,
input and output hashes, rejects missing diagnostic observations, and records
unreviewed case/source metadata. A successful Python test does not certify
that a captured diagnostic belongs to the intended false theorem.

**Never cast the second class directly into the canonical
`semantic_negative_receipts` field.** The current
`final_closure_case_receipts.validate_test_receipt` contract expects an
appended-source mutant with equal import lists and a source-bound positive
control. A standalone imported false probe has different semantics and
requires a separate reviewed, typed validation/receipt adapter before its
result may participate in effective mathematical acceptance. The legacy
observation records are intentionally incompatible with that accepted receipt.
A candidate-only bridge `final_closure_legacy_replay.py` now accepts one
individually attributable captured false method, demands a provider from its
original frozen theorem map, appends the false assertion to *unchanged tracked*
Lean provider bytes, recompiles the positive and negative sides with real pinned
Lean, and retains both sources and logs. Failed or ambiguous replays stay open
obligations. The replay output deliberately has no accepted CI check-run ID,
no independent review and no release authority.

The detached negative receipt schema now requires
`original_lean_source_member` in addition to the original source digest.
The strict source validator checks that the archived original matches the
checkout, that the mutation is an append-only extension, and that no import,
axiom, `sorry`, or `admit` has been injected. A hash-only reference to the
mutable checkout no longer suffices.

The separate four-shard `pr113-all-case-compiler.yml` workflow enumerates
the selected original 45-case and 11-claim theorem support. It must compile
the exact final source, export full elaborated Lean types and transitive axioms,
and retain the actual logs. All candidate workflows are read-only, shardable,
and cancel superseded branch-head runs. CI artifact retention is temporary
(30 days), so an authenticated final release must carry its own complete
source-bound evidence rather than relying on expiring GitHub artifacts.

### Operational progression, in order

1. Freeze a final candidate commit H. Verify original B, H, actual synthetic
   merge S, source-tree equality, dependency pins, protected paths and review
   policy. Do not treat an earlier green commit as evidence for a later H.
2. Execute all nine appended-source and eight legacy-compiler shards and all
   four theorem-export shards on the same authenticated source. Inspect
   every actual compiler diagnostic, positive control, source identity and
   missing/partial observation. No artificial check-run IDs are permitted.
3. Resolve standalone-probe versus appended-mutant typed evidence contracts.
   Authenticate the producing GitHub job, run attempt, checkout tree, uploaded
   artifact member inventory and digest; require the original case-to-test
   source map and the independent exact-H case/claim scope reviewer.
4. Only after effective 45/45 original cases and 11/11 new claims are accepted
   may the premerge full-source predicate be evaluated. The operation must
   still keep the release unapproved and not claim a merge.
5. A separately authorized merge M, exact-M CI, reproducible manuscript and
   archive builds, every rendered PDF page, and independent scholarly approval
   are indispensable to the full-release seal. No empirical Exact GR/PR or
   unbounded randomized-control assertion follows automatically.

PR #113 remains a draft until these gates actually succeed. No automation in
these candidate producer workflows authorizes a merge, release, review
approval, repository-setting change or deployment.


## Source-bound GitHub producing-artifact attestation (candidate only)

`verification/research/final_closure_candidate_artifact_auth.py` is the
read-only consumer for a downloaded GitHub Actions ZIP. It requires the actual
successful producing workflow/run, the precise shard job and its own check-run
ID, the recorded head and run attempt, the artifact ID/name and the authoritative
GitHub `sha256:` artifact digest. It verifies the downloaded ZIP against that
digest and checks the expected, explicitly unreviewed candidate manifest.
If GitHub does not provide the SHA-256 digest, this attestor **fails closed**.
A successful attestation **does not** certify its inner mathematical logs, test
semantics, completeness of the final 45/11 graph, or independent case approval.

For a genuine, already completed run, the operator may separately supply
the *actual* IDs and ZIP from GitHub (illustrative placeholders only):

```sh
python3 verification/research/final_closure_candidate_artifact_auth.py \
  --head "$H" --kind append --shard 0 \
  --run-id "$REAL_RUN_ID" --artifact-id "$REAL_ARTIFACT_ID" \
  --artifact-zip /external/pr113-append-shard-0.zip \
  --output /external/verified-producer-shard-0.json
```

The attestor records the independently queried producing check-run ID as
metadata but **never writes it into a mathematical acceptance receipt**.
Current strict `final_closure_case_receipts.validate_test_receipt` still
requires a research check binding and a reviewed append-only false theorem;
before G3, the final source gate must be further reconciled with authenticated
per-producing-job artifacts and every complete original criterion. Never copy
a green general research CI ID onto locally produced mutant logs.

The repository's current draft branch has no permission to self-approve
evidence, merge, tag, release or override these missing authentic dependencies.


## Immutable historical tooling gate — unresolved new release dependency

The archival v0.2.0 offline verifier binds the complete canonical
`verification/integrity/`, `verification/archive/`, and historical
reproduction-guide byte closure between its preserved tooling commit T and
candidate C. It deliberately rejects a changed checker at candidate HEAD
with `E_TOOLING_CLOSURE`, even when the new checker's own unit tests pass.

PR #113's updated 25-workflow source-profile checker remains **new, draft
tooling**, not a silently substituted historical verifier. Its workflow-pin
fix may pass frozen-source preservation while the historical offline-replay
job correctly refuses the altered code/guide closure. Resolving this
requires an explicitly authorized, independently reviewed tooling-version
migration or a reviewed release strategy that restores immutable T-compatible
tooling; the archived T snapshot must never be retroactively rewritten,
and source checks must not be skipped to obtain a green release check.

A green draft paper build or an updated workflow hash does not supersede
this distinct archive-reproducibility gate.


## PR113 successor-tooling preflight (candidate, not historical certification)

`verification/research/pr113_tooling_migration.py` compares the immutable
historical tooling T, release base B, current candidate H and every packaged
v0.2.0 tooling byte. It fails if the historical archive snapshot changes or
if any canonical verifier beyond the two named integrity profile files differs.
The 25-workflow successor inventory is bound to H; a distinct read-only test
exercises extra-tooling, archive-tampering, missing-workflow and wrong-HEAD
adversaries.

The resulting `Permansson.PR113.ToolingMigrationProposal.v1` is deliberately
`DRAFT_NEEDS_OWNER_AND_INDEPENDENT_SECURITY_REVIEW`. Its GitHub artifact is
not a signed migration, an approved new T, a reason to alter historical v0.2.0
evidence, or a mathematical release authorization. The old v0.2.0 offline
job remains an independently enforced gate until an owner and an independent
security reviewer authorize the successor release pathway.
