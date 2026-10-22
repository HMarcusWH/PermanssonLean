# Mathematical closure operational readiness

**Draft; no deployment authorization.** Baseline main was unprotected at commit `17c315f7df7abf457eb94d393bd526d46da6f6f4`. No ruleset, original source or dependency pin is changed by this PR.

Engineering compilation, theorem approval, independent scholarly review, PDF inspection, empirical identification, archive publication and operations are separate gates. The generated candidate remains unaccepted until actual post-merge M and CI identities and source/reviewer receipts have been authenticated. No release, tag, branch-setting change or production rollout is authorized.


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
