# PR #115: T/T2 archive closure repair integration — **not activated**

The required `archive-reproducibility` check fails its actual restoration because the immutable tooling T snapshot `71cc34fa0bc4b639c05d2ec5f39f0b88afd56388` is no longer identical to current C. The frozen source manifest contains **35 files**. The two named changes between T and current 25-workflow source are:

- `verification/integrity/workflow_contract.py`
- `verification/integrity/tests/test_workflow.py`

The original versioned T2 architecture is **already implemented as an unapproved candidate** in `verification/research/pr113_tooling_migration_v2.py`, `pr113_dual_tooling_candidate_v2.py`, associated tests and `docs/operations/PR113_T2_FINAL_REPAIR_AND_CUTOVER_2026-10-28.md`. Do not implement a competing bypass or relabel an old historical T execution as C.

This PR adds `verification/research/pr115_archive_transition_guard_v1.py`. It performs a **read-only diagnosis** via the already-existing PR113 v1/v2 audits. It requires a clean, genuine exact-head Git checkout and checks: immutable B supplement tree; exact T package files and blob identities; the two explicitly allowed T-to-H integrity changes; installed 25 workflows; staged 30-workflow source proposal (when enabled); and review flags all explicitly *false*. It returns `CLOSURE_DRIFT_IDENTIFIED_REVIEW_REQUIRED`, never required-check PASS, never approved artifacts. Synthetic negative tests reject a forged historical package, an extra change to the original verifier, a stale/dirty checkout and missing workflows. An authentic full checkout case is exercised when the test runs in pinned CI; it is skipped in a source-only ZIP without Git history.

```bash
H="$(git rev-parse HEAD)"
OUT="$(mktemp -d)/pr115-T2-unapproved.json"
python3 -B verification/research/pr115_archive_transition_guard_v1.py \
  --repo . --head "$H" --out "$OUT"
```

This diagnostic **does not fix** the mandatory historical `E_TOOLING_CLOSURE` gate. The former archive job is correctly red until separately authorized source migration. The original isolated T replay, current H integrity verification, 30-workflow security review, genuine owner authorization, actual source-controlled activation, original GitHub run/job/artifact authentication and independent review are still separate, non-substitutable obligations. No `verification/archive/`, `verification/integrity/`, `.github/workflows/`, historical archive, hashes or accepted mathematical release files are modified.

Source-only engineering tests cannot sign an independent security attestation, confer final application acceptance, or merge PR #115 into main.
