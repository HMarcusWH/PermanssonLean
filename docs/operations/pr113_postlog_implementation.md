# PR113 post-log implementation handoff

**State:** source-engineering candidates implemented. Historical security
authorization, exact-H CI evidence and independent mathematical/scholarly
approval are NOT complete. Do not merge or publish.

The original 45 cases, eleven claim IDs (Q1 Q2 Q3 M1 M2 M3 N1 N2 N3 D8
D9), 259 compiler targets, four A2 proof blobs and historical T supplement
remain the controlling scope. None of the code below creates review receipts.

## Implemented entrypoints

| Work | Source entrypoint | Result |
|---|---|---|
| W0 | verification/research/pr113_release_preflight.py | Detached B/H/T, 45/11/259 source identity snapshot, unreviewed |
| W1 | verification/research/pr113_dual_tooling_candidate.py | Actual original-T isolated offline restore and separate H workflow integrity candidate; owner/security signoff pending |
| W2 | verification/research/pr113_dual_a2_compiler.py | Separate real historical A2 and PR113 successor Lean, signatures, positive/false mutants; not substituted into original required test |
| W3 | verification/research/final_closure_assemble_v3.py | Original 21 producing ZIPs, actual 259 proof logs, 25 append-source true/false controls; 20 legacy/11 claim-control gaps reported |
| W3 | verification/research/final_closure_batch_legacy_replay.py | Batch actual source-appended Lean replays for 20 explicitly selected original legacy cases; new CI attribution still required |
| W4 | verification/research/final_closure_producer_bytes.py + final_closure_case_receipts.py | Authentic original job/check/archive/member SHA, typed v3 source evidence, no self-approval |
| W5 | research_papers/mathematical_closure/preamble.tex + reproduce_clean_sources.py | pdfTeX trailer determinism and honest mismatched-PDF diagnostics; independent final-M check pending |
| W6 | verification/research/final_closure_reproduction_auth.py | Live source-M GitHub clean build + retained two-root PDF, pages, manifest and archive byte authentication |
| W6 | verification/research/final_closure_postseal_auth.py | A future independently security-approved postseal job and original candidate ZIP verifier; workflow not yet installed |
| W7 | verification/research/pr113_final_source_readiness.py | Fail closed on less than 12 checks, 21 producing artifacts, 259 types or 45/11 individually owned controls |
| W8 | Actual independent reviewer authority and real M | Still outstanding; cannot be simulated by CI or author-created JSON |

The original historical verifier, release supplement, dependency pins and
accepted mathematical source modules have not been modified in this series.

## Step 1 — Source checkpoint and original T/H historical boundary

In an exact-H, clean Git checkout, write baseline outside the repository:

    python3 verification/research/pr113_release_preflight.py \
      --head "$H" --output /external/pr113/source-baseline.json

On an eligible nonroot isolated Linux host with original clean historical T
checkout and distinct clean H checkout, the two-leg archival candidate is:

    python3 verification/research/pr113_dual_tooling_candidate.py \
      --historical-T-source /checked-out-T \
      --current-source /checked-out-H --head "$H" \
      --output /external/pr113/dual-tooling

Running original T without genuine network isolation fails; running the
standalone historical replay inside GitHub Actions without source/event
binding is expressly prohibited. A green local candidate is not
authorization to replace the historical archive workflow.

Original historical A2 source checkout with original unchanged verifier
must also be run separately from the current PR113 successor checker:

    python3 verification/research/pr113_dual_a2_compiler.py \
      --historical-source /checked-out-valid-original-A2 \
      --historical-head "$HISTORICAL_A2_SHA" \
      --current-source /checked-out-H --current-head "$H" \
      --out /external/pr113/dual-A2

Both paths run actual pinned Lean theorem signatures, axiom checks, positive
fixture and all four false semantic mutants. Security authorization is
pending; the existing required old A2 test and T/C archive gate must never
be hidden, skipped or marked green by local diagnostic JSON.

## Step 2 — Only after code stabilizes: 4+9+8 exact-H producing jobs

A final H requires all twelve exact-H required contexts genuinely green.
The four all-case compiler shards may require explicit manual
workflow_dispatch due restrictive push-path filters.

Download all 21 *original* GitHub Actions ZIPs before expiry and authenticate
actual run attempts, job/check IDs and GitHub authoritative artifact SHA256.
Provide final_closure_producer_catalog.py an external JSON with format
Permansson.PR113.ExternalProducerCatalog.v1, head_sha H and 21 artifacts
entries containing kind, shard, run_id, artifact_id, zip_file.

    python3 verification/research/final_closure_producer_catalog.py \
      --head "$H" --catalog /external/pr113/catalog.json \
      --output /external/pr113/catalog-output

For the versioned v3 assembler, retain the identical ZIP bytes in a
directory as exact artifact_id.zip filenames:

    python3 verification/research/final_closure_assemble_v3.py \
      --head "$H" --synthetic "$S" \
      --catalog-dir /external/pr113/catalog-output \
      --producer-zips /external/pr113/producer-ids \
      --output /external/pr113/v3-preparation

The output consists of unreviewed_v3_receipts.json, unreviewed_evidence.zip
and remaining_work.json. The v3 statement SHA means the complete
kernel-elaborated Lean type digest, not an invented lexical source-header
hash. Only 25 truly observed append-case controls can be prefilled;
20 legacy cases and all eleven claim-specific controls still need genuine
new positive/negative evidence.

## Step 3 — Twenty actual original legacy source replays

Supply an externally reviewed selection JSON with format
Permansson.PR113.LegacyReplaySelection.v1 and exactly twenty cases entries.
Each must contain case_id, test_index, test_method, original_provider,
observation_id and producing_artifact_id, drawn from the authentic
legacy-shard recorded named-method observations. No model or test may guess
the relevant mathematical original source provider.

    python3 verification/research/final_closure_batch_legacy_replay.py \
      --head "$H" --catalog-dir /external/pr113/catalog-output \
      --producer-zips /external/pr113/producer-ids \
      --selection /external/pr113/legacy-selection.json \
      --out /external/pr113/legacy-real-lean

Each actual compile/mutation bundle is retained. The batch result has no
new CI check-run ID, acceptance decision or reviewer; it requires separate
authentic producing CI execution and independent mathematical evaluation.

## Step 4 — Exact-H readiness, independent reviews, genuine M

    python3 verification/research/pr113_final_source_readiness.py \
      --head "$H" --synthetic "$S" \
      --receipts /external/pr113/v3-preparation/unreviewed_v3_receipts.json \
      --bundle /external/pr113/v3-preparation/unreviewed_evidence.zip \
      --out /external/pr113/readiness.json

Expected to FAIL while any original case or claim lacks its own positive and
negative control, or any required check is red/missing. A green readiness
result is unreviewed source evidence, NOT mathematical acceptance.

After real owner authorization and independent reviewer disclosures:
review 45/45 historical case premises, all eleven claim statements,
theorem source types, axioms and semantic negative relevance. Preserve the
P-06 deterministic phase-blind limitation and D-09 mixed-initial
nonlinear-expectation versus barycenter distinction. Bind actual independent
GitHub approvals to H, evidence bundle SHA and reviewed payload SHA.

Only after premerge-full is truly satisfied can the owner authorize a
genuine ordered [B,H] Git merge M with identical synthetic tree. Then rerun
all twelve checks on M, rebuild PDF twice, inspect every PDF page and obtain
independent scholarly signoff for exact M/PDF/claim wording.

## Step 5 — Real M reproduction and final postseal authentication

The merged-M clean paper artifact must come from a real successful
clean-paper-rebuild job on main with name pr113-clean-paper-rebuild-draft.
The strict preseal gate consumes its original ZIP and an external JSON of
run_id, run_attempt, job_id, check_run_id and artifact_id. Provide the pair:

    --reproduction-zip /external/pr113/real-M-clean.zip \
    --reproduction-ids /external/pr113/real-M-clean-ids.json

final_closure_reproduction_auth.py checks original GH artifact SHA256,
run/job/check, both clean source-root PDF, log, archive, manifest and all
rendered pages. With true independent mathematical/scholarly review this
may establish POSTMERGE_PRESEAL_READY. seal_approved.py --full emits only
Permansson_Mathematical_Closure_CANDIDATE.zip.

Full-release-strict additionally requires a separately authorized exact-M
pr113-postseal-replay.yml workflow_dispatch, job postseal-archive-replay,
and GitHub artifact pr113-complete-postseal-candidate:

    --postseal-zip /external/pr113/real-M-postseal.zip \
    --postseal-ids /external/pr113/real-M-postseal-ids.json

The future producer workflow is intentionally **not added** to the
security-pinned 25-workflow inventory; it needs independent security
authorization first. The postseal authenticator replays all nested source,
PDF, page, archive and sidecar bytes. A local replay cannot self-award a
COMPLETE_ARCHIVE_REPLAY receipt. No current code may fabricate reviewers,
security approval, actual M, publication/tag or empirical Exact GR/PR proof.

## Stop conditions

Do NOT merge/tag/release while historical E_TOOLING_CLOSURE or original A2
source gate fails; code head H changes after evidence or review; main has
advanced; any of 12 CI checks fail; any of 21 original producing ZIPs is
missing/stale; any of 259 Lean declarations or 45+11 controls is missing;
historical source/premise boundaries change without review; independent
45+11 mathematical approval, exact M, PDF page review, two-clean-build
evidence or authenticated postseal replay is absent.
