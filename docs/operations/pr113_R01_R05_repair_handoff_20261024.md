
# PR113 R01-R05 repair handoff — source candidates, not acceptance

Date: 2026-10-24
Repository: HMarcusWH/PermanssonLean
PR: https://github.com/HMarcusWH/PermanssonLean/pull/113

All five repair work packages are coded as review-pending candidates.
Original 45 acceptance criteria, eleven new claims, 259 kernel source targets,
Lean 4.34.0, historical T archive/supplement and original 25-workflow
inventory were NOT altered by this batch.

## R01 — Fast engineering QA

Use a genuine clean checkout of final H:

    python3 verification/research/pr113_fast_engineering_preflight.py --head "$H" --out /external/pr113/fast-qa

The QA checks Python source ASTs and 17 focused regression suites, including
the new source-control producer v3.1 tests. This is not the original required
Research Lean suite or historical archive approval.

## R02 — Stable TeX stage and no cache contamination

The original two source roots are still separately cloned with no hardlinks.
The sequential builder now creates the same absolute fresh _canonical_tex_stage
path for each run. After draft verification the complete generated directory
is moved intact to first/ or second/, and a remaining stage is rejected.
This avoids path-dependent TeX line wrapping without stripping log bytes.

    python3 release/mathematical-closure-1/reproduce_clean_sources.py --source-head "$H" --out /external/pr113/clean-paper

A standalone local pdfTeX smoke passed identical PDF/log bytes, but final-H
and postmerge-M manuscript SHA256, ZIP, manifest and page review remain pending.
This README modification intentionally triggers the existing clean-paper
workflow path filter at the new exact H. No workflow file was modified.

## R03 — Actual historical A2 Python execution profile

The original A2 compiler script was introduced at commit
f71a76032b169aac7bfe0694aa715339a94d4e05 (not at the earlier
674c1b55 inherited source baseline). The dual-run candidate now:
- authenticates historical source and support Git blobs and clean checkout;
- requires the original historical executable blob from the introducing commit;
- launches the executable and support from the HISTORICAL checkout in its
  own Python process, with source PYTHONPATH contamination removed;
- verifies that execution's own actual source/commit/tree receipt;
- then separately runs current H A2 successor with real positive and four
  Lean semantic false mutants.

    python3 verification/research/pr113_dual_a2_compiler.py --historical-source /real-A2-original --historical-head "$A2_HISTORICAL_SHA" --current-source /real-H --current-head "$H" --out /external/pr113/dual-A2

A successful successor remains unreviewed; it cannot disable the mandatory
inherited original A2 Research Lean check. Versioned CI migration requires
owner and independent security authorization.

## R04 — Original T/H dual archive security report

Historical unmodified T is replayed from its own real clean checkout in an
actual isolated nonroot network namespace. Current H separately runs every
original workflow-integrity adversarial method. No Python source import path
can substitute H's verifier for the historical one.

    python3 verification/research/pr113_dual_tooling_candidate.py --historical-T-source /real-T --current-source /real-H --head "$H" --output /external/pr113/dual-T-H

The detached T2_security_review_candidate.json now retains immutable T/H
Git source blobs for two known changed canonical tooling files, the frozen
historical manifest hash, both complete original report SHA256 digests and
25 original workflow inventory entries. All approval fields remain false.
The current required archive E_TOOLING_CLOSURE is not silently waived.

## R05 — Extra authenticated source-control CI producers v3.1

New files:
- verification/research/final_closure_extra_producers_v31.py
- verification/research/test_final_closure_extra_producers_v31.py
- research/paper_closures/post_merge_112/additional_control_producers_v3_1.schema.json

The original 21 GitHub producing artifacts (4 compiler, 9 appended-source
semantic, 8 legacy observation) remain mandatory without rewriting v2 or v3.
The additional versioned v3.1 contract covers **76 source-control owners**:
45 original role-selected positives, 20 original legacy source-appended
negatives and 11 claim-specific positive-and-negative PAIRS (22 directions).

Each new producer must be a genuinely reviewed source-controlled workflow
with authentic GitHub run attempt, job ID, check-run ID, original artifact
SHA256 and byte-for-byte owner index and receipt in the original ZIP. Wrong
head, borrowed artifact, missing mathematical owner, invented review or
changed source/workflow Git blob must fail. This contract does NOT install
a new workflow or accept any local declaration of independent approval.

After owner-approved producing workflows genuinely run, provide original
strict-v3 receipt JSON/ZIP, additional v3.1 contract JSON, original artifact-ID
ZIP files, and exact proposed workflow Git blob SHA JSON:

    python3 verification/research/final_closure_extra_producers_v31.py --head "$H" --original-v3-receipts /external/strict-v3.json --original-v3-zip /external/strict-v3.zip --additional-contract /external/v3_1-controls.json --additional-zips /external/control-artifacts --reviewed-workflow-blob-candidates /external/workflow-blobs.json --output /external/v3_1-unreviewed.json

Even a genuinely source-attributed output remains strictly unreviewed:
security approval false, 0/45 cases accepted, 0/11 claims accepted,
no merge or mathematical release.

## R06-R11 still require external execution/authorization

First get required Research/Archive green through genuinely reviewed
historical trust migration. Freeze B/H/S, get twelve exact-H required checks,
and all 4+9+8 original CI artifacts and 259 Lean type/axiom receipts.
Execute and authenticate original 45 positive test routes and 45 negatives
(including twenty source-appended legacy replays), plus eleven genuine
claim-specific positive/false semantic controls. Independent nonauthor
mathematical reviewers must accept 45/45 and 11/11 against EXACT H and
original criterion wording. No claims can be inferred from generic CI.

Only owner-authorized genuine merge M permits 12 exact-M checks, independent
PDF/page scholarly review, matching two-root PDF/ZIP manifests, candidate
seal, independent authorized external postseal replay and explicit publication.

Stop if any required check/source SHA differs; never substitute a successful
mock, unapproved status flag, borrowed old-head artifact or synthetic review.
