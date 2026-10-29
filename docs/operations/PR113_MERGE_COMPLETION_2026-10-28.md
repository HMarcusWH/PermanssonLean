# PR #113: one completion sequence

Baseline inspected: `4764861bf1384f3e7cd13840f4bd7fcdcc795064`.
This plan distinguishes deployed code, actual execution, and external authority.
It is not a review receipt, activation authorization, merge, or release.

## Findings and the source repair in this change

The baseline Research run (40608689212) completed 1,883 tests with only the
original historical A2 source-contract rejection remaining. The archive run
(40608689053) passed its 35 adversarial tests and rejected current tooling with
`E_TOOLING_CLOSURE`. Those historical verifiers must not be rewritten.

The reviewed candidate has one additional **post-activation** integration defect:
`test_pr113_a2_successor_compiler.py` unconditionally imported the v1 compiler,
whose identity checker pins the current 25-workflow source and original A2 test.
The 30-workflow cutover intentionally changes those pins. The existing eight-suite
disposable rehearsal did not execute this separate actual-Lean test.

This patch keeps both native compilers unchanged and routes that mandatory test
through `pr113_a2_compiler_route_v3.select_compiler`. The complete exact-Git
workflow audit, not a filename count or environment variable, selects v1 for
staged-25 and v2 for active-30. A failed audit or compiler never falls back to
another profile. Both paths retain the original 40 declarations, positive
fixture, all four semantic mutations, source checks and nonacceptance flags.
The receipt format must match the selected compiler. Thirteen routing regressions
are added to Research discovery and the fast preflight now lists 53 suites.

## Ordered work to make this infrastructure PR merge-ready

| Step | Work and completion evidence | Responsibility / status |
|---|---|---|
| 1 | Deploy the phase-selected actual-Lean consumer, routing regression suite and preflight entry together. Preserve the native v1/v2 and historical A2 verifiers. | Source repair in this patch |
| 2 | Run exact-new-head fast QA, disposable direct-C and ordered-S rehearsal, and the actual Lean compiler tests. Retain failure-level logs. The original historical checks may remain red before the authorized cutover; do not call that a green required run. | Engineering execution |
| 3 | Reproduce original T in its exact isolated checkout; reproduce original A2 in its exact checkout; compile the successor separately. Review the full source/test/manuscript implementation matrix and clean draft reproduction. Source discovery is not independent 45/11 certification. | Genuine preactivation evidence |
| 4 | Obtain the actual independent security reviewer's GitHub identity, disclosure and owner authorization. Configure `research/certification/infrastructure_reviewer_authority.json` before final source review. An empty roster, self-review, or invented approval must block. | Owner/reviewer input; currently absent |
| 5 | Freeze the revised proposal and independently review all candidate workflow/guard bytes and called verifiers. Obtain a separate owner decision to install that exact proposal. This source review precedes installation; final artifact attestation follows producer execution. | External source review and installation authority |
| 6 | Install exactly ten source paths atomically: two workflow replacements, five workflow additions and three verification guards. Verify 30 installed workflow blobs, with 23 unchanged retained workflows. Do not change proposal metadata to pretend it is an approval. | Blocked until step 5 |
| 7 | Execute the real branch-push historical producer at the final installed head. Require successful preflight and distinct original-T/current-H and original-A2/current-H jobs in one successful run attempt. Preserve the original ZIP bytes, IDs, digests and source tree. | Real GitHub execution, not a local receipt |
| 8 | Obtain an actual latest independent APPROVED review for the final head and original producer artifacts. Bind the existing five-field attestation contract exactly; do not add guessed IDs or unsupported fields. Supply genuine producer/review IDs through repository variables. | External artifact attestation and administrator inputs |
| 9 | Rerun `research` and `archive-reproducibility` at the **same final head** after inputs exist. Require every applicable downstream step plus all twelve exact-source required contexts. Any source edit restarts affected review and evidence. | Final CI, no skipped-required-step acceptance |
| 10 | Verify effective main protection enforces the intended checks/review. Mark ready only after the applicable criteria are met. Obtain a separate owner merge decision; perform and authenticate ordered `[B113,H113]` merge and main CI. | Owner/admin; not performed by this patch |
| 11 | Open the actual successor CERT PR. Independent 45-case/11-claim certification, scholarly approval, final seal and publication stay in CERT. | Deferred, not waived |

These are dependencies, not independent tasks that can all be completed by a
source-code commit. No source patch can supply a non-author's genuine review.

## Verification commands before the source freeze

Use a clean, complete checkout, run Python with `-B`, and keep outputs outside it.
`H` is obtained from the checkout being tested; do not reuse the baseline SHA.

```sh
H="$(git rev-parse HEAD)"
OUT="$(mktemp -d)"
python3 -B -m unittest discover -s verification/research -p test_pr113_a2_compiler_route_v3.py -v
python3 -B verification/research/pr113_fast_engineering_preflight.py --head "$H" --out "$OUT/fast"
python3 -B verification/research/pr113_disposable_transition_rehearsal.py --head "$H" --out "$OUT/disposable.json"
# Requires the pinned Lean installation and clean, pinned dependencies:
python3 -B -m unittest discover -s verification/research -p test_pr113_a2_successor_compiler.py -v
```

The eight-suite disposable rehearsal is still an engineering rehearsal, not
original T replay, original A2 compilation, or an authenticated required check.
During the reviewed cutover, execute the routing test and the real compiler test
again in the actual 30-workflow checkout. Full Research discovery must not omit
these tests. The new routing tests exercise synthetic profile boundaries;
they are not themselves proof of Lean compilation or security review.

## Exact installation surface

Use `pr113_disposable_transition_rehearsal.planned_sources` and the source-pinned
manifests to obtain target/source/blob triples. The ten targets are:

- `.github/workflows/research-lean.yml`
- `.github/workflows/research-integrity.yml`
- `.github/workflows/pr113-historical-migration-candidates.yml`
- `.github/workflows/pr113-original-positive-controls-candidate.yml`
- `.github/workflows/pr113-postseal-replay.yml`
- `.github/workflows/pr113-source-controls-v3_1.yml`
- `.github/workflows/pr113-preseal-fullscope.yml`
- `verification/integrity/workflow_contract.py`
- `verification/integrity/tests/test_workflow.py`
- `verification/research/test_localized_prefix_compiler.py`

Their staged sources remain under `docs/operations/`. This patch does not copy
those sources into protected active paths. Before installation, compare the
entire intended diff and source modes to the independently reviewed proposal;
reject a changed PR head, dirty source, an extra path or altered historical byte.

## Artifact attestation and final required checks

The existing review parser accepts one `PERMANSSON-INFRA-SECURITY-V1:` JSON
attestation with exactly `head_sha`, `workflow_sha256`, `T_artifact_sha256`,
`A2_artifact_sha256`, and `original_base_sha`. The final head binds the complete
reviewed source profile. Generate all values from real final-source and original
artifact bytes; do not commit external run/review IDs to source.

Runtime inputs are `PR113_HISTORICAL_PRODUCER_RUN_ID` and `PR113_SECURITY_REVIEW_ID`.
Successful producer execution does not itself authorize the security review.
The initial required runs can fail while those inputs are absent; authenticate
and rerun them after the approved inputs exist, without changing source.

All twelve required contexts are: `research`, `build`,
`frozen-source-preservation`, `multiagent-protocols`, `approx-quotient`,
`release-export-integrity`, `archive-reproducibility`, `executable-verification`,
`research-release`, `integrity-portability-windows`,
`Application contract (ubuntu-latest)`, and `Application contract (windows-latest)`.

For the PR event, require C10 generation/verification, D0 reports, the default
build, import coverage and source firewall to execute successfully. Do not
confuse seven successful workflows with all twelve required job contexts.
Do not borrow old-head successes or call an intended historical rejection a pass.

## Explicit non-actions

No original archive, original A2 proof provider, native compiler, protected
workflow, reviewer roster, repository setting, merge or publication was altered
by the source repair in this change. Activation and final merge remain blocked
until their respective genuine approvals and execution evidence exist.
