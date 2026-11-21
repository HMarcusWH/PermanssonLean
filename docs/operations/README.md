# Current operations and historical workflow guidance

[Documentation index](../README.md) · [Version lineage](../paper2/VERSION_LINEAGE.md) · [Current verification](../paper2/VERIFICATION.md) · [Documentation review](../paper2/DOCUMENTATION_REVIEW.md)

**Status checked against main `09c4341c22dfb22c750bfb02d4eaa4486782b77d`,
21 November 2026.** Start here when an older operations document describes
PR #113 as open, refers to 25 installed workflows, or says the archive job
currently fails with `E_TOOLING_CLOSURE`. Those statements belong to their
recorded checkpoints. Their original bytes remain evidence of that history.

## Current operational route

The [owner-engineering archive successor contract v2](ARCHIVE_SUCCESSOR_CONTRACT_V2.md)
and its [committed policy](../../verification/research/archive_successor_policy_v2.json)
govern the present archive successor check. Policy v2 has been in effect since
[PR #118](https://github.com/HMarcusWH/PermanssonLean/pull/118) merged on
1 November 2026. It extends [contract v1](ARCHIVE_SUCCESSOR_CONTRACT_V1.md),
adopted through [PR #116](https://github.com/HMarcusWH/PermanssonLean/pull/116).

The executable is still named
[`archive_successor_gate_v1.py`](../../verification/research/archive_successor_gate_v1.py);
that name does not mean it reads policy v1. The current
[`archive-reproducibility` job](../../.github/workflows/research-integrity.yml)
runs the unchanged archive adversaries, then this gate using policy v2. The
gate separately binds the immutable historical T replay and the inspected
current source C. It preserves the original T/C failure as history.

| Workflow profile | Present role | Source route |
| --- | --- | --- |
| 26 installed workflow definitions | Current owner-engineering profile: the earlier 25 plus the exactly pinned application-release workflow | [Policy v2](../../verification/research/archive_successor_policy_v2.json), [workflow contract](../../verification/integrity/workflow_contract.py), [installed definitions](../../.github/workflows/) |
| 25-workflow profile | Historical preactivation inventory and the original scope of contract v1; its inherited obligations remain where v2 retains them | [Contract v1](ARCHIVE_SUCCESSOR_CONTRACT_V1.md), [v1 policy](../../verification/research/archive_successor_policy_v1.json) |
| Proposed 30-workflow T/T2+A2 profile | Inactive PR #113 migration proposal; its files under `docs/operations/` are staged sources, not installed workflows | [Staged checkpoint](PR113_TT2_A2_V2_IMPLEMENTATION_CHECKPOINT_2026-10-25.md), [cutover design](PR113_T2_FINAL_REPAIR_AND_CUTOVER_2026-10-28.md), [candidate workflow directory](pr113_unapproved_workflows/README.md) |

The proposed 30-workflow profile predates the application-release addition and
does not include it. Its disposable 25-to-30 rehearsal therefore omits that
addition, as [contract v2 explains](ARCHIVE_SUCCESSOR_CONTRACT_V2.md#effect-on-the-staged-pr-113-checks).
A future activation would require its own reconciled source contract and
review; the present 26-file inventory does not demonstrate that activation.

[PR #113](https://github.com/HMarcusWH/PermanssonLean/pull/113) merged on
29 October 2026 at `3492b26707788293ca88c66637b6ba021c7e478d`.
Its merge did not activate the staged 30-workflow proposal or supply independent
mathematical, security or scholarly acceptance. The separate
[infrastructure reviewer roster](../../research/certification/infrastructure_reviewer_authority.json)
at the inspected source remains `UNCONFIGURED`.

## Installed definitions, observed execution and enforced rules

These are three separately evidenced facts:

| Question | Evidence to inspect | Scope of the answer |
| --- | --- | --- |
| What can run? | Workflow definitions and the exact source/policy pins above | There are 26 installed definitions at the inspected head. Event filters determine which can run; the application-release workflow is manual-only. |
| What actually ran? | Exact commit, event, run attempt, job, steps and retained artifacts | The [Research integrity run on main `09c4341c`](https://github.com/HMarcusWH/PermanssonLean/actions/runs/44834661690) succeeded. Other workflow results and later heads require their own observations; see the [merged-head review](../paper2/DOCUMENTATION_REVIEW.md). |
| What does GitHub enforce before a merge? | Effective rulesets and branch-protection configuration at the time of inspection | Source code calling a context “required” and a green workflow do not establish live enforcement. A workflow-file count is not a required-job count. |

During the 21 November audit, the visible
[`Protect main` ruleset, ID 25838177](https://github.com/HMarcusWH/PermanssonLean/rules/25838177)
was active and contained deletion, non-fast-forward and pull-request rules,
with no `required_status_checks` entry in that ruleset. Classic branch-protection
administration data was unavailable to that audit. This bounded observation
does not determine every effective protection mechanism and must be refreshed
before a claim about current enforcement.

## Read historical entrypoints in their recorded scope

The following five entrypoints were last updated on 24 October 2026 at the
source commits shown. Their “current,” “pending” and “do not merge” language
describes that pre-merge checkpoint. The files are preserved; use the current
routes in this table for subsequent operational state.

| Historical entrypoint and last-update source | Statement to interpret historically | Current route |
| --- | --- | --- |
| [Closure readiness](closure_readiness.md), [`5917c437`](https://github.com/HMarcusWH/PermanssonLean/commit/5917c437353093b49e67fa3cb8789018be364ece) | PR #113 remains a draft; candidate twelve-context policy; original archive tooling mismatch | [Current profile and merged status](#current-operational-route); [execution versus enforcement](#installed-definitions-observed-execution-and-enforced-rules) |
| [v3.1 gate usage and limits](pr113_v31_gate_usage_and_limits_20261024.md), [`52f00c9e`](https://github.com/HMarcusWH/PermanssonLean/commit/52f00c9ecb60219da31e7ee6780f6c5debfb5b87) | Everything remains on PR #113; 25-workflow source boundary and unactivated producers | [Contract v2](ARCHIVE_SUCCESSOR_CONTRACT_V2.md); [remaining acceptance boundaries](#acceptance-and-release-boundaries) |
| [Post-log implementation handoff](pr113_postlog_implementation.md), [`14f1a6a9`](https://github.com/HMarcusWH/PermanssonLean/commit/14f1a6a9bf0d49971702650764eba5653f8a7ec9) | Pre-merge source readiness, missing external receipts and historical archive failure | [Current operational route](#current-operational-route); [preserved certification handoff](pr113_implementation_scope_and_certification_handoff.md) |
| [Unapproved T/T2 security dossier](pr113_t2_security_review_dossier_unapproved.md), [`75e9e7d9`](https://github.com/HMarcusWH/PermanssonLean/commit/75e9e7d94bc485ae7594aecc51034727ce325ba7) | Original required archive job fails and the installed inventory contains 25 files | [Current owner-engineering archive contract](ARCHIVE_SUCCESSOR_CONTRACT_V2.md); the independent T2 review remains a separate obligation |
| [Unapproved workflow directory](pr113_unapproved_workflows/README.md), [`52f00c9e`](https://github.com/HMarcusWH/PermanssonLean/commit/52f00c9ecb60219da31e7ee6780f6c5debfb5b87) | Restoring 25 installed files after removing three premature additions | [Current 26-file profile](#current-operational-route); staged files remain outside `.github/workflows/` |

Additional operations records retain these roles:

| Record family | Role and successor route |
| --- | --- |
| [R01–R05 repair handoff](pr113_R01_R05_repair_handoff_20261024.md), [R1–R6 engineering handoff](PR113_R1_R6_ENGINEERING_HANDOFF_UNAPPROVED.md), [post-2FA reconciliation](pr113_post2fa_scope_reconciliation_2026-10-26.md) | Dated implementation and authority checkpoints; read current operational status above and preserve each original evidence boundary. |
| [Research CI scope repair](PR113_RESEARCH_CI_SCOPE_REPAIR_2026-10-28.md), [merge-completion plan](PR113_MERGE_COMPLETION_2026-10-28.md) | Historical dual-source replay design and ordered pre-merge plan. The documented PR #113 merge is subsequent history, not evidence that every listed independent review or activation occurred. |
| [PR #115 archive diagnosis](PR115_ARCHIVE_T_T2_REPAIR_INTEGRATION_2026-10-29.md) | Its 31 October status note already routes the obsolete failure diagnosis to contract v1; use [v2](ARCHIVE_SUCCESSOR_CONTRACT_V2.md) for the application-release addition. |
| [Original-21 dispatch contract](pr113_original21_frozen_head_dispatch_contract.md), [selection survey](pr113_selection_candidate_survey.md), [trigger candidates](pr113_unapproved_workflows/trigger_candidates/README.md) | Original producer identities, source/control selection and unactivated trigger proposals; registry presence does not establish execution or reviewer acceptance. |
| [Two-stage historical cutover](pr113_two_stage_historical_cutover_v1.md), [required-gate replacement candidates](pr113_required_gate_replacement_unapproved/), [external rehearsal harness](pr113_external_rehearsal/README.md) | Staged migration and external-runner designs. The external harness's open-PR #113 freshness condition belongs to that historical preactivation workflow and is not a present-day command for the merged PR. |

## Acceptance and release boundaries

The current owner-engineering policy supplies its narrowly stated archive
route. It does not supply the independent T2 security review or activate the
staged replacement. The [implementation/CERT handoff](pr113_implementation_scope_and_certification_handoff.md)
retains its source-specific mathematical and scholarly requirements; the
[current residual ledger](../paper2/RESIDUAL_STATUS.md) explains the mathematical
obligations without changing historical case dispositions.

Release identities are separate as well. The
[successor application's numeric release record](../../apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md)
defines the published `permansson-app-v0.2.0` scope and platform evidence.
The [accepted research companion](../../release/v0.2.0/README.md),
[unaccepted mathematical-closure candidate](../../release/mathematical-closure-1/README.md)
and [v2.0.1 manuscript publication package](../../paper2/v2.0.1/README.md)
have their own identities and conditions. A successful current CI job does not
change any of those records or establish empirical identification.
