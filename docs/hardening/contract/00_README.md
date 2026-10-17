# Contract provenance and companion source register

Read this companion before interpreting the citations in the five supplied documents:

- [Proposal audit](01_Proposal_Audit.md)
- [Implementation specification](02_Implementation_Spec.md)
- [Acceptance plan](03_Acceptance_Test_Plan.md)
- [Rollout runbook](04_Rollout_Runbook.md)
- [Implementing-agent directive](AGENT_BUILD_DIRECTIVE.md)

Two active documents retain their canonical Git blobs unchanged from `2ff920d6ab470cd49f6f392f23855676ac1f8db3` and byte-match their supplied Markdown originals: `01_Proposal_Audit.md` and `AGENT_BUILD_DIRECTIVE.md`. The other three active documents carry explicit repository amendments. Their byte-identical supplied originals remain separately inspectable:

| Active document and amendment | Pristine supplied original | Original Git blob |
|---|---|---|
| [Implementation specification](02_Implementation_Spec.md): supported offline launcher, candidate-bound archive arguments, and mandatory one-time actual-S Lean-scope acceptance in K4. | [supplied/02_Implementation_Spec.md](supplied/02_Implementation_Spec.md) | `8d0379cc65a9eb056a06673a5b82147dca0468e5` |
| [Acceptance plan](03_Acceptance_Test_Plan.md): PRES-23 covers additions, edits and deletions in both complete Lean trees and both roots, including unprotected paths; its unit fixtures cannot replace K4's actual-candidate evidence. Its opening also distinguishes the new probe subset from unavailable original E1 experiments. | [supplied/03_Acceptance_Test_Plan.md](supplied/03_Acceptance_Test_Plan.md) | `38e9edc01043a9f912c2a652912dfc2ea1a9a570` |
| [Rollout runbook](04_Rollout_Runbook.md): candidate-bound enforced offline invocation and mandatory premerge scope report joined to independently captured current H/B/S. | [supplied/04_Rollout_Runbook.md](supplied/04_Rollout_Runbook.md) | `ea30c552ef47a02aa1873a259d96fb09c4781021` |

Local attributes rules preserve these references' original bytes through Windows checkouts and staging. None of the original Downloads files is changed. The one-time maintenance scope condition adds no permanent workflow job or required context, and no acceptance case ID or level; future additive research remains governed by the permanent preservation policy.

The original full package ZIP, its `00_README.md`, `sources/Original_Proposal.txt`, and the author's E1 probe program/results were **NOT_SUPPLIED** to this repository change. This file is a newly authored companion, **not the recovered original source register**. The three [registries](../registries/) are independently derived repository records, as their provenance fields state; they are not represented as recovered package bytes.

## Reconstructed runbook template

The runbook's literal `templates/research-integrity.yml` reference resolves to the [reconstructed template](templates/research-integrity.yml). This is **NOT_RECOVERED_ORIGINAL_PACKAGE_TEMPLATE**. It copies the reviewed maintenance workflow's exact canonical bytes; it does not reconstruct an unavailable author's template or claim that installing it has already produced genuine PR CI or activated required checks. Production modules, the historical supplement and tests must exist before use. The reviewed required workflow runs on main PRs and main pushes; optional manual dispatch is excluded from this required-check profile.

Template provenance manifest:

| Field | Exact value |
|---|---|
| Reviewed maintenance source | [`.github/workflows/research-integrity.yml` at `049d2620317afd10f8a584254d768f36af1d4979`](https://github.com/HMarcusWH/PermanssonLean/blob/049d2620317afd10f8a584254d768f36af1d4979/.github/workflows/research-integrity.yml) |
| Source Git blob | `52c50993395dc794d1ab8d8dae7357ba39a72c4c` |
| Canonical payload | 4,760 bytes, UTF-8 with LF |
| SHA-256 | `70cd7e8569beb995981be210369f57c34460289e6a5890c54153683a26939093` |
| Review boundary | Any profile change requires a reviewed checker-policy update; the candidate-owned checker does not authenticate its own review. |

The action commits in this reviewed source match references actually observed in the separately captured accepted R Research job `117434492474`, run `39045919534`. The [captured log](https://github.com/HMarcusWH/PermanssonLean/blob/e314ccc2b3587065425a0357874ad5580cce841d/archival/v0.2.0/supplement-1/evidence/runs/job-117434492474-logs.json) is a later **normalized connector** record, not the missing original package or a raw HTTP log response; its SHA-256 is `b69acc4f08e96bba69f9d9a4b417adeee6bd92385307b21c789cd469b8d7ff91`.

| Action | Observed accepted-CI commit retained in the reviewed template |
|---|---|
| `actions/checkout` | `11d5960a326750d5838078e36cf38b85af677262` |
| `actions/setup-python` | `a26af69be951a213d495a4c3e4e4022e16d87065` |
| `actions/upload-artifact` | `ea165f8d65b6e75b540449e92b4886f43607fa02` |

The runbook contains no other literal `templates/...` path. The implementation specification's schema and production-tool paths describe required build outputs, not additional recovered package files.

## Original citation labels: what can be established

The original register's exact label assignments cannot be recovered from the five documents alone. The table distinguishes associations identifiable from the supplied audit's text from unresolved labels. Linked companion sources are inspectable support for the topic; they do not manufacture the missing author's bibliography or HTTP captures.

| Original label | Association and inspectable companion source | Provenance limit |
|---|---|---|
| P | The proposal described by the supplied audit and the earlier conversation. | `sources/Original_Proposal.txt` is **NOT_SUPPLIED**; no byte-identical original proposal file is claimed. |
| R1 | The text identifies the old preservation/checker boundary. Inspect the [accepted verifier][verifier] and [accepted manifest][manifest]. | Contextual association; original register entry not supplied. |
| R2 | The text names `build_release.tex_document`. Inspect the [accepted builder][builder] and its [verifier dependency][verifier]. | Contextual association; the new probe independently checks these exact inputs. |
| R3 | No individual R3 citation appears in the supplied proposal audit. | Exact target **NOT_SUPPLIED**; no assignment invented. Additional accepted inputs are listed below. |
| R4 | No individual R4 citation appears in the supplied proposal audit. | Exact target **NOT_SUPPLIED**; no assignment invented. |
| R5 | No individual R5 citation appears in the supplied proposal audit. | Exact target **NOT_SUPPLIED**; no assignment invented. |
| R6 | Part of the grouped R6–R8 audit-time main/protection/ruleset observation. The fixed [accepted commit][accepted] is independently inspectable. | Individual label assignment and original API response **NOT_SUPPLIED**. No current main or settings assertion follows. |
| R7 | Part of the same grouped audit-time observation. Relevant API entry points are [branch protection][protection-api] and [repository rules][rules-api]. | Individual label assignment and original API response **NOT_SUPPLIED**. Endpoint documentation is not an observed configuration. |
| R8 | Also cited for workflow/check names. Inspect the [accepted workflows][workflows] and [accepted source receipts][receipts]. | Original check-run/App capture **NOT_SUPPLIED**. Workflow definitions alone do not prove live check execution or current enforcement. |
| R9 | The text identifies artifact `12106535829`, run `39045919534`. Inspect the [artifact endpoint][artifact-api] and a [later separately captured metadata record][later-artifact]. | Later capture is not the audit author's missing HTTP response. Expiry/availability statements in the supplied audit describe its observation time. |
| R10 | The text identifies the [acceptance comment][acceptance-comment] and [code-review comment][review-comment]. A [later captured comment][later-review] is also inspectable. | The code-review comment is not a counted `APPROVED` review or mathematical peer-review certificate. |
| G1 | No individual G1 citation appears in the supplied proposal audit. | Exact original documentation target **NOT_SUPPLIED**; no assignment invented. |
| G2 | Bundle/reference/prerequisite topic: [Git bundle manual][git-bundle]. | Newly linked official companion source; original bibliographic entry not recovered. |
| G3 | Bundle payload/import/object-check topic: [bundle format][bundle-format] and [Git fsck][git-fsck]. | Documentation does not itself reproduce the author's reported truncated-bundle experiment. |
| G4 | Object replacement/history topic: [Git replace][git-replace] and [partial clone][partial-clone]. | Newly linked official companion sources; original bibliographic entry not recovered. |
| G5 | Required-check/skip behavior: [GitHub required-check troubleshooting][checks]. | Current official documentation; not evidence that this repository has required checks enabled. |
| G6 | Review eligibility: [GitHub approval documentation][approvals]. | Current official documentation; no eligible human reviewer is identified here. |
| G7 | Rules/read-back/bypass topic: [GitHub rules API][rules-api]. | Current official documentation; no settings write, read-back or enforcement claim is made here. |
| E1 | The supplied audit claims source-ZIP reconstruction, exporter checks and toy bundle experiments. | Original program/results **NOT_SUPPLIED**. The new independent record below covers only its explicitly executed subset. |

## Accepted sources available independently of the missing package

All accepted-source links below are pinned to A, `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`; they are not moving branch tips:

- [Manifest][manifest]: original 340-file inventory and accepted artifact hashes.
- [Builder][builder], [verifier][verifier], [manuscript][manuscript], [TeX][tex], [package checker][packager] and [C10 checker][c10]: actual accepted source/artifacts.
- [Acceptance receipts][receipts]: seven historical milestone identities and captured evidence summaries. The later final R capture is separate.
- [Authority pins](../registries/authority_pins.json), [369-entry inventory](../registries/protected_inventory_369.json), and [archive refs](../registries/archive_commit_registry.json): repository-derived reference records, not a recovered author package.

The later metadata/comment links point to immutable maintenance commit `e314ccc2b3587065425a0357874ad5580cce841d`, outside the accepted kit. Their acquisition index identifies their actual representation. Copying a response or storing a checksum does not create publisher authentication.

## New independent probe record, with explicit limits

[`evidence/source_probes.json`](evidence/source_probes.json) is now an inspectable **new independent reproduction**, not the unavailable original E1 file. Its `provenance` and `original_audit_inputs` fields preserve that distinction. It records only accepted Git identity/input checks, 340 + 29 inventory checks, complete isolated TeX regeneration, and the wrong-revision control.

Reproduce that subset from a clone already containing A, using Python and Git with no additional packages:

```text
python -B docs/hardening/contract/evidence/reproduce_source_probes.py --repo . --output NEW_EXTERNAL_RESULT.json
```

The [script](evidence/reproduce_source_probes.py) reads fixed Git objects, uses an isolated `-I -S -B` interpreter for accepted TeX rendering, never fetches missing history, and refuses to overwrite a result file. Run it from the repository root; use an external scratch location for the output. Runtime/timestamp fields may differ on a new execution. This documentation probe is not a production gate or a proof-environment installer.

The following remain unestablished by this record: the author's original source-ZIP reconstruction/hash observation, original toy-Git experiments, original live API observations, new CI acceptance, network-isolated archival restoration, fresh Lean execution, current repository protection and publication. The source ZIP digest quoted in the supplied audit is retained only as an **author-reported, not independently reproduced** value.

Statements such as “Live GitHub still reports”, unexpired artifact availability, and proposed future deployment in the supplied documents refer to their audit/specification context. They must not be read as current main/settings/availability facts. Current head/base/synthetic CI and administrative completion require separate exact-source receipts. In particular, the 108 cases are requirements; this four-check companion record is not 108 completed acceptance cases.

[accepted]: https://github.com/HMarcusWH/PermanssonLean/commit/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618
[verifier]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/verify_release.py
[manifest]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/manifest.json
[builder]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/build_release.py
[manuscript]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/manuscript.json
[tex]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/output/pdf/Permansson_Research_Companion_v0.2.0.tex
[packager]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/package_release.py
[c10]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/c10_archive_validation.py
[receipts]: https://github.com/HMarcusWH/PermanssonLean/blob/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/release/v0.2.0/acceptance-evidence.json
[workflows]: https://github.com/HMarcusWH/PermanssonLean/tree/d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618/.github/workflows
[artifact-api]: https://api.github.com/repos/HMarcusWH/PermanssonLean/actions/artifacts/12106535829
[later-artifact]: https://github.com/HMarcusWH/PermanssonLean/blob/e314ccc2b3587065425a0357874ad5580cce841d/archival/v0.2.0/supplement-1/evidence/R-c10-artifact-metadata.json
[acceptance-comment]: https://github.com/HMarcusWH/PermanssonLean/pull/76#issuecomment-6236142249
[review-comment]: https://github.com/HMarcusWH/PermanssonLean/pull/76#issuecomment-6235925253
[later-review]: https://github.com/HMarcusWH/PermanssonLean/blob/e314ccc2b3587065425a0357874ad5580cce841d/archival/v0.2.0/supplement-1/evidence/final-code-review-comment.json
[protection-api]: https://docs.github.com/en/rest/branches/branch-protection
[rules-api]: https://docs.github.com/en/rest/repos/rules
[git-bundle]: https://git-scm.com/docs/git-bundle
[bundle-format]: https://git-scm.com/docs/gitformat-bundle
[git-fsck]: https://git-scm.com/docs/git-fsck
[git-replace]: https://git-scm.com/docs/git-replace
[partial-clone]: https://git-scm.com/docs/partial-clone
[checks]: https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks
[approvals]: https://docs.github.com/en/pull-requests/how-tos/review-pull-requests/approving-a-pull-request-with-required-reviews
