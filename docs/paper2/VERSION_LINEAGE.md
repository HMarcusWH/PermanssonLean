# Version lineage and historical documentation

[Current documentation](README.md) · [Publication hub](../../paper2/README.md) · [Residual status](RESIDUAL_STATUS.md)

## Artifact versions

Each version below names a specific deliverable. The [publication manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json) is authoritative for the new manuscript assets and their upload identity.

| Artifact | Version or identity | Scope |
|---|---|---|
| [Current scientific manuscript](../../paper2/README.md) | Reviewed draft 2.0.1, 20 November 2026 | 218-page integrated exposition; 31 sections and 16 appendices |
| [Original paper](../../paper/README.md) | 0.1.8 | Frozen original manuscript and its supporting materials |
| [Original Lake package](../../lakefile.toml) | 0.1.0 | Frozen original formalization metadata |
| [Accepted research companion](../../release/v0.2.0/README.md) | 0.2.0 | Accepted release commit `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`; exporter/research source argument `5822cdff0fc360d9e368e10ff5f7576c3141a1b3` |
| [Mathematical reference guide](../reference/README.md) | 1.1.1 | Preserved 126-page, 46-chapter guide and source-navigation records |
| [Application Standard](../../application/README.md) | Draft 0.1.0 | Historical reporting/validation contract compatible with original paper 0.1.8 |
| [Successor application](../../apps/permansson/application-successor/README.md) | Numeric release 0.2.0 | `permansson-app-v0.2.0`, source `63a66c82a9ece4361f646ee13b6711192f831406`; the release's actual platform and evidence limits remain in its record |
| [Native C10 CLI](../../apps/permansson/closure-successor/README.md) | 0.1.0 | Fixed supported six-state source-bound replay |
| [Native C11 CLI](../../apps/permansson/closure-successor-c11/README.md) | 0.2.0 | Supported finite rational stationary-family replay |
| [Mathematical-closure candidate](../../release/mathematical-closure-1/README.md) | `mathematical-closure-1` | DRAFT — NOT ACCEPTED — NOT PUBLISHED; separate historical eight-page manuscript and preseal/postseal/independent-review conditions |

The accepted release and exporter/research source are different identities, as recorded in the [v0.2.0 hardening guide](../V020_HARDENING.md). The mathematical-closure candidate's builder and manifest are not the new 218-page publication package and remain unchanged.

## Source identities for v2.0.1

| Identity | Value and role |
|---|---|
| Mathematical source | `c5a36cd6189e2a249d5f4bc11f31698917dc8b10` |
| Mathematical source tree | `e3211713f1ef508ea891f534509116accaad56a4` |
| Documented repository snapshot | `f0dee1c11a20f96c9a11b380e942b9252e6ebe44` after PR #127; the manuscript calls this its publication snapshot, but the new paper PDF was not yet in that tree |
| Actual artifact upload | Recorded in the [publication manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json); use its actual containing commit for immutable artifact citations |
| Documentation and CI review | Separate candidate/head/run identities in [documentation review](DOCUMENTATION_REVIEW.md) and the relevant detached receipts |

The guide's **2,332 tracked paths** belong to its c5a source snapshot. The f0 documentation snapshot has **2,338 tracked paths**. The mathematical inventory common to those snapshots contains 798 Lean files (64 core, 710 research, 24 other) and 793 Python files. Preserve those source-qualified counts instead of treating them as an undated current-head total.

## Why current documentation is additive

The [global integrity policy](../../verification/integrity/policy.py) protects historical objects and closes specified roots, including `paper/`, `provenance/`, `application/` and `release/v0.2.0/`. Its [preservation tests](../../verification/integrity/tests/test_preservation.py) explicitly permit additions under `paper2/` and new documentation paths.

The [A2 inherited-source contract](../../verification/research/localized_prefix_support.py) also preserves the PR79 baseline outside named exceptions. Its five reviewable Markdown paths are `README.md`, `docs/README.md`, `docs/RESEARCH_BUILD.md`, `apps/permansson/closure-successor/README.md` and `apps/permansson/closure-successor-c11/README.md`. Later-added files have their own applicable contracts. The [current successor identity check](../../verification/research/pr113_a2_successor_identity.py) retains this boundary. The separately staged v2 identity profile is not activated by this documentation.

New current explanations therefore live here. Historical source, guide editions, proof records, release receipts and acceptance ledgers retain their bytes and scientific status.

## Read older documents in their own scope

| Preserved document family | How to read it now | Current route |
|---|---|---|
| [Original formalization map](../FORMALIZATION_MAP.md) and [paper verification manifest](../PAPER_VERIFICATION_MANIFEST.md) | Authorities for the frozen v0.1.8 formalization and artifact record | [Mathematical crosswalk](MATHEMATICAL_CROSSWALK.md) |
| [Old getting started](../GETTING_STARTED.md), [glossary](../GLOSSARY.md) and [contribution rules](../../CONTRIBUTING.md) | Historical contract vocabulary and preserved contribution requirements | [Current getting started](GETTING_STARTED.md), [glossary](GLOSSARY.md) |
| [v0.2.0 integration index](../V020_IMPLEMENTATION_INDEX.md), [proof ledger](../V020_RESEARCH_PROOF_LEDGER.md), [architecture](../PERMANSSON_RESEARCH_ARCHITECTURE.md) and [roadmap](../FUTURE_THEORY_ROADMAP.md) | Dated implementation contracts and earlier research checkpoints, including current-looking wording inherited from those dates | [Current mathematical routes](MATHEMATICAL_CROSSWALK.md), [residual status](RESIDUAL_STATUS.md) |
| CQ1, D0/D1/D2 and mathematical lane documents | Hypotheses, constructions and evidence at the stated lane checkpoint; later source can extend a route without rewriting that record | [Mathematical crosswalk's legacy routes](MATHEMATICAL_CROSSWALK.md) |
| [Closure specification](../../research/paper_closures/spec/README.md) and [selected-scope review](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md) | Original requirements and selected contracts present at their source; stronger paper obligations may remain | [Residual status](RESIDUAL_STATUS.md) |
| [Original verification guide](../../verification/README.md) and archived run reports | Commands and receipts for their original packages, environments and source pins | [Current verification](VERIFICATION.md) |
| [September documentation review](../DOCUMENTATION_REVIEW.md) | Historical usability/review record | [Current documentation review](DOCUMENTATION_REVIEW.md) |

## Citation and evidence changes

Root [CITATION.cff](../../CITATION.cff) retains the original companion citation. Use the new edition's [CITATION.bib](../../paper2/v2.0.1/CITATION.bib) and the publication hub's plain citation for v2.0.1. No journal, DOI or external acceptance is implied by repository availability.

The manuscript's 58 review findings concern its internal draft 2.0-to-2.0.1 revision. They do not relabel historical source or independently accept the 56 cases. The guide's frozen distribution remains 15 `PENDING`, 30 `PARTIAL_SCOPE` and 11 `SOURCE_PRESENT_REVIEW_PENDING`. [Compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md) explains consequential wording and hypothesis changes; [residual status](RESIDUAL_STATUS.md) keeps the distinct remaining obligations visible.
