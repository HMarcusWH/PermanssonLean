# Permansson — Mathematical Reference Guide v1.1.1

**Current proofread technical reference** (20 November 2026). The guide is six volumes, 46 chapters and 126 A4 pages. It documents the frozen core, evolving research library, finite numerical applications, exact verification and bounded real-world casebook. No independent mathematical case-acceptance is asserted by the documentation itself.

- [Read the complete PDF](Permansson_Mathematical_Reference_Guide_v1.1.1.pdf)
- [Read/edit the Markdown](Permansson_Mathematical_Reference_Guide_v1.1.1.md)
- [Navigate 46 chapters to exact cited files](CHAPTER_SOURCE_CROSSWALK.md)
- [Navigate all 56 certification cases through their 166 source catalog entries](CASE_SOURCE_CROSSWALK.md)
- [Inspect every tracked source/module, with Git blob SHAs and suggested reading paths](MODULE_MANIFEST_v1.1.1.json)

## Related second-edition manuscript

The [reviewed manuscript v2.0.1](../../paper2/README.md) is the current integrated scientific exposition. This v1.1.1 guide remains the preserved 46-chapter technical reference with its original hashes, source pins and case dispositions. Use the [new guide-to-paper map](../paper2/GUIDE_TO_PAPER.md) to navigate all 46 chapters, all 56 literal cases and the 166 source-catalog identifiers into the manuscript's actual section/appendix structure.

The paper's section IDs and the guide's chapter IDs are separate namespaces. Editorial topic routes, source correspondence and independent acceptance remain separate. The guide's 2,332-file inventory stays pinned to c5a; the later f0 repository snapshot has 2,338 tracked paths because it includes this guide publication. Neither count is a fresh compiler result. See [version lineage](../paper2/VERSION_LINEAGE.md) and [current residual status](../paper2/RESIDUAL_STATUS.md).

## Pinned edition and source

- **Markdown SHA-256:** `2ce83a40d69a9ab4122749dd47cc07546ded2882ceaaaeea24552d0380b7fd13`.
- **PDF SHA-256:** `4326061573494c1049e360c3be963a03b9074b5e862c2b245ba1cfc882c350ec`.
- The guide source is *verbatim* from proofread v1.1.1. Its older theorem/historical event links retain their original immutable SHA references.
- The navigational repository inventory is pinned to commit [`c5a36cd6189e2a249d5f4bc11f31698917dc8b10`](https://github.com/HMarcusWH/PermanssonLean/commit/c5a36cd6189e2a249d5f4bc11f31698917dc8b10) and Git tree `e3211713f1ef508ea891f534509116accaad56a4`.
- The index has 2332 tracked files, 798 Lean files (64 core, 710 research), and 793 Python files.
- Research root imports 710/710 research modules directly. Core root imports 63/64 core modules directly; `PermanssonLean/Regime/SurvivalBridge.lean` is not directly listed.
- 409 distinct existing paths are mentioned explicitly in the guide; only 294 are Lean/Python modules. Paths with no direct mention are **still indexed**, with **suggested chapter-family navigation** explicitly marked as inferred.

## What the links do—and do not—prove

| Kind | Meaning |
|---|---|
| Exact chapter reference | The guide actually names this current-tree path or a uniquely resolvable filename in that chapter. |
| Module-family navigation | A reading suggestion derived from the source directory (not proof ownership or a theorem dependency). |
| Appendix J S-number | One of 166 exact source-catalog references; it resolves to a tracked file. |
| Case source route | A literal join from a frozen case to catalog S-numbers; it does not confer acceptance. |
| Direct root import | The root Lean file imports that module explicitly; compilation and proof scope are different questions. |

**Frozen independent decisions:** original 15 `PENDING`, original 30 `PARTIAL_SCOPE`, later 11 `SOURCE_PRESENT_REVIEW_PENDING`. The guide remains a qualified technical reference.

## Build and validation entrypoints

```bash
lake exe cache get
lake build
lake build PermanssonResearch
```

These build the default frozen core and separate research library; they do not reexecute external empirical identification. For application replay, use the [successor application's guide](../../apps/permansson/application-successor/README.md). For pinned checks, see [research build](../RESEARCH_BUILD.md) and [verification](../../verification/README.md).

## Updating this index

On a new guide edition or source commit, rebuild the indexes against that **new fixed commit**, preserve the prior edition and its hashes, compare all 166 source-catalog paths and 56 literal cases, and update the README links only after validation. Do not silently repoint historical theorem/source links. The machine-readable manifest records each path and its exact Git blob identity.
