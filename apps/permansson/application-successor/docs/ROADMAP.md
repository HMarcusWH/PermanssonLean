# Successor application — roadmap and execution status

Branch `feature/application-successor-full`; `main` is untouched. This page
records what has been built against the original plans, what was decided,
and what is deliberately out of scope for an implementation branch.

It is not an acceptance record. The distinct gates in
[`ACCEPTANCE_STATUS.md`](ACCEPTANCE_STATUS.md) stay authoritative, and nothing
here asserts independent certification, release or empirical identification.
**A completed engineering step is not application acceptance.**

## Evidence tiers kept separate

| Tier | Meaning | How it is produced here |
| --- | --- | --- |
| Numeric | exact rational computation plus an independent checker that does not import the producer | `permansson_app` CLIs; every receipt says `lean_status=NOT_EXECUTED` |
| Source binding | a Lean source candidate re-derived byte-for-byte from the original request and receipt bytes | `proof/*_emit.py` and `proof/control_source_check.py` |
| Instance replay | the pinned Lean v4.34.0 compiler elaborates the candidate; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`; semantic mutations fail inside the targeted theorem | `verification/research/test_application_*_live_lean.py`, `scripts/end_to_end.py --lean` |
| Exact-head CI | GitHub workflows on one commit; results never transfer to a later commit | pull request #115 |
| Independent acceptance, release, empirical identification | outside this branch | owner-authorized review only |

## Built so far

- **Numeric profiles.** 26 additive exact profiles are registered in
  `data/capabilities.json`, next to the two closed native providers (C10,
  C11).
- **Lean bridges.** 24 source-bound bridge modules sit under
  `PermanssonResearch/ApplicationBridge/`. Each has an emitter, a byte
  recheck family and a pinned-Lean live replay with semantic mutations; see
  [`CAPABILITY_SCOPES.md`](CAPABILITY_SCOPES.md). `permansson-app lean-emit`
  and `lean-recheck` reach every family through one command.
- **Inventory.** `IMPLEMENTATION_MANIFEST.json` (v2) separates fixed
  historical facts from a current inventory recomputed by
  `scripts/inventory.py`. Every untracked planned path carries a disposition.
- **Walkthrough.** `scripts/end_to_end.py` checks every packaged example end
  to end and fails closed on any unexpected checker or CLI status.

Local and CI evidence for each commit is recorded on the pull request, not
here, so this page cannot go stale against the head.

## Status against the original plans

### Build plan batches (v2 build plan, S00–S14)

| Batch | Title | Status on this branch |
| --- | --- | --- |
| S00 | Numeric integration prototype | implemented (native C10/C11, strict envelopes, independent checks) |
| S01 | Full contract, semantics, identity and legacy import | **partial**: legacy reader, semantic digests and per-profile strict schemas exist; the cross-profile versioned contract layer and a shared whole-run budget for additive routes do not |
| S02 | Evidence bridge, claims and genuine native replay | **partial**: evidence, claims and detached bundles exist; no authenticated proof-evidence consumer |
| S03, S03L | Finite strategic-world realization; exact LP substrate | implemented, with `FiniteWorldInput` and `LinearProgramReceipt` bridges |
| S04 | Exact finite analysis and frozen-menu control | implemented except FIX-01 (benchmarks/X1), which is deferred |
| S05–S10 | Exit/grammar/quantitative; feedback and residence; constrained, robust and adaptive control; belief and safety; metric, quotient and nonlinear; multi-agent | implemented for bounded finite scopes, each with a bridge |
| S11 | Expert nonfinite and specialized profiles | ADV-02 implemented (rational algebra); ADV-01 deferred |
| S12 | Domain imports and local federation | **envelope-only, read-only**; source-grade importers deferred |
| S13 | Application acceptance and current release documentation | documentation done; acceptance **not** done (owner-gated) |
| S14 | Optional dedicated CI profile transition | **not performed** (review-gated) |

### Deployment phases (implementation and deployment instructions, P0–P7)

| Phase | Status on this branch |
| --- | --- |
| P0 Source reconciliation | done (manifest v2 with dispositions) |
| P1 Numerical foundation | done |
| P2 Full contracts | **partial** (as S01) |
| P3 Evidence and proof integration | **partial**: source-bound candidates and live replays done; no authenticated evidence consumer, so outputs keep `NOT_EXECUTED` |
| P4 Finite model and LP correspondence | done for bounded instances |
| P5 Full mathematical engines | done for bounded finite scopes; FIX-01 and ADV-01 deferred |
| P6 Domain integration | **envelope-only** |
| P7 Packaging and release preparation | **partial**: wheel, installed-distribution test and locked backend exist; no selected release scope, platform matrix or authorization |

### Final engineering round (R0–R6)

These steps were a short sprint inside the phases above. They do not
complete P2, P3, P6 or P7.

| Step | Work item | Content | Status |
| --- | --- | --- | --- |
| R0 | REL-02 | this roadmap; first inventory reconciliation | done |
| R1 | APP-05 | one `lean-emit` / `lean-recheck` CLI over every emitter family | done |
| R2 | OPT-06 | private-control stage saddle profile and `PrivateStageReceipt` | done |
| R3 | OPT-09 | adaptive admitted-block control and `AdaptiveBlockReceipt` | done |
| R4 | OPT-05 | risk-cap Farkas infeasibility and `FlowInfeasibilityReceipt` | done |
| R5 | ANA-01 | CQ-1 certificate transport and `CQ1TransportReceipt` | done |
| R6 | REL-02 | documentation set, end-to-end walkthrough, staleness-audit repairs | done |

## Staleness audit (2026-10-31): resolution and recorded decisions

An external read-only audit of `a3df725` raised 33 work orders.

**Repaired on this branch:**

- **E2E-01–03.** The walkthrough now fails closed on checker and CLI status,
  uses the Research harness's axiom parser and process-group runner, and no
  longer inherits `PYTHONPATH` for installed runs.
- **INV-01–06.** The manifest is now v2, with the historical/current split,
  the spread-string repair, fixture rows, dispositions, a detached head
  receipt and invariant tests.
- **DOC-03–09.** The stale Lean statements in the numeric guides are
  corrected, and this crosswalk was added.
- **PKG-01–02.** The package metadata is corrected and the build backend
  pinned to the lock.
- **QA-01.** A stale-phrase and bridge-coverage regression was added.

**Decisions recorded here instead of code:**

| Order | Decision |
| --- | --- |
| CON-02 | A first release is **numeric-only**. Outputs keep `lean_status=NOT_EXECUTED` until a separate, independently reviewed proof-evidence consumer authenticates compiler runs for a selected subset. |
| CON-03 | `data/acceptance_policy.json` intentionally selects only C10/C11. The 26 additive profiles are not release capabilities until an owner authorizes a scope with an evidence matrix. |
| PKG-04 | Additive routes rely on per-profile structural bounds: dimensions, horizons and rational bit sizes. A cumulative whole-run budget like the native `RunBudget` is **required before any release that includes them** (manifest disposition `REQUIRED_BEFORE_RELEASE`). |
| CON-06 | FIX-01 (benchmarks/X1) and ADV-01 (nonfinite expert evidence) are deferred (`DEFERRED_SCOPE`); nothing nonfinite is computed or claimed. |
| CON-01, CON-04, CON-05 | The cross-profile contract layer, source-grade domain importers and real federation providers are deferred. Federation stays read-only with no remote execution. |
| CI-04 | Every output keeps `scientific_claims_verified=false`, `empirical_identification=NOT_IDENTIFIED` and nine unassessed certificate dimensions. |

**Not actionable on this branch (owner or independent review):**

- **CI-01.** Exact-head Research Lean completion, read per commit on the
  pull request.
- **CI-02.** The historical T/T2 archive-restoration security migration.
- **CI-03.** Independent source, security and mathematics review, and the
  owner's decision.
- **PKG-03.** An authenticated Linux/Windows × Python 3.12/3.13 distribution
  matrix.

## Out of scope for this branch

* Activating or relaxing any GitHub Actions workflow or guard; the inherited
  `archive-reproducibility` failure is reported, not relaxed.
* Running or claiming independent research CERT for the original 45 or the
  later 11 claims.
* Empirical identification, publication, merging to `main` or publishing a
  release without explicit owner authorization.
* Editing the protected theory core, the legacy `application/` root, the
  pinned toolchain or Lake configuration, or the existing C10/C11 providers.

## Inventory reconciliation

`IMPLEMENTATION_MANIFEST.json` gives every untracked planned path a
`disposition_current` with a reason (vocabulary in its `dispositions`
section):

- excluded generated build products;
- supersessions to implemented paths, with the targets checked;
- deferred alternate layouts naming related implemented files, without
  claiming full equivalence;
- deferred contract-layer, domain or scope items;
- items required before release;
- review-gated CI and release surfaces.

`python scripts/inventory.py --check` verifies these dispositions and that
the current counts match the tracked tree.
