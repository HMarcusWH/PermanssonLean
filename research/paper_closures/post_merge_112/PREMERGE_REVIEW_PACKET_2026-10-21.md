# PR #113 — pre-merge mathematical acceptance reviewer packet

**Status:** PRE-REVIEW CANDIDATE. No independent source or scholarly approval; no release authorization. This document is a source-indexed work queue, **not** an acceptance receipt.

## Verified observations at historical source head H

- GitHub PR: https://github.com/HMarcusWH/PermanssonLean/pull/113
- Exact compiled source `H`: `1ec91b78f423261a91670e5f66bbd5ccb78ed0eb` (before additive audit-document commits).
- Base `B`: `17c315f7df7abf457eb94d393bd526d46da6f6f4`. Synthetic `S`: `2034fa27329d8de445268a64639b88039a1ccbd6`. The observed synthetic commit has ordered parents `[B,H]` and an integrated tree matching H. **No merged main M exists.**
- At H, all 9 PR workflows passed, including Research Lean; its 1,211 regression tests passed, and source checks passed. The N2 false-unrestricted-optimum mutant was rejected as a mathematical error.
- `15` new final test modules with `47/47` named test functions observed reporting `... ok` in the exact Research Lean job log. These are test observations, not per-case scholarly approvals.
- All 11 closure source files were present and imported once by the Research root. Their actual GitHub blob IDs and local declaration names are indexed in [the claim-and-case JSON](PREMERGE_CLAIM_CASE_EVIDENCE_2026-10-21.json).
- Frozen original mathematical providers, pins and old release files were not edited by this PR, according to the protected-source CI and changed-file inspection.

## Original 45-case disposition

- **15 `PENDING`; 30 `PARTIAL_SCOPE`; 0 independently accepted in the current ledger.** No ledger decision is upgraded by this packet.
- Original 42-contract atlas stays intact. Every case retains its original expected result, recorded proof references and unresolved obligations in `acceptance_decisions.json`.
- All 45 rows currently have zero case-level positive, negative, CI and reviewer receipt entries in the new registry. A global 1,211-test pass does not automatically fill those slots.

### Fifteen specifically pending cases

| Case | Newly mapped closure IDs | Legacy substantive acceptance residual (re-evaluate against current proofs) |
|---|---|---|
| `X-01` | — | R2-A01: emitted-literal corruption is not stochasticity-preserving. |
| `X-04` | — | R2-A02: unique learner attainer removal is tested, not tied-equilibrium domain removal. |
| `M-02` | — | R2-A04: marked-versus-unmarked action-coupling distinction has no dedicated tracked countermodel. |
| `F-01` | `M1`, `M2`, `M3` | R2-A03: asymmetric common/private-update swap fixture missing. / R2-I02: general measurable n=2 product identity is distinct from the finite full model/path recovery. |
| `F-05` | — | R2-A05: positive exact SCM test is in the full suite, but not this 48-check route; dedicated positive Lean instantiation is absent. |
| `Q-02` | — | ANA-03: direct projected theorem uses matched starts/homogeneous kernels; expanded projected adapter remains open. |
| `Q-03` | — | ANA-01: routed executable tests the old additive primitive budget, not product saturation. |
| `Q-04` | — | ANA-02: selected localized visit/original-margin/reporting integration missing. |
| `Q-05` | `Q1`, `Q2`, `Q3`, `M1`, `M2`, `M3` | ANA-04: generic discounted/whole-law results are proved; a quotient-native original-margin application must still supply its actual bindings. |
| `D-05` | — | SR-A04: 9/100 versus1/100 boundary is scalar arithmetic rather than an instantiated committed-model path-law fixture. |
| `D-06` | — | SR-A05: hidden-flag fixture uses different pure priors, not two reachable histories from one fixed initial law. |
| `D-08` | `D8` | SR-A02: concrete typed compatible-overlap and joint-only certified block fixture missing. |
| `D-09` | `N1`, `N2`, `N3`, `D9` | SR-A01: concrete ExactClassFunctional and two-state5/6-versus1 regression missing. |
| `B-01` | — | SR-A02: generic compatible overlap proved; concrete typed positive/negative overlap fixtures missing. |
| `B-02` | — | SR-A03: non-global-isomorphism positive local-margin transport fixture missing. / R2-C01: preserved OR/AND labels are correct for ablation margins. |

Some historical residuals say a fixture was missing when the earlier audit was written. The new modules might address some of them. **Only a reviewer comparing exact theorem signatures, assumptions, source/test bytes and required negative conditions may update that determination.**

### Eleven new candidate-claim source owners

| ID | Research source module | Observed declarations | Acceptance |
|---|---|---:|---|
| `Q1` | `PermanssonResearch/Quotient/DiscountedCanonicalSourceWitness.lean` | 1 | Source compiled; declaration review pending |
| `Q2` | `PermanssonResearch/Quotient/DiscountedCanonicalMarginClosure.lean` | 2 | Source compiled; declaration review pending |
| `Q3` | `PermanssonResearch/Quotient/DiscountedCanonicalWitnessExamples.lean` | 6 | Source compiled; declaration review pending |
| `M1` | `PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedProtocols.lean` | 9 | Source compiled; declaration review pending |
| `M2` | `PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean` | 4 | Source compiled; declaration review pending |
| `M3` | `PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedExamples.lean` | 3 | Source compiled; declaration review pending |
| `N1` | `PermanssonResearch/ReverseSolver/NonlinearPeriodThreeStationary.lean` | 11 | Source compiled; declaration review pending |
| `N2` | `PermanssonResearch/ReverseSolver/NonlinearPeriodThreeExpectedScore.lean` | 4 | Source compiled; declaration review pending |
| `N3` | `PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean` | 4 | Source compiled; declaration review pending |
| `D8` | `PermanssonResearch/ReverseSolver/AdaptiveGrammarAdmissionFixture.lean` | 20 | Source compiled; declaration review pending |
| `D9` | `PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean` | 7 | Source compiled; declaration review pending |

## Targeted theorem-scope triage (review notes, not independent acceptance)

- **Q-05 / P-04:** `actual_canonical_discounted_original_margin` in `DiscountedCanonicalMarginClosure.lean` still requires a real `PointWitness` on **both** original baseline and intervention for **every** `y ∈ B₁.states`, exact comparison-image hypothesis `hB`, and uniform error envelopes. Green compilation establishes this conditional theorem, not unrestricted witness existence. Compare the concrete examples in Q3 against the original mandatory Q-05 test.
- **F-01 / P-05:** `matched_closed_loop_original_margin` and `matched_open_loop_original_margin` transport full original margins for an admitted matched conditional-product two-player family, assuming exact `Bbar₁.states` compression-image equality. Do not reinterpret this as arbitrary correlated multiagent recovery or drop the admitted mechanism/anchor conditions.
- **D-08:** the current `AdaptiveGrammarAdmissionFixture.lean` now contains a **nonvacuous** `restrictedCertifiedMenu` whose `admitted` field is defined using `restricted.allowed (componentNames b)` and has two selected components, physical source-row certificates and a proof rejecting the forbidden joint patch. The inherited ledger's 'fixture missing' note is historically scoped; an independent reviewer must retest the original acceptance requirement before changing the decision.
- **D-09:** the current `NonlinearMultichainAggregationFixture.lean` includes distinct physical class and shared-descriptor evidence, an actual two-absorbing original whole-path mixture and an unequal classwise-versus-barycenter nonlinear score. The inherited missing-fixture allegation may be outdated, but the full original acceptance requirement and negative tests still need source-bound review.
- **N2 / P-06 crosswalk completeness:** `NonlinearPeriodThreeExpectedScore.lean` contains a conditional restricted-gap theorem and an unconditional phase-aware numeric score. The unconditional deterministic phase-blind `5/6` bound, its attained example and strict dominance over the declared deterministic class are exported from the **additional** `NonlinearPhaseBlindClassGeometry.lean` module. These supporting declarations must be attached explicitly to the final N2 claim-level crosswalk; the primary 11-row module mapping alone is insufficient. Do **not** claim domination over randomized stationary or history-dependent controls.

All five triage observations are source-reading notes at original green H, **not** claim approvals, per-declaration axiom certificates, or independent reviewer submissions.
## Reproducible reviewer task sequence

1. **Produce current-source hashes and lexical theorem headers:** in a clean pinned checkout on a single reviewed H, run `python3 verification/research/final_closure_generate.py --output /tmp/permansson-claim-observation.json`. Treat its SHA-256 outputs only as source identities; they are not compiler receipts.
2. **Review theorem scopes and assumptions:** for each advertised theorem, save exact compiled `#check` and `#print axioms` output, verify its transitive axioms are within `propext`, `Classical.choice`, `Quot.sound`, inspect the original `B_1` and both sides of P-04 and P-05, and preserve the restricted deterministic policy class in P-06.
3. **Replay positive and adversarial negative tests:** preserve separate source-hashed Lean compiler logs with explicit proof/type rejection. Forbid parser errors, unknown identifiers, heartbeat/resource timeouts, and numerical substitutions. Include current D-08 grammar admission, D-09 distinct physical classes and nonlinear classwise evaluation.
4. **Reconcile every historical acceptance case:** attach its original expected wording, reviewed source declarations, positive and negative receipts, real run/job IDs and an individual independent decision. A `PARTIAL_SCOPE` case stays partial if an original scope or premise is not actually covered.
5. **Separate approvals:** an independent source reviewer must submit a genuine GitHub `APPROVED` review on the exact final head, while manuscript/academic review and PDF visual inspection require their own authentic evidence. No owner-authored comment is an independent review.
6. **Build and inspect the draft manuscript:** from the genuine repository checkout run `python3 release/mathematical-closure-1/build.py --mode draft --engine pdflatex --render --out /tmp/permansson-math-closure`; then `python3 release/mathematical-closure-1/verify_release.py --manifest /tmp/permansson-math-closure/manifest.lock.json`. Inspect all rendered pages and citations; keep the `DRAFT_NOT_ACCEPTED` label. This packet performed **source-level structural lint only**: 13 canonical source files, 10 `\input` references and bibliography entries were found, with no missing cross-reference files; no TeX compilation or PDF visual signoff is claimed.
7. **Make a distinct pre-merge review decision and post-merge final release decision:** the repository's `final_closure_authenticate.py` deliberately requires a real merged `M` for strict verification. Therefore its post-merge strict gate **cannot be a pre-merge prerequisite without circularity**. Do not weaken it. Obtain independent pre-merge review and a narrowly scoped merge authorization first; only after an authorized merge authenticate real `M`, rerun integrated-main CI and use the strict release gate. Full 45-case acceptance is a separate and stronger result than a scoped paper.

## Go/no-go

**NO GO for claiming 45-case completion, scoped scholarly acceptance, tagging, PDF publication or merging PR #113 as a completed mathematical-closure release.** The exact source branch now contains additional audit-only commits after H; rerun exact-head CI and issue fresh H/S observations before any merge decision.

Open requirements: per-theorem statement SHA-256/axiom/negative diagnostic receipts; individual 45-case review evidence; independent source and scholarly signoff; real rendered PDF inspection; approved manuscript claim crosswalk; eventual M and source-bound integrated CI. No empirical GR/PR identification or universal randomized-control dominance is inferred.

## Evidence pointers

- [45-case / 11-module source observations](PREMERGE_CLAIM_CASE_EVIDENCE_2026-10-21.json)
- [47 named final-test and Git blob observations](PREMERGE_EXECUTED_TEST_EVIDENCE_2026-10-21.json)
- [Original immutable requirements](acceptance_decisions.json)
- [11-claim crosswalk](theorem_crosswalk.json)
- [Observed successful Research Lean run](https://github.com/HMarcusWH/PermanssonLean/actions/runs/39652715436)
- [Current candidate release manifest](../../../release/mathematical-closure-1/manifest.json)

