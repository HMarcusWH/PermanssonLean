# Paper v2.0.1: residual obligations and evidence status

[Current documentation](README.md) · [Mathematical crosswalk](MATHEMATICAL_CROSSWALK.md) · [Earlier-paper concordance](EARLIER_PAPER_CONCORDANCE.md) · [Verification](VERIFICATION.md)

This is the current explanatory ledger for the obligations retained by **Section 31 and Appendix P of the reviewed manuscript v2.0.1**. It is bound to mathematical source `c5a36cd6189e2a249d5f4bc11f31698917dc8b10` and the documentation baseline `f0dee1c11a20f96c9a11b380e942b9252e6ebe44`. The [publication manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json) identifies the exact manuscript bytes.

The entries distinguish the scope stated in the paper from the separate evidence or stronger object still requiring reconciliation. They do not assert that a named source file is absent. Existing selected-scope reviews can report a theorem or local receipt present while the corresponding historical criterion, source-to-paper reconciliation or independent acceptance remains outstanding.

## Status dimensions

| Dimension | Question answered | Authority / evidence |
|---|---|---|
| Provider presence | Does the named theorem, model, table or adapter exist in the pinned source? | Exact source declaration and its hypotheses; source and declaration indexes. |
| Supplied mathematical scope | What does that provider prove, under which model, quantifiers and assumptions? | Literal theorem/interface and the manuscript argument using it. |
| Paper/source reconciliation | Does the paper statement match that exact source, or use a different proof/specialization? | A recorded comparison of assumptions, constructions and conclusions. |
| Fixture / control / receipt | Was the specific requested table, negative control or compiler instance actually checked? | Identified fixture and source-bound executed receipt; an unrelated positive test does not substitute. |
| Historical case disposition | What does the original case ledger currently say? | Preserved 45-case and later 11-claim records, routed through the reference guide. |
| Independent acceptance | Has the relevant criterion been independently accepted at its required source identity? | The case-specific review/acceptance record, distinct from compilation or documentation. |
| Empirical identification | Does observed evidence identify the actual structural/causal claim? | Observation model, provenance, modularity, support, identified set and simultaneous uncertainty. |

## Preserved acceptance records

The [56-case reference crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) retains **15 PENDING**, **30 PARTIAL_SCOPE** and **11 SOURCE_PRESENT_REVIEW_PENDING** cases. The original 45-case identifiers and later 11-claim identifiers remain different namespaces: `original_45/Q-01` and `later_11/Q1`, for example, are not aliases.

The [selected mathematical scope review](../../research/paper_closures/SELECTED_SCOPE_REVIEW.md) reports selected contracts and measured local evidence, including literal X1 tables, clocks and occupation adapters. It expressly separates these from the 45-case acceptance ledger and later authenticated integration/release decisions. This page preserves that separation and the more specific Appendix P reconciliation criteria. A documentation update changes none of those historical dispositions.

## Seven retained obligations

## X-01

**Historical record:** `original_45/X-01` · **Preserved disposition:** `PENDING`.\
**Paper routes:** [`sec:C23`](MATHEMATICAL_CROSSWALK.md#c23), [`app:L`](MATHEMATICAL_CROSSWALK.md#appendix-l), [`sub:P:01`](MATHEMATICAL_CROSSWALK.md#appendix-p).

**Supplied scope.** The paper uses actual typed X1 atom formulas, incentive verification, occupation results and protocol margins. The selected source review separately reports eight literal matrices and local checks.

**Retained requirement.** Bind each of the eight historically specified literal 18×18 matrices to the actual atoms at all 324 pairs in each matrix. A formula identity is not by itself a recorded comparison of each emitted table.

**Evidence needed for reconciliation.** Identify the exact eight tables and typed model, check every pair with a recorded literal-table comparison, bind the receipt to source and table bytes, then reconcile that evidence against the original criterion. Preserve the historical PENDING field until its own acceptance process changes it.

**Source route.** [`PermanssonResearch/X1/ExactMatrixTables.lean`](../../PermanssonResearch/X1/ExactMatrixTables.lean); [`PermanssonResearch/X1/InterventionNumericalBridge.lean`](../../PermanssonResearch/X1/InterventionNumericalBridge.lean); [`verification/research/test_paper_x1_matrix_lean.py`](../../verification/research/test_paper_x1_matrix_lean.py). The [case-source crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) supplies the fuller historical catalog route.

## F-02

**Historical record:** `original_45/F-02` · **Preserved disposition:** `PARTIAL_SCOPE`.\
**Paper routes:** [`sec:C24`](MATHEMATICAL_CROSSWALK.md#c24), [`app:L`](MATHEMATICAL_CROSSWALK.md#appendix-l), [`sub:P:05`](MATHEMATICAL_CROSSWALK.md#appendix-p).

**Supplied scope.** Finite and natural advancing-clock constructions supply actual row and path projection identities. The general measurable-coordinate natural-clock review is a particular stated scope, distinct from the earlier countable-coordinate profile.

**Retained requirement.** Preserve the clock in the augmented mechanism and assess the original stalled or treatment-driven clock adversary at its literal scope. An exogenous update n′=n+1 does not automatically prove the same assertion for n′=n+a or a stalled update n′=n.

**Evidence needed for reconciliation.** Name the augmented mechanism, original chronological law and actual clock update; demonstrate the requested adversarial case under those exact definitions, then reconcile the original criterion and its evidence.

**Source route.** [`PermanssonResearch/MultiAgent/MeasurableNatPrivateClock.lean`](../../PermanssonResearch/MultiAgent/MeasurableNatPrivateClock.lean); [`PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean`](../../PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean); [`PermanssonResearch/MultiAgent/MeasurableNatClockFixture.lean`](../../PermanssonResearch/MultiAgent/MeasurableNatClockFixture.lean); [`research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md`](../../research/paper_closures/MEASURABLE_NAT_CLOCK_SCOPE.md). The [case-source crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) supplies the fuller historical catalog route.

## A-01

**Historical record:** `original_45/A-01` · **Preserved disposition:** `PARTIAL_SCOPE`.\
**Paper routes:** [`sec:C14`](MATHEMATICAL_CROSSWALK.md#c14), [`app:H`](MATHEMATICAL_CROSSWALK.md#appendix-h), [`sub:P:01`](MATHEMATICAL_CROSSWALK.md#appendix-p).

**Supplied scope.** Finite KR primal/dual equality, finite attaining witnesses, first-moment identification and the stated abstract dual-bound interface are available at their respective scopes.

**Retained requirement.** A general named dual-attaining potential and complementary-equality witness in the selected abstract source interface is a separate source/review requirement. Finite-dimensional LP dual attainment is already proved at its finite scope.

**Evidence needed for reconciliation.** Supply or identify the precise potential and complementary equality in the requested abstract interface, check admissibility and all integrability/metric hypotheses, and record the comparison to the historical acceptance criterion.

**Source route.** [`PermanssonResearch/Probability/FirstMomentKantorovichDuality.lean`](../../PermanssonResearch/Probability/FirstMomentKantorovichDuality.lean). The [case-source crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) supplies the fuller historical catalog route.

## A-04

**Historical record:** `original_45/A-04` · **Preserved disposition:** `PARTIAL_SCOPE`.\
**Paper routes:** [`sec:C15`](MATHEMATICAL_CROSSWALK.md#c15), [`app:H`](MATHEMATICAL_CROSSWALK.md#appendix-h), [`sub:P:03`](MATHEMATICAL_CROSSWALK.md#appendix-p).

**Supplied scope.** The paper has actual four-process occupation interfaces and the elementary demonstration that three output values do not determine the fourth.

**Retained requirement.** A concrete canonical four-process model must satisfy exactly three requested factorizations and fail exactly the fourth while retaining the other structural hypotheses. A scalar counterexample or rejection of a missing argument is a different object.

**Evidence needed for reconciliation.** Identify all four processes and the same global property, verify the three required factorizations and all shared premises, and exhibit the failed fourth factorization in the canonical model with its own evidence.

**Source route.** [`PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean`](../../PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean); [`PermanssonResearch/Perturbation/FiniteOccupationProperty.lean`](../../PermanssonResearch/Perturbation/FiniteOccupationProperty.lean). The [case-source crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) supplies the fuller historical catalog route.

## E-05

**Historical record:** `original_45/E-05` · **Preserved disposition:** `PARTIAL_SCOPE`.\
**Paper routes:** [`sec:C26`](MATHEMATICAL_CROSSWALK.md#c26), [`app:M`](MATHEMATICAL_CROSSWALK.md#appendix-m), [`sub:P:04`](MATHEMATICAL_CROSSWALK.md#appendix-p).

**Supplied scope.** Strict Gram-gap negativity, an exact witness, additional-component threshold, amplification and masking are present under their stated algebraic assumptions.

**Retained requirement.** The separately executed zero-gap negative control and source-specific analytic or empirical interpretation retain their own evidence status. At zero gap the strict negative conclusion becomes zero; masking algebra does not establish the natural source identification.

**Evidence needed for reconciliation.** Record the dedicated zero-gap fixture and observed result separately from the strict positive fixture. Any analytic or empirical source interpretation must supply its actual identification and approximation assumptions, beyond the finite algebra.

**Additional finite evidence, 21 November 2026.** The [new reproduction addendum](../../paper2/reproduction/v2.0.1/README.md#fixture-provenance-and-limits) supplies newly chosen, source-consistent rational fixtures. Its [specialized program](../../paper2/reproduction/v2.0.1/specialized_replay.py) and [retained observed results](../../paper2/reproduction/v2.0.1/REPLAY_RESULTS.json) record two separate passing controls: `parallel_gram_vectors_remove_strict_gap` checks that `x = (1,2)` and `y = 2x` have zero Gram gap; `positive_background_changes_witness_sign` uses the separate nonparallel fixture `x = (1,2)`, `y = (3,-1)`, `c = 2` and checks that its witness's negative signed quadratic form becomes positive after adding the declared positive-semidefinite background `P = 2c yyᵀ`, while keeping that witness fixed. These are additional finite controls, outside the original 63 retained outputs. They do not recover the original review inputs or execution, reconcile every part of the historical E-05 criterion, or establish its source-specific analytic or empirical interpretation. The preserved `PARTIAL_SCOPE` disposition and independent acceptance requirement remain unchanged.

**Source route.** [`paper/supporting/specialized_theory/README.md`](../../paper/supporting/specialized_theory/README.md). The [case-source crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) supplies the fuller historical catalog route.

## Later Q1

**Historical record:** `later_11/Q1` · **Preserved disposition:** `SOURCE_PRESENT_REVIEW_PENDING`.\
**Paper routes:** [`sec:C13`](MATHEMATICAL_CROSSWALK.md#c13), [`sec:C16`](MATHEMATICAL_CROSSWALK.md#c16), [`sub:P:02`](MATHEMATICAL_CROSSWALK.md#appendix-p).

**Supplied scope.** Generic finite common-submeasure transport and the canonical discounted wrapper are stated with their actual premises, including the mass-one initial witness premise where used.

**Retained requirement.** A canonical discounted-output adapter must admit a genuinely subprobability initial-mismatch witness, include time-zero discrepancy and all domination conditions, and bind the complete original comparison domain for an original-margin extension.

**Evidence needed for reconciliation.** Identify the canonical path laws, projection/observation maps and score normalization, supply the initial common subprobability with its mass bound, and prove the requested discounted and original-domain statements without dropping time zero.

**Source route.** [`PermanssonResearch/Probability/DiscountedInitialBudget.lean`](../../PermanssonResearch/Probability/DiscountedInitialBudget.lean); [`PermanssonResearch/Probability/DependentHistoryCommonMass.lean`](../../PermanssonResearch/Probability/DependentHistoryCommonMass.lean). The [case-source crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) supplies the fuller historical catalog route.

## M-02

**Historical record:** `original_45/M-02` · **Preserved disposition:** `PENDING`.\
**Paper routes:** [`sec:C24`](MATHEMATICAL_CROSSWALK.md#c24), [`app:L`](MATHEMATICAL_CROSSWALK.md#appendix-l), [`sub:P:01`](MATHEMATICAL_CROSSWALK.md#appendix-p).

**Supplied scope.** Two separately strict anchors share unmarked marginals and differ in actual marked laws. A distinct reactive witness violates strictness.

**Retained requirement.** A stronger single reactive-opponent full marked-history pushforward identity cannot be obtained by joining conclusions from two different constructions.

**Evidence needed for reconciliation.** State one model and its opponent/information profile; prove the actual full marked-history law identity for that model, keeping strictness, reactivity and the comparison domain consistent throughout.

**Source route.** [`research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md`](../../research/paper_closures/post_merge_79/NEXT03_M02_MARKED_COUPLING.md). The [case-source crosswalk](../reference/CASE_SOURCE_CROSSWALK.md) supplies the fuller historical catalog route.

## Broader extensions and review limits

### Continuous-time process and intervention bridge

Appendix P requires a well-posed process or controlled solution family; typed intervention composition; measurable path space and stopping times; a region condition controlling behavior between observations; occupation convergence in the stated mode; and a property or quotient theorem respecting those paths. A discrete skeleton theorem can contribute to this programme, but an additional retention bridge is required. Viability under some selection, invariance under every selection and controlled safety remain different predicates. See [`sub:P:06`](MATHEMATICAL_CROSSWALK.md#appendix-p).

### Partial observation and conditional beliefs

The hidden state, observation kernel and filtration must be stated, along with regular conditional beliefs, measurable belief updates and the admissible policy class. Continuous, sampled and event-driven observations lead to different problems. Full-information occupation convergence alone does not establish control sufficiency under a coarser filtration. See [`sub:P:05`](MATHEMATICAL_CROSSWALK.md#appendix-p).

### Empirical identification and uncertainty

An empirical regime claim needs a frozen observation model preserving source timing and missingness, a defensible strategic/world factorization, intervention modularity and support, a provenance-valid identified set and simultaneous uncertainty for the actual selected claim. The property remains global on the relevant baseline and intervention paths. A zero witness, failed invariance condition, unidentifiable direction or uncertainty set containing zero is a substantive negative outcome. See [`sub:P:07`](MATHEMATICAL_CROSSWALK.md#appendix-p) and [application compatibility](APPLICATION_COMPATIBILITY.md).

### Exhaustive historical and declaration reconciliation

The [earlier-paper concordance](EARLIER_PAPER_CONCORDANCE.md) retains five current-family entries with historical deltas pending, one source-wording clarification and three incomplete required historical reconciliations. All 798 Lean files have written-group routes, while individual equivalence of all 7,690 lexical declaration/example units remains unclaimed. These are different completeness questions from whether the source compiles or the manuscript has a valid label index.

## Updating this ledger

For any changed row, retain the previous source-relative statement and add the exact new theorem/model/table/receipt, its source identity, assumptions, comparison domain and reviewer decision. Change only the dimension supported by that evidence. A new compiler receipt may update execution evidence while leaving independent acceptance or empirical identification unchanged. An editorial correction may resolve wording without adding a new formal theorem. Original case ledgers and preserved evidence records retain their own authority.
