# Paper v2.0.1: earlier-paper concordance

[Current documentation](README.md) · [Mathematical crosswalk](MATHEMATICAL_CROSSWALK.md) · [Version lineage](VERSION_LINEAGE.md) · [Residual status](RESIDUAL_STATUS.md)

This page renders the reviewed [earlier-paper written-obligations index](../../paper2/v2.0.1/indices/earlier_paper_written_obligations.json): **51 source-family obligations**, containing **201 required-content entries**, mapped to **235 actual manuscript labels across 37 manuscript source files**. It carries forward the source editions, requirement wording, written treatment, remaining gaps and explicit review limits of that index.

The mathematical source is `c5a36cd6189e2a249d5f4bc11f31698917dc8b10`; the manuscript is reviewed draft v2.0.1. An entry's source family and source section identify the earlier obligation. A linked current label is a reading destination in the reviewed manuscript, not a claim that every original hypothesis or unique historical clause has been independently reconciled. Full source content IDs and original completion-gate fields remain in the exact JSON record.

## What is complete and what remains open

All 51 obligations and all 201 content entries have actual destinations. The preserved content dispositions are:

| Rendered status | Exact JSON status | Entries | Meaning |
|---|---|---|---|
| WRITTEN | `substantive_written_treatment` | 192 | Substantive treatment is written at the supplied destinations. |
| HISTORICAL_DELTA_PENDING | `written_current_family_historical_delta_pending` | 5 | The current family is treated; the edition-specific comparison remains open. |
| SOURCE_WORDING_CLARIFIED | `written_with_source_wording_clarification` | 1 | The source wording and actual mathematical object are explicitly distinguished. |
| RECONCILIATION_INCOMPLETE | `required_historical_reconciliation_not_complete` | 3 | A required historical comparison has not been completed. |

The obligation-level distribution is 45 substantive family treatments, four families with historical-delta review pending, one family with a source-wording clarification and one partially reconciled family. A family-level status and the statuses of its individual content entries have different denominators.

In particular, **PRIOR-012 through PRIOR-015** retain edition-specific comparison work for v0.1.0, v0.1.3, v0.1.6 and v0.1.7. **PRIOR-050** retains the unique-clause and section-delta review across mathematical-guide editions. The GSCRD entry **PRIOR-040** corrects the inventory's “missingness-aware distance” wording to the located completion-interval geometry without inventing an unlocated distance theorem. The stronger source/interface obligations carried by PRIOR-030, PRIOR-031, PRIOR-032, PRIOR-034 and PRIOR-039 are described in [residual status](RESIDUAL_STATUS.md).

## Source families

| Source family / edition | Obligations | Required-content entries |
|---|---|---|
| EGR_core_v1.2.2 | [PRIOR-001](#prior-001); [PRIOR-002](#prior-002); [PRIOR-003](#prior-003); [PRIOR-004](#prior-004); [PRIOR-005](#prior-005); [PRIOR-006](#prior-006); [PRIOR-007](#prior-007); [PRIOR-008](#prior-008); [PRIOR-009](#prior-009) | 37 |
| EGR_supplement | [PRIOR-010](#prior-010) | 4 |
| EGR_strategic_brief | [PRIOR-011](#prior-011) | 2 |
| original_paper_v0.1.0 | [PRIOR-012](#prior-012) | 2 |
| original_paper_v0.1.3 | [PRIOR-013](#prior-013) | 2 |
| original_paper_v0.1.6 | [PRIOR-014](#prior-014) | 2 |
| original_paper_v0.1.7 | [PRIOR-015](#prior-015) | 2 |
| original_paper_v0.1.8 | [PRIOR-016](#prior-016); [PRIOR-017](#prior-017); [PRIOR-018](#prior-018); [PRIOR-019](#prior-019); [PRIOR-020](#prior-020); [PRIOR-021](#prior-021); [PRIOR-022](#prior-022); [PRIOR-023](#prior-023); [PRIOR-024](#prior-024); [PRIOR-025](#prior-025); [PRIOR-026](#prior-026); [PRIOR-027](#prior-027); [PRIOR-028](#prior-028); [PRIOR-029](#prior-029) | 47 |
| accepted_research_companion_v0.2.0 | [PRIOR-030](#prior-030) | 4 |
| mathematical_closure_13_file_draft | [PRIOR-031](#prior-031); [PRIOR-032](#prior-032); [PRIOR-033](#prior-033); [PRIOR-034](#prior-034) | 18 |
| specialized_Weil_CCM | [PRIOR-035](#prior-035); [PRIOR-036](#prior-036); [PRIOR-037](#prior-037); [PRIOR-038](#prior-038); [PRIOR-039](#prior-039) | 28 |
| GSCRD_master_history | [PRIOR-040](#prior-040) | 8 |
| Brown_MacKay_finite_grid | [PRIOR-041](#prior-041) | 4 |
| MIDR_lineage | [PRIOR-042](#prior-042) | 5 |
| Russia_Ukraine_lineage | [PRIOR-043](#prior-043) | 5 |
| Hormuz_empirical_lineage | [PRIOR-044](#prior-044) | 5 |
| Iran_January_counterfactual | [PRIOR-045](#prior-045) | 3 |
| Breaking_Persistence_lineage | [PRIOR-046](#prior-046) | 8 |
| cross_conflict_geometry | [PRIOR-047](#prior-047) | 4 |
| geometry_research_programme | [PRIOR-048](#prior-048) | 4 |
| historical_domain_framing | [PRIOR-049](#prior-049) | 2 |
| mathematical_reference_guide_editions | [PRIOR-050](#prior-050) | 3 |
| application_upgrade_and_build | [PRIOR-051](#prior-051) | 2 |

The [original v0.1.8 paper](../../paper/README.md), [foundational EGR source](../../paper/supporting/foundational/README.md), [specialized source papers](../../paper/supporting/specialized_theory/README.md), [accepted v0.2.0 companion](../../release/v0.2.0/README.md), [closure-candidate manuscript](../../research_papers/mathematical_closure/README.md) and [v1.1.1 reference guide](../reference/README.md) retain separate identities. Historical application/workpack lineage is documented by the exact source-content inventory in the [source ZIP](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip) at `coverage/inventory/earlier_paper_coverage.json` and `earlier_source_occurrences.json`.

## Requirement-by-requirement concordance

Each numbered requirement below is retained from the reviewed index. Its text describes the source obligation; the treatment describes what the current manuscript actually writes. Exact manuscript labels route to their containing section or appendix in the mathematical crosswalk. Source ZIP paths remain archive member names.

## PRIOR-001

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §§1–2; §12–13; Appendices A–B\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The exact EGR source remains independently substantive; the later embedding theorem does not reproduce its benchmark models or all diagnostics.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-001.1 | Post-equilibrium question and exact contribution boundary — States the post-equilibrium question and distinguishes the selected behavioral solution from persistence, occupation and constitutive classification of the world it generates. The predecessor remains a substantive model paper. | WRITTEN | [`sub:C01:01`](MATHEMATICAL_CROSSWALK.md#c01); [`sub:C01:02`](MATHEMATICAL_CROSSWALK.md#c01); [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-001.2 | Distinguish generator certificate from induced regime classification — Defines the selected-game certificate and proves its typed-process embedding while retaining the independent regime gates and conservative recovery restriction. | WRITTEN | [`sub:C01:02`](MATHEMATICAL_CROSSWALK.md#c01); [`eq:C06-value`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-001.3 | Retain related-work comparisons, generalization limits, notation and formal-claim boundary — Provides related-work comparisons, common notation, model relativity and explicit scope limits for standard probability, games, identification and specialized algebra. | WRITTEN | [`sub:C01:04`](MATHEMATICAL_CROSSWALK.md#c01); [`sub:C01:05`](MATHEMATICAL_CROSSWALK.md#c01); [`sub:C31:01`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:C31:05`](MATHEMATICAL_CROSSWALK.md#c31) |

## PRIOR-002

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §3; Assumption3.1\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Do not transfer an equilibrium certificate to an arbitrary adaptive or nonequilibrium generator.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-002.1 | Finite-player primitive game and equilibrium certificate — Gives finite-player stochastic-game primitives, feasible actions, bounded discounted utilities and the selected pure stationary Markov-perfect certificate; derives its one-shot continuation inequalities. | WRITTEN | [`eq:C06-value`](MATHEMATICAL_CROSSWALK.md#c06); [`prop:C06-one-shot`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-002.2 | Local continuation-action problem and modular state architecture — Separates the local continuation-action comparison from modular world, action-record and strategic-update construction. | WRITTEN | [`eq:C06-value`](MATHEMATICAL_CROSSWALK.md#c06); [`prop:C06-one-shot`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-record`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-002.3 | Measurability, feasibility, payoff/discount and equilibrium-selection assumptions — States measurable state/action data, feasibility support, bounded payoff and discount conditions, and the status of equilibrium selection as an input rather than a consequence of arbitrary adaptation. | WRITTEN | [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C03-composition`](MATHEMATICAL_CROSSWALK.md#c03); [`prop:C06-one-shot`](MATHEMATICAL_CROSSWALK.md#c06) |

## PRIOR-003

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §4; Assumption4.1; Definitions4.2–4.3\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Exact invariance, finite-horizon persistence and occupation convergence require separate stated premises.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-003.1 | Ex ante region/basin/descriptor and analytical persistence status — Freezes the region, basin, global descriptor and convergence convention and distinguishes all-state invariance from finite persistence. | WRITTEN | [`eq:C04-spec`](MATHEMATICAL_CROSSWALK.md#c04); [`def:C04-GR`](MATHEMATICAL_CROSSWALK.md#c04); [`eq:C04-inv`](MATHEMATICAL_CROSSWALK.md#c04) |
| PRIOR-003.2 | Limiting occupation law and declared convergence mode — Defines empirical descriptor occupation and its stated convergence mode for every admitted initial law; explains when a world-level descriptor descends from the game. | WRITTEN | [`eq:C02-empirical`](MATHEMATICAL_CROSSWALK.md#c02); [`eq:C04-occ`](MATHEMATICAL_CROSSWALK.md#c04); [`def:C04-GR`](MATHEMATICAL_CROSSWALK.md#c04); [`eq:C06-lumping`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-003.3 | Multi-axis regime profile, separating persistence, geometry, scale, feedback and constitution — Retains the multi-axis profile of generator, locus, asymptotic form, persistence, constitution and feedback, with scale growth distinguished from normalized composition. | WRITTEN | [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`tab:profile-axes`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`eq:C06-growth`](MATHEMATICAL_CROSSWALK.md#c06) |

## PRIOR-004

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §5; Definitions5.1–5.6\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Positive state cross-generation is not a proof of incentive reinforcement; the latter needs its own normalized deviation-margin analysis.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-004.1 | Policy versus structural/institutional interventions — Separates policy replacement from changes to physical or institutional primitives and identifies which typed mechanisms remain fixed. | WRITTEN | [`def:C06-policy-PR`](MATHEMATICAL_CROSSWALK.md#c06); [`sec:C05`](MATHEMATICAL_CROSSWALK.md#c05) |
| PRIOR-004.2 | Constitutive policy versus constitutive physical/institutional primitive — States policy constitution relative to a declared property and comparison domain; structural constitution changes a different primitive and has a different interpretation. | WRITTEN | [`def:C06-policy-PR`](MATHEMATICAL_CROSSWALK.md#c06); [`def:C05-PR`](MATHEMATICAL_CROSSWALK.md#c05) |
| PRIOR-004.3 | Policy-locked PR, strategic modes and normalized deviation resistance — Defines policy-locked strategic modes and normalized deviation resistance and derives the no-drift/incentive identity used by the diagnostic. | WRITTEN | [`def:C06-policy-PR`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-resistance`](MATHEMATICAL_CROSSWALK.md#c06); [`prop:C06-resistance`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-004.4 | Opponent-mediated state and incentive cross-effects under declared reference actions — Defines material state and incentive cross-effects under frozen reference actions; material cross-generation alone does not certify a positive change in the incentive margin. | WRITTEN | [`eq:C06-cross`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-resistance`](MATHEMATICAL_CROSSWALK.md#c06) |

## PRIOR-005

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §6–7; Definitions6.1–6.2\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Co-stabilisation needs restorative structure and an appropriate stability argument; positive feedback signs alone do not establish it.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-005.1 | Signed feedback graph with declared derivative/intervention semantics — Gives derivative or finite-difference intervention semantics for signed feedback and retains the typed strategic-to-world and world-to-strategic dependencies. | WRITTEN | [`eq:C06-cross`](MATHEMATICAL_CROSSWALK.md#c06); [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b) |
| PRIOR-005.2 | Model-relative self-limitation and asymmetry of restorative channels — Explains model-relative self-limitation and potentially asymmetric restorative channels in the declared state and incentive variables. | WRITTEN | [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-growth`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-005.3 | Antagonistic co-constitution versus co-stabilisation — Distinguishes antagonistic co-constitution from co-stabilization; the latter needs a restorative mechanism and a stability argument beyond a positive feedback sign. | WRITTEN | [`eq:C06-cross`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-Perron`](MATHEMATICAL_CROSSWALK.md#c06); [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b) |
| PRIOR-005.4 | Scale law and compositional descriptor must remain distinct — Separates the Perron growth factor of magnitude from convergence of normalized capability composition. | WRITTEN | [`eq:C06-growth`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-perron`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-Perron`](MATHEMATICAL_CROSSWALK.md#c06) |

## PRIOR-006

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §8; Assumption8.1; Theorems8.2–8.4; Proposition8.5\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Retain bounded nondecreasing state utility, strictly increasing activation functions, benefit>cost>0, dissipation in(0,1), positive coupling and the exact branch transition rule. The positive-matrix ingredients are not claimed as new general mathematics.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-006.1 | Full canonical two-player mutual-engagement primitives and threshold policy — Writes the complete two-player threshold engagement construction, four action-branch matrices, bounded nondecreasing state utility, activation and benefit-cost assumptions. | WRITTEN | [`eq:C06-matrices`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-payoff`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-threshold`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-006.2 | Threshold cone invariance iff two closure inequalities — Derives both necessary and sufficient closure inequalities for the threshold cone by evaluating the least admissible coordinate pair and monotonicity. | WRITTEN | [`eq:C06-closure`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-engagement`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-006.3 | Pure stationary MPE certificate is logically separate from closure — Proves the pure stationary MPE from the continuation inequalities independently of whether the chosen threshold cone is closed. | WRITTEN | [`prop:C06-one-shot`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-engagement`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-006.4 | Perron eigenvalue and binding/strict closure classification — Computes the positive-matrix Perron eigenvalue and classifies binding versus strict closure, retaining the standard nature of the positive-matrix tools. | WRITTEN | [`thm:C06-Perron`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-perron`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-006.5 | Positive-initial composition convergence and growth/neutral/contracting scale cases — Proves convergence of normalized positive-initial composition to the Perron vector and distinguishes growing, neutral and contracting scale. | WRITTEN | [`thm:C06-Perron`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-growth`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-006.6 | Uniform constitutive growth-sign change under fixed-primitive permanent withdrawal — Shows a fixed-primitive permanent withdrawal changes the declared growth-sign property uniformly over the stated comparison domain. | WRITTEN | [`prop:C06-constitutive-growth`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-matrices`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-006.7 | Exact cross-generation formulas and constant-cohesion special case — Retains exact cross-generation expressions and the unit/constant-cohesion specialization, without identifying incentive effects from these material formulas alone. | WRITTEN | [`eq:C06-cross`](MATHEMATICAL_CROSSWALK.md#c06); [`prop:C06-constitutive-growth`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-nonlinear`](MATHEMATICAL_CROSSWALK.md#c06) |

## PRIOR-007

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §9; Propositions9.1–9.2\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** State-space preservation and exact nesting do not establish nonlinear equilibrium, bifurcation, stability or an EGR. Those remain separate mathematical questions.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-007.1 | Nonlinear capability/cohesion recurrence and all parameter bounds — States the nonlinear capability/cohesion recurrence and bounds on dissipation, coupling, activation, clipping and cohesion parameters. | WRITTEN | [`eq:C06-nonlinear`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-007.2 | Borel self-map/state-space preservation proof — Proves that the nonlinear update is a Borel self-map of the declared state space using continuity/measurability and the coordinate bounds. | WRITTEN | [`prop:C06-nonlinear`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-007.3 | Exact nesting of the linear model at unit cohesion — Substitutes unit cohesion to recover the exact linear branch matrices rather than an approximate resemblance. | WRITTEN | [`prop:C06-nonlinear`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-matrices`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-007.4 | Separate optional monotonicity assumptions from assumptions actually used by the proposition — Separates optional monotonicity hypotheses from the bounds needed for self-mapping and nesting; neither result is presented as nonlinear equilibrium or stability. | WRITTEN | [`prop:C06-nonlinear`](MATHEMATICAL_CROSSWALK.md#c06); [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06) |

## PRIOR-008

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §10; Definition10.1; Corollary10.2\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The recognition architecture is not an identified latent model; the two-action timing benchmark is not a completed dynamic EGR. Preserve these boundaries while including the full mathematics.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-008.1 | Separate belief, latent recognition, public act and operative classification — Distinguishes private belief, latent recognition, a public act and operative classification as different mathematical or measurement objects. | WRITTEN | [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-record`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-008.2 | Admission mechanism and recognition field with distinct measurement semantics — Defines the admission/update architecture and recognition field and preserves the fact that this does not itself identify a latent empirical process. | WRITTEN | [`eq:C06-record`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-008.3 | Causal-origin capture as an intervention-relative definition — Retains causal-origin capture as relative to a specified admission mechanism and intervention, not as recovery of historical causality from an observed label. | WRITTEN | [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-record`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-008.4 | Full claim-or-wait payoff matrix and best-response correspondence — Gives the full two-by-two claim-or-wait payoff matrix, expected gain from claiming and set-valued best-response correspondence. | WRITTEN | [`eq:C06-claim-matrix`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-claim-increments`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-claim-response`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-008.5 | Interior, boundary and degenerate Nash cases, with supplement proofs — Solves the complete pure and mixed Nash correspondence, including strict interior mixing, equality boundaries, flat responses and degenerate parameter cases, with proofs. | WRITTEN | [`thm:C06-claim-equilibrium`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-008.6 | Order premium and conditional branch pre-emption — Defines and derives the order premium and conditional branch-preemption comparison while keeping this timing game separate from a completed dynamic EGR. | WRITTEN | [`eq:C06-order-premium`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-claim-equilibrium`](MATHEMATICAL_CROSSWALK.md#c06) |

## PRIOR-009

**Source:** `EGR_core_v1.2.2`\
**Source sections:** §11\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** No welfare or moral conclusion follows solely from equilibrium or regime structure.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-009.1 | Decision-maker utility versus stakeholder welfare — Separates player utility, material capacity, diagnostic quantities and stakeholder welfare; a social conclusion requires a separately specified welfare map. | WRITTEN | [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06); [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C31:07`](MATHEMATICAL_CROSSWALK.md#c31) |
| PRIOR-009.2 | Empirical identification sequence — Writes the ordered measurement/specification/model-identification/uncertainty workflow and the full model-set quantifiers rather than inferring empirical constitution from a simulation. | WRITTEN | [`def:confirmatory-pipeline`](MATHEMATICAL_CROSSWALK.md#c28); [`def:identified-constitution`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:07`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-009.3 | All diagnostic exclusion criteria and falsification conditions — States falsifiers for incentives, invariance, occupation, grounding, modularity, support, information cutoff and held-out performance, and preserves uncertified application status. | WRITTEN | [`sub:N:08`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`sub:C31:01`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:C31:07`](MATHEMATICAL_CROSSWALK.md#c31) |

## PRIOR-010

**Source:** `EGR_supplement`\
**Source sections:** Technical Proof Supplement; Formal Proof Audit and Claim Ledger; Academic Circulation Note; Overleaf source\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Supplemental numerical checks and symbolic audits must be distinguished from analytic proofs and Lean formalization.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-010.1 | Every proof and ancillary lemma supporting the EGR numbered claims — Provides analytic arguments for the predecessor numbered results and supporting lemmas, including equilibrium verification, closure, positive-matrix algebra, state preservation and embedding. | WRITTEN | [`prop:C06-one-shot`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-engagement`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-Perron`](MATHEMATICAL_CROSSWALK.md#c06); [`prop:C06-nonlinear`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-010.2 | Complete claim-or-wait Nash correspondence, including degeneracies — Includes the complete best-response and Nash correspondence, with endpoint and degenerate cases rather than only the interior mixed solution. | WRITTEN | [`eq:C06-claim-response`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-claim-equilibrium`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-010.3 | Occupation-law and positive-matrix proofs, not only the main-paper sketches — Supplies the positive-matrix/normalized occupation derivation and the initial-law transfer needed by the original regime definition. | WRITTEN | [`thm:C06-Perron`](MATHEMATICAL_CROSSWALK.md#c06); [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`lem:A-initial-mixture`](MATHEMATICAL_CROSSWALK.md#appendix-a) |
| PRIOR-010.4 | Preserve formal claim ledger and validation/nonimplication examples as separate evidence — Preserves analytic proof, historical symbolic/numerical validation, Lean execution and claim/acceptance evidence as different coordinates. The old ledger is not silently promoted into a new compilation receipt. | WRITTEN | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`def:evidence-coordinates`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C29:05`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C30:04`](MATHEMATICAL_CROSSWALK.md#c30) |

**Retained review limits.** All principal analytic claim families are written, but the historical supplementary claim-ledger rows have not received a fresh independent one-to-one semantic audit.

## PRIOR-011

**Source:** `EGR_strategic_brief`\
**Source sections:** Complete brief\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** A summary is not an independent theorem source; unique qualifiers must still be checked rather than discarded as a duplicate.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-011.1 | Preserve the brief’s conceptual framing and any unique qualification — Retains the strategic brief’s framing of generated persistence, equilibrium as a behavioral certificate and constitutive comparisons in the full predecessor exposition. | WRITTEN | [`sub:C01:01`](MATHEMATICAL_CROSSWALK.md#c01); [`sub:C01:02`](MATHEMATICAL_CROSSWALK.md#c01); [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-011.2 | Map compressed claims back to full EGR source — Maps compressed brief claims to the explicit EGR models and theorem arguments and treats the brief as a summary rather than an independent theorem source. | WRITTEN | [`sub:C01:02`](MATHEMATICAL_CROSSWALK.md#c01); [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06) |

**Retained review limits.** Unique brief qualifications are treated through the full predecessor exposition; a new sentence-by-sentence brief-versus-core diff was not performed for this mapping.

## PRIOR-012

**Source:** `original_paper_v0.1.0`\
**Source sections:** Entire archived edition, all sections and named claims\
**Obligation disposition:** Written family; historical delta review pending.

**Original scope boundary.** Newly located in MIDR source archive. Later versions supersede editorial authority, but every changed assertion requires a correction or preservation record.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-012.1 | Working-paper starting definition set and early EGR embedding/conservative-recovery formulations — Retains the early definition/embedding/recovery family through the present exact formulations and identifies the recovered v0.1.0 source. Every changed clause of that edition has not been independently reconciled. | HISTORICAL_DELTA_PENDING | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`def:C04-GR`](MATHEMATICAL_CROSSWALK.md#c04); [`def:C05-PR`](MATHEMATICAL_CROSSWALK.md#c05); [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-012.2 | Historical representation/constitution examples and stated limitations — Contains the representation/constitution counterexample family and explicit limitations; the source occurrence and named-statement lineage are retained, but this map is not an exhaustive v0.1.0 text diff. | HISTORICAL_DELTA_PENDING | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`thm:C05-representation`](MATHEMATICAL_CROSSWALK.md#c05); [`subsec:C05-witness`](MATHEMATICAL_CROSSWALK.md#c05); [`ex:bernoulli-factorization`](MATHEMATICAL_CROSSWALK.md#c27); [`sub:C31:01`](MATHEMATICAL_CROSSWALK.md#c31) |

**Retained review limits.** Every altered v0.1.0 clause still needs an exact preservation/correction record; current family destinations do not establish exhaustive containment.

## PRIOR-013

**Source:** `original_paper_v0.1.3`\
**Source sections:** Entire edition, all sections and named claims\
**Obligation disposition:** Written family; historical delta review pending.

**Original scope boundary.** Do not infer complete containment from the unchanged section numbering.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-013.1 | Intermediate typed-process/GR/PR formalization — Provides the typed-process, GR and PR definitions and identifies v0.1.3 as a separate thirteen-statement historical edition. | WRITTEN | [`eq:C03-chronology`](MATHEMATICAL_CROSSWALK.md#c03); [`thm:C03-composition`](MATHEMATICAL_CROSSWALK.md#c03); [`def:C04-GR`](MATHEMATICAL_CROSSWALK.md#c04); [`def:C05-PR`](MATHEMATICAL_CROSSWALK.md#c05); [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b) |
| PRIOR-013.2 | Exact old assumptions, examples and exclusions retained in version reconciliation — Retains the principal earlier assumptions, examples and exclusions at explicit current destinations; complete clause-by-clause preservation/correction for v0.1.3 remains unverified. | HISTORICAL_DELTA_PENDING | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`subsec:C05-witness`](MATHEMATICAL_CROSSWALK.md#c05); [`ex:periodic-original`](MATHEMATICAL_CROSSWALK.md#c27); [`ex:bernoulli-factorization`](MATHEMATICAL_CROSSWALK.md#c27) |

**Retained review limits.** Exact v0.1.3 hypotheses, examples and exclusions have not all been compared clause by clause against the final current manuscript.

## PRIOR-014

**Source:** `original_paper_v0.1.6`\
**Source sections:** Entire edition, all sections and named claims\
**Obligation disposition:** Written family; historical delta review pending.

**Original scope boundary.** This edition contributes an explicit nuisance-padding result relative to the earlier named-claim list; later equivalent statements need exact reconciliation.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-014.1 | Earlier submission formulation and fixed-relevance nuisance-padding exclusion — Records v0.1.6’s added fixed-relevance nuisance-padding result and proves why a nuisance-only replacement cannot change a relevance-factorized property. | WRITTEN | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`prop:C05-nuisance`](MATHEMATICAL_CROSSWALK.md#c05); [`def:C05-grounded`](MATHEMATICAL_CROSSWALK.md#c05) |
| PRIOR-014.2 | Existing example, feedback, identification and generalization content — Retains example, feedback, identification and extension families with actual arguments and open-boundary statements; no complete v0.1.6 unique-clause reconciliation is claimed. | HISTORICAL_DELTA_PENDING | [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`ex:periodic-original`](MATHEMATICAL_CROSSWALK.md#c27); [`ex:bernoulli-factorization`](MATHEMATICAL_CROSSWALK.md#c27); [`sub:C28:01`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C31:04`](MATHEMATICAL_CROSSWALK.md#c31) |

**Retained review limits.** The added nuisance-padding result is explicitly covered; exhaustive semantic reconciliation of the other v0.1.6 clauses remains open.

## PRIOR-015

**Source:** `original_paper_v0.1.7`\
**Source sections:** Entire edition plus post-proofread test suite\
**Obligation disposition:** Written family; historical delta review pending.

**Original scope boundary.** Testing records are historical evidence, not substitute proofs. Preserve correction provenance into v0.1.8.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-015.1 | Expanded Polish-descriptor, killed-kernel, QSD, perturbation, family-signature and quotient results — Writes the expanded Polish-descriptor, killed-kernel, QSD, two-sided perturbation, family-signature and compatible-quotient mathematics, including independent gates. | WRITTEN | [`prop:A-Polish`](MATHEMATICAL_CROSSWALK.md#appendix-a); [`thm:C04-killed`](MATHEMATICAL_CROSSWALK.md#c04); [`thm:C04-QSD`](MATHEMATICAL_CROSSWALK.md#c04); [`lem:C-output-errors`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`thm:C-signature`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`thm:C16:exact`](MATHEMATICAL_CROSSWALK.md#c16) |
| PRIOR-015.2 | Historical proofread tests and source claims separated from theorem proofs — Distinguishes the historical proofreading/test record and producing source from analytic proofs or a new compiler execution; full v0.1.7-to-v0.1.8 clause-level correction provenance remains a review task. | HISTORICAL_DELTA_PENDING | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:C29:05`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C30:04`](MATHEMATICAL_CROSSWALK.md#c30) |

**Retained review limits.** The expanded mathematics and historical evidence distinction are written; complete edition-specific proofread/correction provenance is not independently reconciled.

## PRIOR-016

**Source:** `original_paper_v0.1.8`\
**Source sections:** §3; Theorem3.1; Proposition3.2\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The entire typed factorization and physical-fixed intervention meaning must be preserved, not just the induced kernel.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-016.1 | Strategic/world split and alpha→P→U chronology — Specifies alpha then physical P then strategic U on their full typed arguments and derives the composed joint-state kernel. | WRITTEN | [`eq:C03-chronology`](MATHEMATICAL_CROSSWALK.md#c03); [`eq:C03-induced`](MATHEMATICAL_CROSSWALK.md#c03); [`thm:C03-composition`](MATHEMATICAL_CROSSWALK.md#c03) |
| PRIOR-016.2 | Feasibility and well-posed composed kernel — States feasibility support and measurable-kernel assumptions, proves normalized composition and constructs the canonical path law. | WRITTEN | [`eq:C03-feasibility`](MATHEMATICAL_CROSSWALK.md#c03); [`thm:C03-composition`](MATHEMATICAL_CROSSWALK.md#c03); [`thm:C03-path`](MATHEMATICAL_CROSSWALK.md#c03); [`lem:C-compProd`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-016.3 | Enlarged-state Markov reduction — Derives the enlarged-state Markov description and action erasure while retaining the information carried by action-marked histories. | WRITTEN | [`eq:C03-cylinder`](MATHEMATICAL_CROSSWALK.md#c03); [`prop:C03-erasure`](MATHEMATICAL_CROSSWALK.md#c03); [`prop:C-information`](MATHEMATICAL_CROSSWALK.md#appendix-c) |

## PRIOR-017

**Source:** `original_paper_v0.1.8`\
**Source sections:** §4; Proposition4.1a; Assumption4.1; Proposition4.2; Theorem4.2a; Corollaries4.2b–c; Definitions4.3/4.4a; Proposition4.4b\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** QSD conclusions are conditional on the eigenmeasure equation and accompanying hypotheses. Descriptor occupation, persistence and QSD are not interchangeable.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-017.1 | Global Polish descriptor and ex ante nontriviality — Constructs a Polish descriptor target with the selected topology and states ex ante region/basin/reference/nontriviality gates, including the distinct time-zero reachable-law condition. | WRITTEN | [`prop:A-Polish`](MATHEMATICAL_CROSSWALK.md#appendix-a); [`eq:C04-spec`](MATHEMATICAL_CROSSWALK.md#c04); [`def:C04-confirmatory`](MATHEMATICAL_CROSSWALK.md#c04) |
| PRIOR-017.2 | Equivalent exact invariance on all of B — Proves equivalence between one-step invariance throughout B and all-time pathwise retention from every B start. | WRITTEN | [`eq:C04-inv`](MATHEMATICAL_CROSSWALK.md#c04); [`cor:C04-exact`](MATHEMATICAL_CROSSWALK.md#c04) |
| PRIOR-017.3 | Killed-kernel persistence with exact exit indexing — Defines the killed kernel and exact first-exit indexing; derives retained endpoint mass, survival, and the extended exit/Green identities. | WRITTEN | [`thm:C04-killed`](MATHEMATICAL_CROSSWALK.md#c04); [`eq:C04-endpoint`](MATHEMATICAL_CROSSWALK.md#c04); [`eq:C04-survival`](MATHEMATICAL_CROSSWALK.md#c04); [`prop:C-Green`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-017.4 | Finite-persistence characterization and one-step bound — States finite persistence as the full-region retained-mass bound and proves q-to-the-L retention from a uniform one-step lower bound, while distinguishing optional metastability extensions. | WRITTEN | [`def:C04-quasi`](MATHEMATICAL_CROSSWALK.md#c04); [`thm:C04-killed`](MATHEMATICAL_CROSSWALK.md#c04); [`eq:C04-metastability`](MATHEMATICAL_CROSSWALK.md#c04) |
| PRIOR-017.5 | Exact GR and declared occupation-convergence mode — Defines Exact GR with its declared convergence mode and every admissible initial law, separating this from a chosen-start statement. | WRITTEN | [`def:C04-GR`](MATHEMATICAL_CROSSWALK.md#c04); [`eq:C04-occ`](MATHEMATICAL_CROSSWALK.md#c04); [`lem:A-initial-mixture`](MATHEMATICAL_CROSSWALK.md#appendix-a) |
| PRIOR-017.6 | QSD certification, survival and conditional stationarity; regime locus — States QK_B=lambda Q with its hypotheses, derives geometric survival and conditional stationarity, and preserves finite-persistence and regime-locus conditions separately. | WRITTEN | [`def:C04-QSD`](MATHEMATICAL_CROSSWALK.md#c04); [`thm:C04-QSD`](MATHEMATICAL_CROSSWALK.md#c04); [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b) |

## PRIOR-018

**Source:** `original_paper_v0.1.8`\
**Source sections:** §5; Definition5.1\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Retain original B1, property, relevance and intervention scope; failure of one protocol is not a global non-PR theorem.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-018.1 | Typed intervention grammar with fixed physical primitive — Defines fixed-P alpha/U interventions and the admissibility/compatibility grammar for component or block replacements. | WRITTEN | [`sec:C05`](MATHEMATICAL_CROSSWALK.md#c05); [`def:C11:grammar`](MATHEMATICAL_CROSSWALK.md#c11); [`prop:C11:assembly`](MATHEMATICAL_CROSSWALK.md#c11) |
| PRIOR-018.2 | Property maps on whole paths and comparison-set diversity — Defines total property maps on actual whole-path laws, the shared metric and multi-start comparison domain, retaining time-zero diversity and all original gates. | WRITTEN | [`eq:C05-values`](MATHEMATICAL_CROSSWALK.md#c05); [`eq:C05-margin`](MATHEMATICAL_CROSSWALK.md#c05); [`def:C05-PR`](MATHEMATICAL_CROSSWALK.md#c05) |
| PRIOR-018.3 | Original strategic constitution, protocol-scoped negative claims and regime equivalence — States constitution and uniform margin, gives the compatible law/property preservation theorem and explains why failure of one protocol is not a family-wide non-PR claim. | WRITTEN | [`def:C05-PR`](MATHEMATICAL_CROSSWALK.md#c05); [`thm:C05-representation`](MATHEMATICAL_CROSSWALK.md#c05); [`thm:C-signature`](MATHEMATICAL_CROSSWALK.md#appendix-c) |

## PRIOR-019

**Source:** `original_paper_v0.1.8`\
**Source sections:** §5.4.1; Proposition5.2; Corollary5.3\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** These metric bounds begin after both output-law errors have been justified; numerical margin alone is not an Exact GR/PR certificate.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-019.1 | Two-sided constitutive-margin perturbation bound — Derives the reverse-triangle bound with separate baseline and treatment output-law errors and transports it through infima on the full shared comparison set. | WRITTEN | [`lem:C-output-errors`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`thm:C15:margin`](MATHEMATICAL_CROSSWALK.md#c15); [`eq:C15:margin`](MATHEMATICAL_CROSSWALK.md#c15) |
| PRIOR-019.2 | Strict positive robust margin and original definition bridge — Establishes strictly positive transported margin only above the sum of both error budgets and explicitly invokes the independent original GR/PR prerequisites. | WRITTEN | [`thm:C12:finitecertificate`](MATHEMATICAL_CROSSWALK.md#c12); [`eq:C12:transport`](MATHEMATICAL_CROSSWALK.md#c12); [`thm:C15:margin`](MATHEMATICAL_CROSSWALK.md#c15) |

## PRIOR-020

**Source:** `original_paper_v0.1.8`\
**Source sections:** Proposition5.4\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** A finite-prefix bound does not automatically control infinite survival or exact invariance.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-020.1 | Finite-horizon kernel-to-path TV envelope — Constructs chronological common submeasures for actual finite prefixes; the product retained-mass envelope yields the classical finite-horizon TV bound as a consequence. | WRITTEN | [`thm:C13:product`](MATHEMATICAL_CROSSWALK.md#c13); [`eq:C13:product`](MATHEMATICAL_CROSSWALK.md#c13); [`G:commonmass`](MATHEMATICAL_CROSSWALK.md#appendix-g); [`G:fullpath`](MATHEMATICAL_CROSSWALK.md#appendix-g) |
| PRIOR-020.2 | Exact probability-distance convention and baseline/intervention error separation — Uses event-supremum TV (one half of finite l1), distinguishes matched starts and initial discrepancy, and propagates separate baseline/treatment budgets without claiming infinite-survival control. | WRITTEN | [`eq:C13:TV`](MATHEMATICAL_CROSSWALK.md#c13); [`prop:C12:primitiveTV`](MATHEMATICAL_CROSSWALK.md#c12); [`eq:C12:prefixbudget`](MATHEMATICAL_CROSSWALK.md#c12); [`G:discount`](MATHEMATICAL_CROSSWALK.md#appendix-g) |

## PRIOR-021

**Source:** `original_paper_v0.1.8`\
**Source sections:** §6; Theorems6.1–6.2\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The embedding/recovery statements must accompany the full EGR predecessor material, not replace it.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-021.1 | Exact lifted EGR embedding — Proves the world-lift and action-record variants of EGR embedding, matching the actual chronological law and the predecessor descriptor/occupation semantics. | WRITTEN | [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-lumping`](MATHEMATICAL_CROSSWALK.md#c06); [`eq:C06-record`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c) |
| PRIOR-021.2 | Conservative recovery of the earlier PR notion under admissible Paper-I protocol — Recovers the earlier policy-constitutive PR notion for the Paper-I admissible protocol while retaining all standalone EGR benchmark models and diagnostics. | WRITTEN | [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06); [`def:C06-policy-PR`](MATHEMATICAL_CROSSWALK.md#c06); [`app:C`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b) |

## PRIOR-022

**Source:** `original_paper_v0.1.8`\
**Source sections:** §7 except quotient; Propositions7.1/7.4/7.4a/7.5; Theorems7.2–7.3\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Resolve the historical prose-versus-provider witness mismatch for Theorem7.3 explicitly; do not rewrite the old receipt or silently substitute a different example.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-022.1 | Baseline path/occupation invariance — Proves that corresponding baseline kernels and descriptor/initial-law semantics preserve the baseline path and GR occupation statements. | WRITTEN | [`thm:C05-representation`](MATHEMATICAL_CROSSWALK.md#c05); [`eq:C05-intertwining`](MATHEMATICAL_CROSSWALK.md#c05) |
| PRIOR-022.2 | Factorization non-identification from induced process — Constructs distinct alpha/P/U factorizations with equal baseline induced process, so baseline dynamics do not identify the primitive mechanisms. | WRITTEN | [`subsec:C05-witness`](MATHEMATICAL_CROSSWALK.md#c05); [`ex:bernoulli-factorization`](MATHEMATICAL_CROSSWALK.md#c27) |
| PRIOR-022.3 | Constitutive noninvariance under common baseline — Calculates unequal constitution under common baseline laws. The original stochastic Bernoulli/SLLN example and deterministic identity-kernel/provider variants are explicitly distinguished, including the custom-True convergence predicate. | WRITTEN | [`subsec:C05-witness`](MATHEMATICAL_CROSSWALK.md#c05); [`ex:bernoulli-factorization`](MATHEMATICAL_CROSSWALK.md#c27) |
| PRIOR-022.4 | Full intervention-family signatures and compatible invariance — Defines full frozen intervention-family signatures with predeclared label matching and proves invariance only when the baseline and every relevant treatment/property map correspond. | WRITTEN | [`eq:C-app-signature`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`thm:C-signature`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`thm:C05-representation`](MATHEMATICAL_CROSSWALK.md#c05) |
| PRIOR-022.5 | Grounding/relevance map and nuisance-padding exclusion — States the relevance-factorization and grounding maps and proves nuisance-padding exclusion for a fixed declared relevance map. | WRITTEN | [`eq:C05-groundingmaps`](MATHEMATICAL_CROSSWALK.md#c05); [`def:C05-grounded`](MATHEMATICAL_CROSSWALK.md#c05); [`prop:C05-nuisance`](MATHEMATICAL_CROSSWALK.md#c05) |

## PRIOR-023

**Source:** `original_paper_v0.1.8`\
**Source sections:** §7.4.2; Theorem7.4b\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Ordinary lumpability alone does not imply PR preservation.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-023.1 | Intervention-compatible quotient preservation — Proves Exact-GR and original PR preservation under the full typed intervention-compatible quotient certificate, not only baseline lumpability. | WRITTEN | [`thm:C16:exact`](MATHEMATICAL_CROSSWALK.md#c16); [`I:exactpath`](MATHEMATICAL_CROSSWALK.md#appendix-i); [`I:semantics`](MATHEMATICAL_CROSSWALK.md#appendix-i) |
| PRIOR-023.2 | Exact descriptor/property/basin/comparison-set transport and full family matching — Retains region preimage, descriptor/convergence compatibility, basin-law lifting, exact comparison-set image, common property and all-family target/label matching; derives equality of effect ranges and infima. | WRITTEN | [`eq:C16:spec`](MATHEMATICAL_CROSSWALK.md#c16); [`eq:C16:property`](MATHEMATICAL_CROSSWALK.md#c16); [`thm:C16:exact`](MATHEMATICAL_CROSSWALK.md#c16); [`I:margins`](MATHEMATICAL_CROSSWALK.md#appendix-i) |

## PRIOR-024

**Source:** `original_paper_v0.1.8`\
**Source sections:** §8; Proposition8.1\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Keep the original examples and their assumptions even where the repository adds stronger or different examples.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-024.1 | Periodic Exact GR without equilibrium primitive — Gives the original deterministic two-cycle, empirical-measure calculation and actual almost-sure weak occupation limit without an equilibrium primitive. | WRITTEN | [`ex:periodic-original`](MATHEMATICAL_CROSSWALK.md#c27); [`sub:C27:01`](MATHEMATICAL_CROSSWALK.md#c27) |
| PRIOR-024.2 | Discrete strategy/world feedback example — Retains its discrete strategy/world feedback interpretation and distinguishes feedback bookkeeping from identified causal structure. | WRITTEN | [`ex:periodic-original`](MATHEMATICAL_CROSSWALK.md#c27); [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b) |
| PRIOR-024.3 | Baseline-equivalent processes with different constitution — Retains the original stochastic equal-baseline/different-constitution model with an actual occupation argument, while separately identifying later deterministic and custom-mode witnesses. | WRITTEN | [`ex:bernoulli-factorization`](MATHEMATICAL_CROSSWALK.md#c27); [`sub:C27:02`](MATHEMATICAL_CROSSWALK.md#c27); [`subsec:C05-witness`](MATHEMATICAL_CROSSWALK.md#c05) |

## PRIOR-025

**Source:** `original_paper_v0.1.8`\
**Source sections:** §9\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Feedback/causal semantics cannot generally be recovered from K alone.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-025.1 | Generator class versus regime class — Separates the class of behavioral generators from classification of the generated process and lists the independent profile coordinates. | WRITTEN | [`sub:C01:01`](MATHEMATICAL_CROSSWALK.md#c01); [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`tab:profile-axes`](MATHEMATICAL_CROSSWALK.md#appendix-b) |
| PRIOR-025.2 | Typed feedback graph and its interpretation — Defines strategic-to-world and world-to-strategic dependencies with mechanism-relative signs; factorization nonidentification explains why K alone generally does not determine them. | WRITTEN | [`eq:C03-chronology`](MATHEMATICAL_CROSSWALK.md#c03); [`eq:C03-induced`](MATHEMATICAL_CROSSWALK.md#c03); [`sub:B:02`](MATHEMATICAL_CROSSWALK.md#appendix-b) |

## PRIOR-026

**Source:** `original_paper_v0.1.8`\
**Source sections:** §10.4–10.7; AppendixB.6/B.8; complete AppendixC\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** No representative/average/majority model substitutes for a uniform identified-set certificate. If a valid outer set includes zero constitution, report statistical unresolvedness.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-026.1 | Three-layer confirmatory architecture — Defines mathematical validity, semantic specification and empirical/statistical certification as separate layers of one frozen application. | WRITTEN | [`def:confirmatory-pipeline`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:01`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-026.2 | Full provenance-valid identified model set — Defines the nonempty provenance-valid identified model set and universal model/start comparisons, with pointwise, uniform-gap and directional conclusions distinguished. | WRITTEN | [`def:identified-constitution`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:modelset-distinction`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-026.3 | One joint outer structural/statistical uncertainty set — Uses a single joint outer structural/statistical uncertainty object and a lower bound on the infimum effect over every model/start in that object. | WRITTEN | [`thm:outer-certificate`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-026.4 | Simultaneous rather than pointwise uncertainty guarantee — Proves the false-positive probability is at most alpha from simultaneous coverage; separate pointwise intervals do not supply that event. | WRITTEN | [`thm:outer-certificate`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-026.5 | Selection status, causal modularity, intervention-reachable support and provenance graph — States selection timing, causal modularity, treatment-reachable support and rooted acyclic provenance requirements; the eighteen-step workflow separates empirical roots, declared assumptions and mathematical consequences. | WRITTEN | [`sub:C28:01`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:07`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`sub:N:08`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-026.6 | Hard-target closure and component/grammar audit — Requires hard-target closure, held-fixed mechanisms and an explicit component/grammar audit before a constitutive comparison is interpreted. | WRITTEN | [`sub:C28:01`](MATHEMATICAL_CROSSWALK.md#c28); [`def:C11:grammar`](MATHEMATICAL_CROSSWALK.md#c11); [`sub:N:07`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-026.7 | Orthogonal application-certificate tuple and separate robust/sign/uniform-gap status — Gives the nine-coordinate application certificate and examples separating validity, identification, selection, statistical status, provenance, PR status, direction and uniform gap. | WRITTEN | [`sub:C28:01`](MATHEMATICAL_CROSSWALK.md#c28); [`def:identified-constitution`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:modelset-distinction`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:07`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-026.8 | All18 empirical/computational workflow steps — Retains all eighteen explicit workflow steps, from observation/admission and frozen specification through all-family checks, simultaneous uncertainty, falsifiers and publication of the certificate. | WRITTEN | [`sub:N:07`](MATHEMATICAL_CROSSWALK.md#appendix-n) |

## PRIOR-027

**Source:** `original_paper_v0.1.8`\
**Source sections:** §§10.1–10.3;11–13\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** A proposed extension remains explicitly conditional or open unless matched to a present exact theorem with its quantified hypotheses.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-027.1 | Analyst relativity and typed-factorization motivation — Explains analyst-relative frozen choices and why typed factorization is necessary for counterfactual interpretation; states concrete falsification tests under fixed choices. | WRITTEN | [`sub:C01:01`](MATHEMATICAL_CROSSWALK.md#c01); [`sub:C31:01`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:C31:07`](MATHEMATICAL_CROSSWALK.md#c31) |
| PRIOR-027.2 | Continuous-time, differential-inclusion, random/nonautonomous and partial-observation extension architectures — States continuous-time, flow, inclusion, random-environment and nonautonomous extension architectures and their additional obligations; separately presents completed finite belief/control and clock results at their exact scope. | WRITTEN | [`sub:C31:04`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:P:05`](MATHEMATICAL_CROSSWALK.md#appendix-p); [`sub:P:06`](MATHEMATICAL_CROSSWALK.md#appendix-p); [`prop:C18-filter`](MATHEMATICAL_CROSSWALK.md#c18); [`thm:C18-alpha`](MATHEMATICAL_CROSSWALK.md#c18) |
| PRIOR-027.3 | Falsifiability, failure modes, novelty standard and all nonclaims — Retains failure modes, finite-versus-infinite distinctions, standard-mathematics/novelty boundaries and explicit nonclaims, including the intersample exit counterexample. | WRITTEN | [`sub:C31:01`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:C31:02`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:C31:05`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:C31:07`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:C30:05`](MATHEMATICAL_CROSSWALK.md#c30) |

## PRIOR-028

**Source:** `original_paper_v0.1.8`\
**Source sections:** AppendicesA/B/D and references\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Preserve exact old hashes and distinguish paper theorem, compiled provider, acceptance and empirical status.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-028.1 | Complete theorem/definition ledger — Provides the twenty-five named v0.1.8 statement crosswalk and the generated index of actual numbered current definitions/results; the surrounding text retains substantive unnumbered gates. | WRITTEN | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:O:03`](MATHEMATICAL_CROSSWALK.md#appendix-o) |
| PRIOR-028.2 | Technical explanations for global descriptors, multi-start B1, all-region invariance, exact exit indexing and other gates — Explains globality of descriptors, multiple comparison starts, full-region invariance, exact exit indexing and the limited strength of time-zero nontriviality. | WRITTEN | [`prop:A-Polish`](MATHEMATICAL_CROSSWALK.md#appendix-a); [`def:C04-GR`](MATHEMATICAL_CROSSWALK.md#c04); [`def:C04-confirmatory`](MATHEMATICAL_CROSSWALK.md#c04); [`thm:C04-killed`](MATHEMATICAL_CROSSWALK.md#c04); [`def:C05-PR`](MATHEMATICAL_CROSSWALK.md#c05); [`sub:C31:01`](MATHEMATICAL_CROSSWALK.md#c31) |
| PRIOR-028.3 | Formalization/source crosswalk and reproducibility record — Supplies source/manuscript crosswalk conventions, exact source and evidence identities, build/calculation commands and the distinct compiler/numerical/empirical reproduction routes. | WRITTEN | [`sub:O:02`](MATHEMATICAL_CROSSWALK.md#appendix-o); [`sub:O:04`](MATHEMATICAL_CROSSWALK.md#appendix-o); [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C30:04`](MATHEMATICAL_CROSSWALK.md#c30) |
| PRIOR-028.4 | Artifact revision lineage and scholarly references — Retains artifact-version lineage and scholarly dependencies; exact source hashes and historical evidence remain separately identified in the package and are not rewritten by new exposition. | WRITTEN | [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:B:03`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:C30:01`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C30:05`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C01:04`](MATHEMATICAL_CROSSWALK.md#c01) |

**Retained review limits.** The printed v0.1.8 named-statement ledger and current index are written. This map does not reproduce or freshly certify every historical compiler receipt, hash or bibliography comparison.

## PRIOR-029

**Source:** `original_paper_v0.1.8`\
**Source sections:** AppendixE plus all five supporting papers\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** These restricted algebraic structures do not yield universal GR/PR theorems without extra transfer hypotheses.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-029.1 | Every specialized finite-certificate/source-rigidity argument — Develops all five specialized argument families with equations and proofs: scalar defect, finite detection, first-bad shell/cubic rigidity, direct zero shift and Gram witnesses. | WRITTEN | [`C26:scalar`](MATHEMATICAL_CROSSWALK.md#c26); [`thm:C26:detection`](MATHEMATICAL_CROSSWALK.md#c26); [`C26:firstbad`](MATHEMATICAL_CROSSWALK.md#c26); [`C26:zerosource`](MATHEMATICAL_CROSSWALK.md#c26); [`C26:gram`](MATHEMATICAL_CROSSWALK.md#c26); [`app:M`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-029.2 | Precise source-to-restricted-subclass bridges — States actual path-law feature maps and supplied source identities needed to transfer each restricted algebraic result to constitutive effects, keeping those bridges conditional. | WRITTEN | [`M:interfaces`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`C26:gram`](MATHEMATICAL_CROSSWALK.md#c26); [`sub:C31:05`](MATHEMATICAL_CROSSWALK.md#c31) |

## PRIOR-030

**Source:** `accepted_research_companion_v0.2.0`\
**Source sections:** All17 accepted companion anchors, complete PDF/TeX/theorem map\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Historical status/open fields are frozen at source5822cdff0fc360d9e368e10ff5f7576c3141a1b3; later closures need explicit current-source status records, especially F1.MA2.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-030.1 | R.SCOPE, CORE.IDENTITY, C69.RESTART, C70.SWITCH — Records R.SCOPE and CORE.IDENTITY at the accepted companion SHA and provides the actual restart/entry/switch derivations for C69.RESTART and C70.SWITCH. | WRITTEN | [`sub:B:03`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30); [`thm:C10-restart`](MATHEMATICAL_CROSSWALK.md#c10); [`thm:C10-switch`](MATHEMATICAL_CROSSWALK.md#c10) |
| PRIOR-030.2 | A2.FINITE, E1.LINEAR, B2.SEQUENTIAL, F1.PROTOCOL, F1.MA2 — Treats A2.FINITE, E1.LINEAR, B2.SEQUENTIAL and F1.PROTOCOL with current proofs. F1.MA2 retains its historical open scope and the later strict-autonomy/marked-law distinction instead of retroactively changing the companion. | WRITTEN | [`sub:B:03`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`prop:C12:primitiveTV`](MATHEMATICAL_CROSSWALK.md#c12); [`thm:C13:product`](MATHEMATICAL_CROSSWALK.md#c13); [`thm:C16:geometric`](MATHEMATICAL_CROSSWALK.md#c16); [`prop:C11:assembly`](MATHEMATICAL_CROSSWALK.md#c11); [`thm:C24-matched`](MATHEMATICAL_CROSSWALK.md#c24); [`thm:C24-autonomy`](MATHEMATICAL_CROSSWALK.md#c24) |
| PRIOR-030.3 | A3.DUAL, A3.SURVIVAL, D2.RESIDENCE, D2.ORDER — Maps A3.DUAL/A3.SURVIVAL and D2.RESIDENCE/D2.ORDER to metric transport, survival boundaries, residence monitors, full-history/risk control and nature-order results. | WRITTEN | [`sub:B:03`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`thm:C14:duality`](MATHEMATICAL_CROSSWALK.md#c14); [`G:fullpath`](MATHEMATICAL_CROSSWALK.md#appendix-g); [`thm:C17-monitor-optimality`](MATHEMATICAL_CROSSWALK.md#c17); [`thm:C19-risk-optimality`](MATHEMATICAL_CROSSWALK.md#c19); [`thm:C22-rectangular`](MATHEMATICAL_CROSSWALK.md#c22) |
| PRIOR-030.4 | X1.MODEL, X1.NOEXACT, X1.OCCUPATION, X1.FINITEOUTPUT — Retains X1’s eighteen-state model, explicit failure of exact trapping, actual occupation and finite-output values with their typed-law identifications and comparison effects. | WRITTEN | [`sub:B:03`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`eq:C23-X1-matrix`](MATHEMATICAL_CROSSWALK.md#c23); [`cor:C23-X1-full-history`](MATHEMATICAL_CROSSWALK.md#c23); [`eq:C23-X1-targets`](MATHEMATICAL_CROSSWALK.md#c23); [`proof:L-03`](MATHEMATICAL_CROSSWALK.md#appendix-l); [`proof:L-04`](MATHEMATICAL_CROSSWALK.md#appendix-l); [`proof:L-05`](MATHEMATICAL_CROSSWALK.md#appendix-l) |

**Retained review limits.** Historical accepted-companion identity remains 5822cdff0fc360d9e368e10ff5f7576c3141a1b3. Current closures do not retroactively alter its accepted status fields.

## PRIOR-031

**Source:** `mathematical_closure_13_file_draft`\
**Source sections:** P–04 chapter and related appendix rows\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The old draft’s pending statements are historical; current Q05 whole-path closure must be reconciled from source. Positive leakage still does not prove Exact GR.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-031.1 | Canonical whole-path discounted score — Defines the actual normalized infinite discounted path score, proves measurability/integration and extends the bound to general summable nonnegative weights. | WRITTEN | [`C13:wholepath`](MATHEMATICAL_CROSSWALK.md#c13); [`eq:C13:discounted`](MATHEMATICAL_CROSSWALK.md#c13); [`G:discount`](MATHEMATICAL_CROSSWALK.md#appendix-g); [`thm:G:summable`](MATHEMATICAL_CROSSWALK.md#appendix-g) |
| PRIOR-031.2 | Chronological retained-mass envelope with separate baseline/treated witnesses — Builds chronological retained-mass envelopes with separate fine/coarse baseline and treatment source witnesses and domination assumptions. | WRITTEN | [`thm:C13:product`](MATHEMATICAL_CROSSWALK.md#c13); [`thm:C16:nonstationary`](MATHEMATICAL_CROSSWALK.md#c16); [`I:margins`](MATHEMATICAL_CROSSWALK.md#appendix-i) |
| PRIOR-031.3 | Dirac matched starts versus general nonzero initial mismatch — Distinguishes matched-Dirac original-margin scope (zero initial mismatch) from the general subprobability initial witness; proves why a mass-one common witness forces initial equality. | WRITTEN | [`C16:nonstationary`](MATHEMATICAL_CROSSWALK.md#c16); [`I:margins`](MATHEMATICAL_CROSSWALK.md#appendix-i); [`sub:P:02`](MATHEMATICAL_CROSSWALK.md#appendix-p) |
| PRIOR-031.4 | Exact original comparison-set projection and original full-B1 margin API — Uses the exact image of the full original comparison set and uniform baseline/treatment error bounds before taking the infimum; no sampled-start replacement is used. | WRITTEN | [`eq:C16:margin`](MATHEMATICAL_CROSSWALK.md#c16); [`I:margins`](MATHEMATICAL_CROSSWALK.md#appendix-i) |
| PRIOR-031.5 | Q05 concrete nonidentity witness, bound versus exact score/margin identities — Writes Q05’s nonidentity Boolean-to-singleton strategic compression, actual discounted scores, original margins 19/90 and 1/5, exact discrepancy 1/90 and separate bound 2/41, with the completed canonical-law source chain. | WRITTEN | [`C13:witnesses`](MATHEMATICAL_CROSSWALK.md#c13); [`G:fixtures`](MATHEMATICAL_CROSSWALK.md#appendix-g) |

**Retained review limits.** The source-specific stronger canonical original-margin adapter with a genuinely subprobability initial-mismatch witness remains explicitly residual in Appendix P; general measure-level bounds do not discharge it.

## PRIOR-032

**Source:** `mathematical_closure_13_file_draft`\
**Source sections:** P–05 chapter and reactive-history boundary\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Hidden common correlation lies outside the chosen conditional-product subclass. Reactive fixtures do not refute strict nonreactive opponent-locked theorems.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-032.1 | Separate maps for strategic state, action, joint state and physical/update inputs — Keeps state, action, joint-state and physical/update input maps distinct in measurable two-player assembly and protocol projection. | WRITTEN | [`eq:C24-products`](MATHEMATICAL_CROSSWALK.md#c24); [`eq:C24-induced`](MATHEMATICAL_CROSSWALK.md#c24); [`thm:C24-matched`](MATHEMATICAL_CROSSWALK.md#c24) |
| PRIOR-032.2 | Conditional-product measurable two-player kernel and full-path recovery — Derives the conditional-product kernel and canonical full-path recovery with explicit normalization and projection of the relevant marked inputs; arbitrary initial dependence is allowed. | WRITTEN | [`prop:C24-product`](MATHEMATICAL_CROSSWALK.md#c24); [`thm:C24-matched`](MATHEMATICAL_CROSSWALK.md#c24); [`proof:L-06`](MATHEMATICAL_CROSSWALK.md#appendix-l) |
| PRIOR-032.3 | Actual matched admitted CL/OL interventions — Identifies the actual matched admitted closed-loop and anchored open-loop replacements and their held-fixed world primitive, including additional autonomy premises where needed. | WRITTEN | [`thm:C24-matched`](MATHEMATICAL_CROSSWALK.md#c24); [`eq:C24-protocol-gap`](MATHEMATICAL_CROSSWALK.md#c24); [`thm:C24-autonomy`](MATHEMATICAL_CROSSWALK.md#c24) |
| PRIOR-032.4 | Marked histories and exact M02 scope distinction — Calculates strict-anchor marked-law separation despite equal unmarked marginals and separately records the reactive witness’s failed strictness and unfinished stronger M02 bridge. | WRITTEN | [`eq:L-marked-key`](MATHEMATICAL_CROSSWALK.md#appendix-l); [`proof:L-06`](MATHEMATICAL_CROSSWALK.md#appendix-l); [`sub:P:01`](MATHEMATICAL_CROSSWALK.md#appendix-p) |

**Retained review limits.** The stronger single reactive-opponent full marked-history bridge remains a residual integration/review object; the actual strict-anchor separation is not substituted for it.

## PRIOR-033

**Source:** `mathematical_closure_13_file_draft`\
**Source sections:** P–06 chapter and D09 nonlinear witness\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Preserve actual path-law identification and objective placement; E[F(nu_C)] is not F(E[nu_C]). A phase-aware controller is stationary on the augmented state.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-033.1 | Native phase-aware deterministic cycle with unchanged physical/update primitives — Gives the native Fin3-by-Bool phase construction with the same physical/update primitives and an explicitly phase-aware deterministic controller. | WRITTEN | [`eq:C21-native-phase-row`](MATHEMATICAL_CROSSWALK.md#c21); [`proof:K-06`](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| PRIOR-033.2 | Actual occupation-limit objective E[F(nu_C)] — Defines the nonlinear objective as the expectation of F of the random classwise limiting occupation measure and identifies it with the actual canonical law. | WRITTEN | [`eq:C21-actual-objective`](MATHEMATICAL_CROSSWALK.md#c21); [`prop:C21-exact-objective`](MATHEMATICAL_CROSSWALK.md#c21); [`proof:K-06`](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| PRIOR-033.3 | Restricted four deterministic phase-blind controller comparison — Calculates all four deterministic phase-blind policies and the restricted phase-aware comparison; the phase-aware policy is stationary on its augmented state. | WRITTEN | [`eq:C21-native-phase-row`](MATHEMATICAL_CROSSWALK.md#c21); [`proof:K-06`](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| PRIOR-033.4 | Randomized phase-blind counterexample to unrestricted dominance — Includes the randomized phase-blind boundary construction, so superiority over four deterministic rules is not promoted to unrestricted controller dominance. | WRITTEN | [`eq:C21-native-phase-row`](MATHEMATICAL_CROSSWALK.md#c21); [`proof:K-06`](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| PRIOR-033.5 | Mixed-initial classwise nonlinear score versus barycenter score — Calculates the mixed-initial classwise score and contrasts it with applying F after barycentering, preserving E[F(nu_C)] rather than F(E[nu_C]). | WRITTEN | [`ex:C21-nonlinear-mixture`](MATHEMATICAL_CROSSWALK.md#c21); [`eq:C21-random-limit`](MATHEMATICAL_CROSSWALK.md#c21); [`eq:C21-actual-objective`](MATHEMATICAL_CROSSWALK.md#c21) |

## PRIOR-034

**Source:** `mathematical_closure_13_file_draft`\
**Source sections:** All13 files including counterexamples, formal evidence, appendices, main/preamble/references\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The complete draft is a historical source. Its stale status prose cannot override current compiler evidence, and compiler success does not automatically establish independent acceptance.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-034.1 | Original45-case criterion routing versus accepted evidence — Identifies the original forty-five case records and distinguishes their routing, source proof, compiler evidence and independent acceptance fields. | WRITTEN | [`sub:B:03`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:O:02`](MATHEMATICAL_CROSSWALK.md#appendix-o) |
| PRIOR-034.2 | Eleven additional claim criteria — Retains the eleven later claims as a separate namespace, for fifty-six records altogether, including concrete residual criteria rather than conflating similarly spelled IDs. | WRITTEN | [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:P:01`](MATHEMATICAL_CROSSWALK.md#appendix-p) |
| PRIOR-034.3 | Full elaborated types/axioms, source-bound positive and negative evidence — Requires full elaborated types, implicit/bundled premises and transitive axioms; distinguishes negative compiler controls from semantic countermodels and preserves source-bound evidence. | WRITTEN | [`def:evidence-coordinates`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C29:05`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:P:01`](MATHEMATICAL_CROSSWALK.md#appendix-p) |
| PRIOR-034.4 | Draft/release/publication/independent-review distinctions — Separates draft, implementation, release/publication, fresh numerical execution, Lean replay and independent acceptance. Historical pending prose does not override later proof, and later proof does not create historical acceptance. | WRITTEN | [`sub:C29:02`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C29:05`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C30:04`](MATHEMATICAL_CROSSWALK.md#c30) |

**Retained review limits.** This map preserves the 45+11 criterion and evidence namespaces but is not a new elaborated-type/axiom audit of all source declarations or a new independent acceptance review.

## PRIOR-035

**Source:** `specialized_Weil_CCM`\
**Source sections:** Scalar-defect reduction paper, all sections/proofs\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Preserve concrete canonical dictionary assumptions and distinction between imported explicit-formula results and the paper’s structural reduction.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-035.1 | Pivoted-probe second differences and codimension-one completion — Expands pivoted differences and proves the codimension-one coefficient-sum-zero completion A=1a^T+a1^T. | WRITTEN | [`C26:scalar`](MATHEMATICAL_CROSSWALK.md#c26); [`eq:C26:seam`](MATHEMATICAL_CROSSWALK.md#c26); [`M:tent`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-035.2 | Two-sided coefficient-sum seam and diagonal rigidity — Combines the two-sided seam with independently proved constant diagonal to reduce the defect to delta times the all-ones matrix. | WRITTEN | [`eq:C26:seam`](MATHEMATICAL_CROSSWALK.md#c26); [`eq:C26:commonmode`](MATHEMATICAL_CROSSWALK.md#c26); [`M:tent`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-035.3 | Scalar-defect/rank-one reduction, single-scalar obstruction — Shows dimension independence and equivalence of full dictionary equality to one scalar tent defect, retaining rank-one rather than identity-shift semantics. | WRITTEN | [`eq:C26:scalardefect`](MATHEMATICAL_CROSSWALK.md#c26); [`M:tent`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-035.4 | Literal-tent explicit formula and recovered finite dictionary — Writes the literal dictionary kernels and tent transform; proves the mollified explicit-formula limit through zero, pole, prime and archimedean channels and recovers the exact finite dictionary. | WRITTEN | [`eq:M:basis`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`eq:M:tenttransform`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`M:tent`](MATHEMATICAL_CROSSWALK.md#appendix-m) |

**Retained review limits.** Full arithmetic source identities and analytic inputs are retained as the earlier papers’ concrete normalization, distinct from the current repository’s generic real-profile formalization; external analytic Lean recompilation was not performed.

## PRIOR-036

**Source:** `specialized_Weil_CCM`\
**Source sections:** Persistent finite detection paper, all sections/proofs\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The conditional off-critical-zero implication and RH-equivalent hierarchy criterion are not a proof of RH or universal finite positivity.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-036.1 | Common-support Weil bound and cross identity — Proves the common-support Weil estimate with inverse-square zero summability and the exact cross identity controlling two approximation errors. | WRITTEN | [`eq:C26:Weil`](MATHEMATICAL_CROSSWALK.md#c26); [`eq:C26:Weilbound`](MATHEMATICAL_CROSSWALK.md#c26); [`eq:M:Weilerror`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-036.2 | Two-jet localized approximation and exact three-mode correction — Constructs simultaneous two-jet approximation and the explicit -1/0/1 Fourier-mode correction enforcing all three moment conditions exactly. | WRITTEN | [`M:detection`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`eq:M:correction`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-036.3 | Boundary-flat approximation and strict finite sign transfer — Proves global C2 boundary-flat legality and strict sign transfer under an explicit error budget, identifying the complete-detector theorem as an upstream analytic input. | WRITTEN | [`thm:C26:detection`](MATHEMATICAL_CROSSWALK.md#c26); [`M:detection`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-036.4 | Rank-three moment map and exact constrained dimension — Gives an explicit right inverse of the three-moment map and deduces complex constrained dimension 2N-2, including the zero N=1 space. | WRITTEN | [`M:detection`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`thm:C26:detection`](MATHEMATICAL_CROSSWALK.md#c26) |
| PRIOR-036.5 | Centered zero extension, principal-block nesting and exact quadratic preservation — Proves centered zero extension preserves moments, test, norm, central principal-block identity and exact quadratic value. | WRITTEN | [`M:detection`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`thm:C26:detection`](MATHEMATICAL_CROSSWALK.md#c26) |
| PRIOR-036.6 | Persistent detection, upward-closed bad-size set and finite-hierarchy criterion — Derives upward-closed bad sizes and a persistent bad tail at fixed aperture; the conditional complete-detector and critical-line implications yield a hierarchy equivalence, not an unconditional positivity proof. | WRITTEN | [`M:detection`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`thm:C26:detection`](MATHEMATICAL_CROSSWALK.md#c26); [`M:abstractdetection`](MATHEMATICAL_CROSSWALK.md#appendix-m) |

**Retained review limits.** The complete-detector theorem is an explicit analytic source input; this edition proves the finite approximation/transfer consequences and does not claim a new proof of the upstream detector or global positivity.

## PRIOR-037

**Source:** `specialized_Weil_CCM`\
**Source sections:** First-bad cubic rigidity paper, all sections/proofs\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** The result classifies constraints forced by hypothetical badness; retain all source, parity, first-bad and safe-negative-shift assumptions.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-037.1 | Globally first-bad parity/predecessor reduction and shell decomposition — Uses globally first-bad minimality, parity dimensions and predecessor positivity to obtain one-dimensional successor shells and a negative mode with nonzero shell component. | WRITTEN | [`C26:firstbad`](MATHEMATICAL_CROSSWALK.md#c26); [`M:firstbad`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-037.2 | Canonical cubic generator, factorization and shell incidence — Constructs the nonzero canonical cubic generator, proves its shell incidence, and derives rank-at-most-one source-normal factorization; nonzero generator does not force nonzero coefficient functional. | WRITTEN | [`M:firstbad`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`M:parity`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-037.3 | Negative constrained eigenmode and exact secular equivalence — Proves exact predecessor cancellation and both directions between negative compressed eigenmodes and the genuine scalar secular equation in a one-dimensional shell. | WRITTEN | [`eq:C26:trial`](MATHEMATICAL_CROSSWALK.md#c26); [`eq:C26:secular`](MATHEMATICAL_CROSSWALK.md#c26); [`M:firstbad`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-037.4 | Quotient–Schur/resolvent bridge and kernel-range decomposition — Derives the quotient/Schur determinant and full vector equations for arbitrary shell dimension and the kernel/range decomposition for singular cores. | WRITTEN | [`eq:C26:Schur`](MATHEMATICAL_CROSSWALK.md#c26); [`M:firstbad`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`M:zero`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-037.5 | Regular/resonant zero-shift branches — Separates compatible regular zero-shift preimages from a nonzero kernel projection causing the exact inverse pole; no singular inverse is substituted at zero. | WRITTEN | [`eq:C26:pole`](MATHEMATICAL_CROSSWALK.md#c26); [`M:zero`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-037.6 | Source-explicit cubic defect and cross-parity transfer — Extracts the concrete quadratic-normal source functional and derives cross-parity transfer with all inherited correction terms and safe-negative-shift hypotheses. | WRITTEN | [`eq:C26:cubicdefect`](MATHEMATICAL_CROSSWALK.md#c26); [`eq:C26:transfer`](MATHEMATICAL_CROSSWALK.md#c26); [`M:parity`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-037.7 | Exact overlap and root specializations; first-bad rigidity conclusion — Proves the exact overlap coefficient and specializes at even/odd roots without dividing by possibly zero factors; the conclusion constrains hypothetical first badness rather than ruling it out. | WRITTEN | [`M:parity`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`eq:C26:transfer`](MATHEMATICAL_CROSSWALK.md#c26) |

**Retained review limits.** Concrete source commutation/displacement identities belong to the earlier canonical hierarchy; generic shell algebra alone does not establish them.

## PRIOR-038

**Source:** `specialized_Weil_CCM`\
**Source sections:** Zero-shift source rigidity paper, all sections/proofs\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Zero shift is proved directly, not obtained by substituting zero into an inverse/resolvent formula that may be singular. Preserve preimage-dependence qualifications.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-038.1 | Production source decomposition — Writes the canonical pole, reduced archimedean diagonal/off-diagonal and finite prime decomposition of the production source functional in its fixed normalization. | WRITTEN | [`eq:M:production`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`M:production`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-038.2 | Denominator-free kernel/source transport and projected compatibility — Derives denominator-free kernel transport and full odd-kernel projected compatibility, retaining the entire kernel rather than a one-dimensional substitute. | WRITTEN | [`eq:M:kerneltransport`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`M:zero`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-038.3 | Direct zero-shift preimages and transfer — Supplies explicit preimages H±x±=b± and proves the zero-shift transfer directly by inner products and predecessor equations. | WRITTEN | [`eq:C26:zerotransfer`](MATHEMATICAL_CROSSWALK.md#c26); [`M:zero`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-038.4 | Product law, nondegenerate kernel annihilation and degeneration dichotomy — Proves Gamma_0 Phi(z)=0 for every even-kernel vector, its nondegenerate annihilation implication and source-visible degeneration alternative, with preimage-dependent coefficients allowed. | WRITTEN | [`eq:C26:zerotransfer`](MATHEMATICAL_CROSSWALK.md#c26); [`M:zero`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-038.5 | Arithmetic kernel-balance consequence — Combines the product law with the actual production decomposition to obtain exact arithmetic kernel balance under both preimages and nonzero overlap; no termwise sign assertion is made. | WRITTEN | [`eq:M:production`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`M:production`](MATHEMATICAL_CROSSWALK.md#appendix-m) |

**Retained review limits.** Canonical production matrices are fixed source objects, and the zero-shift theorem remains conditional on explicit compatible preimages and the stated overlap branch.

## PRIOR-039

**Source:** `specialized_Weil_CCM`\
**Source sections:** Explicit Gram witnesses paper, all sections/proofs\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** A negative witness for an isolated visible pair is not automatically a negative witness for the complete sum when other contributions can mask it.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-039.1 | Signed pair block and Gram determinant — Defines the signed pair block and Gram gap Delta and relates complex reflected responses to two real rank-one terms. | WRITTEN | [`C26:gram`](MATHEMATICAL_CROSSWALK.md#c26); [`eq:C26:Gram`](MATHEMATICAL_CROSSWALK.md#c26); [`M:gram`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-039.2 | Explicit negative vector identity and normalized margin — Expands the explicit witness w, its norm and negative quadratic value and obtains normalized margin c Delta / &#124;&#124;x&#124;&#124;^2. | WRITTEN | [`eq:C26:Gram`](MATHEMATICAL_CROSSWALK.md#c26); [`M:gram`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-039.3 | Exact isolated-pair spectrum/inertia — Derives both nonzero eigenvalues and isolated-pair inertia (1,1,d-2), with zero-gap cases treated separately. | WRITTEN | [`M:gram`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-039.4 | PSD-cone separation — Uses the witness functional and finite spectral decomposition to separate the signed block from the whole PSD cone. | WRITTEN | [`M:gram`](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| PRIOR-039.5 | Operator-norm robustness and exact witness masking — Proves operator-norm robustness and the exact additional-background threshold; explicitly calculates positive masking of the original negative witness. | WRITTEN | [`M:gram`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`C26:gram`](MATHEMATICAL_CROSSWALK.md#c26); [`sub:P:04`](MATHEMATICAL_CROSSWALK.md#appendix-p) |
| PRIOR-039.6 | Amplification-to-separation principle and finite visibility — States the amplification-to-separation condition and finite transversality visibility, requiring control of the complete background and actual path-feature identity before stronger conclusions. | WRITTEN | [`M:gram`](MATHEMATICAL_CROSSWALK.md#appendix-m); [`M:interfaces`](MATHEMATICAL_CROSSWALK.md#appendix-m) |

**Retained review limits.** Finite visible-pair negativity is not full-population negativity. The source-specific interpretation and independently executed zero-gap historical control retain separate evidence status.

## PRIOR-040

**Source:** `GSCRD_master_history`\
**Source sections:** Complete master theory/history/operating guide; all30 sections and appendices\
**Obligation disposition:** Written family with source-wording clarification.

**Original scope boundary.** Missing observations are not zeros; current-vintage historical data were not necessarily available then. No equilibrium, nonlinear stability, attractor, structural causality, collapse probability or GR/PR certificate follows from the dashboard alone.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-040.1 | Live v0.3b-r5 versus retrospective v0.5 R14.1 lineage — Identifies live v0.3b-r5 versus retrospective v0.5 R14.1 and explains why changed panels, normalizers and validity windows change the model fingerprint and prospective interpretation. | WRITTEN | [`sub:C28:02`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:06`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`sub:B:04`](MATHEMATICAL_CROSSWALK.md#appendix-b) |
| PRIOR-040.2 | Evidence ontology and as-of/source/decision time semantics — Separates effective, publicly known, acquired and recorded times; distinguishes facts, claims, institutional labels, stress, control and context, with explicit as-of admission and correction semantics. | WRITTEN | [`sub:C28:02`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-040.3 | Measurement normalization, coverage and missingness — Writes clipped affine/quantile/deficit normalizers, observed coverage, evaluability thresholds and sharp lower/upper completion bounds; missing observations are not inserted as zeros. | WRITTEN | [`eq:normalizers`](MATHEMATICAL_CROSSWALK.md#c28); [`eq:missingness-interval`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:completion-bounds`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-040.4 | Rolling-window geometry and missingness-aware distance — Retains the declared rolling windows and missingness-aware vector completion geometry. The source guide’s relevant section defines completion intervals, not a separate general distance function; the inventory word distance is therefore clarified rather than treated as an unlocated metric theorem. | SOURCE_WORDING_CLARIFIED | [`sub:C28:02`](MATHEMATICAL_CROSSWALK.md#c28); [`eq:missingness-interval`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:completion-bounds`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-040.5 | Adaptive/control and signed-network architecture — Defines adaptive/control scalars, normalized signed and gross edge arithmetic and the distinction between scoring-network structure and a transition/stability operator. | WRITTEN | [`sub:C28:03`](MATHEMATICAL_CROSSWALK.md#c28); [`eq:signed-network`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:06`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-040.6 | G0–G4 classifier, temporal-resolution and historical-null logic — Gives three-valued G0–G4 logic, temporal-resolution rules, historical null periods excluding 2026, R28/R30 distinction, evaluable-component counts and unresolved classifier gates. | WRITTEN | [`sub:C28:03`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-040.7 | Fourteen stress vectors, eight control families and E3 edge registries — Enumerates the fourteen stress vectors, eight control families, ninety total channels and frozen positive/negative E3 edge registries; proves signed rectangular bounds and scale/permutation invariances. | WRITTEN | [`sub:N:06`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-040.8 | Mathematical property claims and explicit no-causal-certification boundary — States the mathematical scoring bounds and the absence of equilibrium, nonlinear stability, attractor, structural-causal, collapse-probability or GR/PR certification from dashboard values. | WRITTEN | [`sub:C28:03`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:06`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`sub:N:08`](MATHEMATICAL_CROSSWALK.md#appendix-n) |

**Retained review limits.** The inventory phrase missingness-aware distance overstates the named source object: the guide’s missingness-aware vector geometry gives completion intervals. No unlocated distance theorem is invented. All thirty historical sections have not received an independent unique-clause diff.

## PRIOR-041

**Source:** `Brown_MacKay_finite_grid`\
**Source sections:** Certification ZIP README, full E2E report, v0.3 findings, source hashes\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Reported certification applies to BM-FG-TURN-0.005-v0.4 only. It does not certify the unmodified continuous-action source paper or a real market.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-041.1 | Frozen finite-grid turn-based model and equilibrium certificate — Defines the frozen 601-price turn-based trigger game and supplies the exact integer best-response enumeration, payoff/gap values and full-history one-shot verification argument. | WRITTEN | [`sub:C28:04`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:bm-exact`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:05`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-041.2 | Declared EGR/constitutive property and strict protocol scope — Defines the phase-aware descriptor, full high-price region/basin, counting measure and fixed-P policy replacement; proves exact baseline invariance/Dirac occupation and uniform survival margin one in this finite model. | WRITTEN | [`sub:C28:04`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:bm-exact`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-041.3 | Robustness checks, clean-room procedure and continuous-source comparison — Retains grid, tie, upper-bound, threshold and discount attacks; exact threshold interval; clean-directory and nonimporting checker reports; and numerical comparison with the continuous source without identifying the two models. | WRITTEN | [`par:C28:bm-repair`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:05`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-041.4 | Version0.3-to0.4 repair lineage — Records the exact v0.3 omissions and v0.4 repairs: measure, B1, property codomain/metric, unified sensitivity generation, source-equation solution, source hashes and local freeze provenance; primary equilibrium/intervention unchanged. | WRITTEN | [`par:C28:bm-repair`](MATHEMATICAL_CROSSWALK.md#c28) |

**Retained review limits.** Only the frozen finite turn-based model is certified by the constructed mathematics. Continuous-source benchmark and archived clean-room/sensitivity results remain distinct from this edition’s fresh exact integer enumeration.

## PRIOR-042

**Source:** `MIDR_lineage`\
**Source sections:** v1 report; legacy v0.1/.2/.4/.5; v0.6 refinement/spec/crosswalk; archive status\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Node-level causal elasticities, uniform full-basin finite persistence, exact invariance/occupation and strategic constitution are explicitly not established. Preserve generic model and identification content without operational targeting recommendations.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-042.1 | Historical network/state/measurement model and source ontology — Defines the dependency-network state, normalized descriptor, finite-horizon property, typed perturbation response and four evidence tiers. Retains the correction from an alleged transition matrix to a support/gain prior. | WRITTEN | [`sub:C28:05`](MATHEMATICAL_CROSSWALK.md#c28); [`eq:midr-property`](MATHEMATICAL_CROSSWALK.md#c28); [`par:C28:midr-lineage`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-042.2 | Coverage, dated evidence and calibration/validation distinction — Distinguishes dated administrative/documentary and causal-design evidence, requires adequate raw panel/concordance/pretrends and forbids node-level point identification when those gates fail. | WRITTEN | [`par:C28:midr-lineage`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:02`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-042.3 | GR/PR mathematical refinement and comparison-scope requirements — Requires a frozen world locus, averages, thresholds, comparison domain and typed intervention. Separates simple-path products from repeated-walk resolvents and leaves exact GR/constitution gates unestablished. | WRITTEN | [`eq:midr-property`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:05`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-042.4 | Frozen forward-validation protocol and archive empirical status — Retains the 22 August 2026 discovery end and 23 August held-out start, fixed region/descriptor/topology, null comparisons and explicit topology/constitution/invariance/occupation falsifiers. | WRITTEN | [`par:C28:midr-lineage`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:08`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-042.5 | Exact relation to embedded EGR and original v0.1.0 source — Identifies embedded EGR and generalized v0.1.0 sources and v0.4/v0.5/v0.6/v1.0 release roles. Full unique-clause reconciliation across every legacy MIDR report is not certified. | WRITTEN | [`par:C28:midr-lineage`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:B:01`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`thm:C06-embedding`](MATHEMATICAL_CROSSWALK.md#c06) |

**Retained review limits.** Legacy v0.1/.2/.4/.5 and v0.6/v1.0 roles are identified; a complete report-by-report unique-clause reconciliation remains open. No operational dependency or targeting prescription is reproduced.

## PRIOR-043

**Source:** `Russia_Ukraine_lineage`\
**Source sections:** v0.2.1 paper, FOI v0.4.1 archive, historical modeling review\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Historical exploratory patterns and constructed model comparisons do not prove empirical Exact GR/PR or identify operational effects. Preserve methods, equations and status, with no tactical implementation guidance.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-043.1 | Weekly state ontology, provenance and missingness — Distinguishes event and weekly-state ledgers, source/known-at timing, direct and attributed events, observation loss and observed outside-region states. | WRITTEN | [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:02`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-043.2 | Candidate region, coupling/breadth and descriptive occupancy — Defines occupancy conditional on evaluability and reports the archived broad/central/strict values, event/episode counts and measurement-ablation scope, separate from all-start survival. | WRITTEN | [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-043.3 | Response chains, clustering, temporal/placebo and sensitivity tests — Writes the equal-window directional placebo versus circular-phase-shift null, names both directions, preserves exact reported rates/ratios/p-values and memory/effect-weight sensitivity. | WRITTEN | [`par:C28:case-diagnostics`](MATHEMATICAL_CROSSWALK.md#c28); [`par:C28:case-memory`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-043.4 | Recognition/causal-history identification limits and memory dependence — States that the separate claims layer is incomplete and recognition/causal history is not identified; shows substantial dependence of measured occupancy on declared memory. | WRITTEN | [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28); [`par:C28:case-memory`](MATHEMATICAL_CROSSWALK.md#c28); [`sec:C06`](MATHEMATICAL_CROSSWALK.md#c06) |
| PRIOR-043.5 | Mathematical model lineage and empirical stopping point — Preserves the v0.2.1/FOI lineage and uncertified stopping point: sourced links, exploratory clustering and constructed sensitivity do not establish empirical equilibrium or strategic constitution. | WRITTEN | [`sub:B:04`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28); [`par:C28:case-diagnostics`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C31:07`](MATHEMATICAL_CROSSWALK.md#c31) |

**Retained review limits.** Historical reconstructions and reported statistics were not rerun here. All empirical mathematics is retained at measurement/identification level, without operational-effect claims.

## PRIOR-044

**Source:** `Hormuz_empirical_lineage`\
**Source sections:** v1.1.1 paper; nested FOI v1.2.1; legacy v1.0; hindcast/prospective records\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Do not relabel retrospective fit as prospective evidence or exploratory structural sensitivity as identified causal intervention effects.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-044.1 | State/descriptor construction and predeclared candidate ontology — Retains the event/claim/weekly-state and candidate-region ontology, tri-state episode semantics and a separately frozen state-rule protocol. | WRITTEN | [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28); [`par:C28:hormuz-repair`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-044.2 | Coverage, response matching, co-clustering and directional placebo logic — Retains the reported coverage and response-link counts and distinguishes documented links, circular-shift co-clustering and paired directional before/after evidence. | WRITTEN | [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28); [`par:C28:case-diagnostics`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-044.3 | Memory/threshold sensitivity and formal stopping point — Reports memory and effect-weight occupancy sensitivity and explains why exact duration and strict membership are measurement-dependent, with no empirical GR/PR certificate. | WRITTEN | [`par:C28:case-memory`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-044.4 | Test1 pseudo-prospective hindcast versus Test2 genuinely frozen prospective protocol — States the historical input cutoff and distinct 18:38:49Z retrospective versus 20:09:55Z prospective freezes on 12 August 2026; preserves Test 1 as hindcast and Test 2’s predeclared rule/horizon/outcome evaluation. | WRITTEN | [`par:C28:hormuz-repair`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-044.5 | v0.4 legacy versus v0.5 repaired numeric/source lineage — Records v0.4’s mistaken unevaluable-as-exit constructor and v0.5’s observed-exit/censoring correction, the 211 unchanged plus nine corrected rows, and the separated source/numeric revision status. | WRITTEN | [`par:C28:hormuz-repair`](MATHEMATICAL_CROSSWALK.md#c28) |

**Retained review limits.** The corrected historical counts and two freezes are recorded from the archived report; no future Test 2 outcome or fresh historical reanalysis is invented.

## PRIOR-045

**Source:** `Iran_January_counterfactual`\
**Source sections:** Complete v0.1.1 report and its imported version in companion\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Preserve abstract modeling and uncertainty only; a counterfactual simulation is not an observed causal estimate or operational prescription.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-045.1 | Declared counterfactual model, source timing and historical motivation — Retains the 22 August 2026 proofread revision, unchanged v0.1 calculations and retrospective source chronology, with the model described as a constructed conditional analysis. | WRITTEN | [`par:C28:january-measurement`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-045.2 | Parameter/measurement/projection assumptions — Explains qualitative rejection-sampling bands, persistent once-drawn parameters, normalized unmeasured latent coordinates and projection limits; proves the abstract clipped construction’s well-posedness. | WRITTEN | [`par:C28:january-measurement`](MATHEMATICAL_CROSSWALK.md#c28); [`eq:clipped-architecture`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`prop:clipped-wellposed`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-045.3 | Constructed simulation and identifiability status — States that accepted-draw shares and paired simulated trajectories are not empirical success probabilities or an identified posterior, and gives a general inactive-channel nonidentification result. | WRITTEN | [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28); [`par:C28:january-measurement`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:inactive-channel`](MATHEMATICAL_CROSSWALK.md#appendix-n) |

**Retained review limits.** Treatment preserves abstract recurrence/selection/identification mathematics and uncertainty, not operational prescriptions or real-world intervention optimization. Full historical model-version reconciliation is not independently certified.

## PRIOR-046

**Source:** `Breaking_Persistence_lineage`\
**Source sections:** Complete v0.2 manuscript, full companion TeX and end-to-end report\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Retain the mathematical counterexamples, constructions and identification restrictions. The historical models do not establish real-world regime certification or validate an operational intervention policy.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-046.1 | Proposition5.1 wellposed declared construction;5.2 reporting-rate nonidentification — Proves measurable invariant-cube path construction with a persistent parameter and the Poisson thinning identity identifying only the product of reporting and underlying rates. | WRITTEN | [`prop:clipped-wellposed`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`prop:poisson-thinning`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-046.2 | Proposition8.1 inactive-channel observational equivalence — Proves observational equality when the multiplier of a channel is zero on every observed trajectory, so its coefficient cannot be recovered from that observation. | WRITTEN | [`prop:inactive-channel`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-046.3 | Proposition12.1 reserve-stock first-step lag semantics — Proves geometric reserve decay under the replacement and first-step equality of the other coordinates under simultaneous old-stock timing. | WRITTEN | [`eq:reserve-abstract`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`prop:reserve-lag`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-046.4 | Proposition13.1 exact projected-path null — Proves equality of the complete relevant projected path under the null family, distinguishing structural-family changes from within-family policy changes and preserving frozen memory semantics. | WRITTEN | [`prop:projected-null`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-046.5 | Propositions14.1–14.2 killed-kernel survival/restricted exit and saved-model noninvariance — Derives killed survival/restricted exit and writes the saved model’s exact rational one-step exit witness, which refutes all-state invariance without relying on a floating-point simulation. | WRITTEN | [`thm:C04-killed`](MATHEMATICAL_CROSSWALK.md#c04); [`prop:C-Green`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`eq:exact-noninvariance`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`sub:N:04`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-046.6 | Propositions15.1–15.2 two-sided perturbation and finite-prefix comparison — Provides the two-sided baseline/treatment perturbation inequality and finite-prefix TV comparison with exact probability convention and no infinite-survival extrapolation. | WRITTEN | [`lem:C-output-errors`](MATHEMATICAL_CROSSWALK.md#appendix-c); [`thm:C13:product`](MATHEMATICAL_CROSSWALK.md#c13); [`G:fullpath`](MATHEMATICAL_CROSSWALK.md#appendix-g) |
| PRIOR-046.7 | Source chronology, model selection, observation/cohesion limits and synthetic versus empirical evidence — Retains retrospective source timing, qualitative model selection, observation/latent-state limitations, equal-follow-up correction and the difference between reproduced calculations and unrecovered simulator search history. | WRITTEN | [`par:C28:january-measurement`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:06`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:01`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`sub:N:08`](MATHEMATICAL_CROSSWALK.md#appendix-n) |
| PRIOR-046.8 | Full identified-model/outer-uncertainty interpretation and finite-sample universal-quantifier limits — Quantifies over the full admitted model family and one joint uncertainty set. A finite positive sampled minimum does not establish a universal infimum; inclusion of the projected-null model defeats the claimed positive uniform gap. | WRITTEN | [`def:identified-constitution`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:modelset-distinction`](MATHEMATICAL_CROSSWALK.md#c28); [`thm:outer-certificate`](MATHEMATICAL_CROSSWALK.md#c28); [`prop:projected-null`](MATHEMATICAL_CROSSWALK.md#appendix-n) |

**Retained review limits.** The generic constructions and all listed proposition families are written. Reproduction of simulations does not establish search-history recovery, empirical identification or universal model-set claims.

## PRIOR-047

**Source:** `cross_conflict_geometry`\
**Source sections:** Complete v0.1 workpack methods/findings/boundaries/chronology/provenance\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Archived summary reports contemporaneous mean cosine0.103, median0.026 and circular-shift p0.425; these are historical computed outputs, not independently rerun empirical conclusions here.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-047.1 | Common-grid measurement and jointly evaluable windows — Requires a common observable coordinate grid and jointly evaluable windows before cross-case comparison. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-047.2 | Directional geometry and contemporaneous/lagged cosine comparisons — Defines normalized nonzero-increment cosine, contemporaneous and lagged comparisons and an explicit zero-increment handling requirement. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-047.3 | Circular-shift null and multiplicity/lag-scan interpretation — Explains circular shifting, internal-order preservation and repeated lag selection/simultaneous correction within the null; attributes mean 0.103, median 0.026 and p=0.425 to the historical computation. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-047.4 | Source granularity and missingness restrictions — Keeps source granularity, time admission and missing-coordinate restrictions; missingness cannot be encoded as a zero increment and archived calculations are not presented as newly rerun. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:02`](MATHEMATICAL_CROSSWALK.md#c28) |

**Retained review limits.** The reported cosine/null summaries remain archived outputs, not newly executed empirical conclusions.

## PRIOR-048

**Source:** `geometry_research_programme`\
**Source sections:** All24 sections of research programme\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** These are hypotheses and proposed methods unless separately matched to completed derivations or evidence.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-048.1 | Trajectory/event-context/motif/sequence/driver definitions — Defines the five proposed objects: descriptor trajectories, event contexts, recurring local motifs, ordered motif sequences and candidate drivers requiring identification. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-048.2 | Distinguish region, regime and manifold concepts — Distinguishes a set-valued region, process-relative regime classification and a geometric manifold hypothesis requiring dimension/regularity/error evidence. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-048.3 | Data architecture, geometry and motif/driver identification — Describes the measurement/context architecture and motif/driver tests under frozen observation rules; neither geometric compactness nor naming a driver supplies causal identification. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C28:02`](MATHEMATICAL_CROSSWALK.md#c28) |
| PRIOR-048.4 | Validation nulls, workpackages and success/failure criteria — Retains proposed work on held-out motif recognition, context-matched comparisons, time/block nulls, scale/missingness sensitivity and predictive failure criteria. This is family-level methods treatment, not an independent reconciliation of all twenty-four historical sections. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:N:08`](MATHEMATICAL_CROSSWALK.md#appendix-n); [`sub:P:07`](MATHEMATICAL_CROSSWALK.md#appendix-p) |

**Retained review limits.** The five-object architecture and validation/failure programme are written; no complete section-by-section reconciliation of the twenty-four-section proposal is asserted.

## PRIOR-049

**Source:** `historical_domain_framing`\
**Source sections:** Art-of-War essay and strategic memorandum metadata/context\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** Preserve a source-level lineage record and abstract methodological relevance. Do not reproduce operational military tactics, targeting or attack prescriptions.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-049.1 | Historical framing and any abstract model assumptions — Retains historical framing of conditions of choice, generated persistence and attributed causal history at the level of abstract research questions and source lineage. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:B:04`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:C01:01`](MATHEMATICAL_CROSSWALK.md#c01) |
| PRIOR-049.2 | Separate interpretive claims from mathematical theorems and identified evidence — Separates interpretive essays from transition laws, proofs and identified evidence; includes no tactical targeting or operational attack guidance. | WRITTEN | [`sub:C28:07`](MATHEMATICAL_CROSSWALK.md#c28); [`sub:C31:07`](MATHEMATICAL_CROSSWALK.md#c31) |

**Retained review limits.** Historical domain texts are retained as source-level abstract motivation; operational tactics are outside this manuscript treatment.

## PRIOR-050

**Source:** `mathematical_reference_guide_editions`\
**Source sections:** Every A–F draft/compilation; v0.9/.9.1/.9.2/v1.0/v1.1/v1.1.1; exact renders\
**Obligation disposition:** Required historical reconciliation incomplete.

**Original scope boundary.** Byte-identical artifacts may share one record; matching title, version label or PDF/Markdown pairing does not by itself establish semantic identity.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-050.1 | Each edition’s unique explanation, hypotheses, examples, claim corrections and source crosswalk — Written theory integrates the guide’s mathematical families and records content/version distinctions, but this edition does not yet list and reconcile every unique explanation, hypothesis and example across all A–F drafts and guide editions. | RECONCILIATION_INCOMPLETE | [`sub:B:03`](MATHEMATICAL_CROSSWALK.md#appendix-b); [`sub:C30:01`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C30:03`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:O:02`](MATHEMATICAL_CROSSWALK.md#appendix-o) |
| PRIOR-050.2 | Section-level delta reconciliation against latest v1.1.1 and current source — Explicitly requires separate records for changed versions and identifies exact-byte aliases; a complete section-level delta map against v1.1.1 and current source is still a required review deliverable. | RECONCILIATION_INCOMPLETE | [`sub:C30:01`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:C30:03`](MATHEMATICAL_CROSSWALK.md#c30); [`sub:O:02`](MATHEMATICAL_CROSSWALK.md#appendix-o); [`sub:P:07`](MATHEMATICAL_CROSSWALK.md#appendix-p) |
| PRIOR-050.3 | All positive/negative scope qualifications and completed versus pending changes — Writes current positive/negative scope qualifications and specific residual criteria, but does not certify that every edition-specific completed/pending correction has received an independent historical unique-clause reconciliation. | RECONCILIATION_INCOMPLETE | [`sub:C31:06`](MATHEMATICAL_CROSSWALK.md#c31); [`sub:P:01`](MATHEMATICAL_CROSSWALK.md#appendix-p); [`sub:C29:05`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C30:02`](MATHEMATICAL_CROSSWALK.md#c30) |

**Retained review limits.** Required full unique-clause and section-delta reconciliation across A–F drafts and v0.9/v0.9.1/v0.9.2/v1.0/v1.1/v1.1.1 remains incomplete. Current mathematical chapter coverage is not a substitute for that historical review.

## PRIOR-051

**Source:** `application_upgrade_and_build`\
**Source sections:** Upgrade report, file specification and source-linked mathematical workorders\
**Obligation disposition:** Substantive written family treatment.

**Original scope boundary.** An upgrade plan or manifest is evidence of a requirement, not evidence of an implemented theorem or empirical result.

| Requirement | Required content and written treatment | Status | Current manuscript labels |
|---|---|---|---|
| PRIOR-051.1 | Retain mathematical application requirements and comparison assumptions — Retains actual application input/comparison contracts, all twenty-six numerical profile bounds, native C10/C11 literal-instance restrictions and the role of prior workorders as requirements. Complete workorder-by-workorder semantic equivalence is not asserted. | WRITTEN | [`sub:C29:01`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C29:03`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C29:04`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C29:05`](MATHEMATICAL_CROSSWALK.md#c29) |
| PRIOR-051.2 | Keep candidate workorders separate from implemented/compiled/accepted claims — Separates candidate text and proposed profiles from implemented, numerically checked, Lean-compiled, released and independently accepted results; a manifest or upgrade plan alone supplies none of those stronger evidence claims. | WRITTEN | [`def:receipt-contract`](MATHEMATICAL_CROSSWALK.md#c29); [`prop:reflection-chain`](MATHEMATICAL_CROSSWALK.md#c29); [`sub:C29:05`](MATHEMATICAL_CROSSWALK.md#c29); [`def:evidence-coordinates`](MATHEMATICAL_CROSSWALK.md#c30) |

**Retained review limits.** All actual current profile contracts are presented, but this written-family map is not a full source-linked workorder/draft implementation audit.

## Completion criterion

An independent historical reconciliation must identify each original substantive claim, every changed hypothesis, example, correction and evidence status, and its actual preservation or correction destination. It must review the differences, not simply count current chapter coverage. The original JSON retains `independent_complete_historical_unique_clause_reconciliation: false` and the per-obligation completion-gate fields. This page preserves those meanings.

The manuscript review supplies concrete written treatments and a checkable index. It does not issue a new empirical certificate for the historical case studies, change the source chronology, infer an identified model from a simulation, or turn an interpretive essay into a theorem. For evidence and acceptance distinctions see [verification](VERIFICATION.md) and [residual status](RESIDUAL_STATUS.md).
