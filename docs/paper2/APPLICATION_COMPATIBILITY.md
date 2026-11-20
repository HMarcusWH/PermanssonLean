# Paper v2.0.1 and application compatibility

[Current documentation](README.md) · [Reviewed manuscript](../../paper2/README.md) · [Current residual status](RESIDUAL_STATUS.md)

This is the authoritative **paper-to-application reading map** for the reviewed
manuscript v2.0.1. The application contracts remain defined by their actual
registry, parsers, checkers and source-bound proof interfaces. A route to a paper
section is an editorial connection; it does not by itself establish equivalence
between every manuscript statement and a generated instance theorem.

The mapping is based on the mathematical source `c5a36cd6189e2a249d5f4bc11f31698917dc8b10`
and documentation snapshot `f0dee1c11a20f96c9a11b380e942b9252e6ebe44`, reviewed on
20 November 2026. The paper describes the input and receipt contract in §29.1–29.2,
all 26 numeric profiles in §29.3, native C10/C11 replay in §29.4, and legacy/release
boundaries in §29.5. These correspond to labels `sub:C29:01` through `sub:C29:05` in
the [reviewed label index](../../paper2/v2.0.1/indices/manuscript_label_index.json).

## Three application routes

| Route | What it does | Evidence boundary |
| --- | --- | --- |
| Historical Application Standard v0.1.0 | Validates the structure of a declared application packet; available through the successor's read-only `legacy-validate` wrapper | Structural contract validation; the historical schemas and validator are unchanged |
| Successor application v0.2.0 | Computes 26 bounded exact-rational profiles, independently checks receipts, and can emit/recheck source-bound Lean candidates | Numeric output, source binding, compiler replay, independent certification and empirical identification are separate |
| Native C10 v0.1.0 / C11 v0.2.0 | Run their distinct supported numeric routes or explicitly invoke pinned Lean replay on reified inputs | Native replay is outside the published 26-profile numeric release scope; each CLI retains its own source and input contract |

The successor numeric release is `permansson-app-v0.2.0` from
`63a66c82a9ece4361f646ee13b6711192f831406`, released on 1 November 2026 for Linux
CPython 3.12/3.13. The new manuscript and these reading links do not rebuild that
wheel, change its version or alter its accepted release bytes. Current checkout
documentation can therefore contain this map even though the previously released
distribution predates it. See the preserved
[release acceptance record](../../apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md)
and [version lineage](VERSION_LINEAGE.md).

## All 26 exact profiles

The table joins the literal registry identifiers to commands, independent checkers,
candidate families and paper destinations. A checker name is a Python symbol,
except `receipts.lp`, which denotes the consumer-side LP verification module.
The `permansson_app.` prefix is omitted from checker names for readability.
Lean reflection limits can be smaller than the numeric profile's limits; both
are stated separately below.

| Registered profile | CLI command | Independent checker | Lean candidate family | Paper route |
| --- | --- | --- | --- | --- |
| `finite.adaptive_block_control.numeric.v1` | `finite-adaptive-grammar` | `receipts.adaptive.check_adaptive` | [`adaptive`](../../apps/permansson/application-successor/docs/ADAPTIVE_LEAN_BRIDGE.md) | [§11](MATHEMATICAL_CROSSWALK.md#c11), [§17](MATHEMATICAL_CROSSWALK.md#c17), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j) |
| `finite.almost_sure_safety_core.numeric.v1` | `finite-safety` | `receipts.safety.check_safety_core` | [`safety-core`](../../apps/permansson/application-successor/docs/SAFETY_CORE_LEAN_BRIDGE.md) | [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j) |
| `finite.alpha_P_U.induced_kernel.numeric.v1` | `finite-kernel` | `receipts.finite_world.check_finite_receipt` | [`finite-world`](../../apps/permansson/application-successor/docs/FINITE_WORLD_LEAN_REIFICATION_V1.md) | [§3](MATHEMATICAL_CROSSWALK.md#c03), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.cq1_certificate_transport.numeric.v1` | `finite-cq1-transport` | `receipts.cq1_transport.check_cq1_transport` | [`cq1-transport`](../../apps/permansson/application-successor/docs/CQ1_TRANSPORT_LEAN_BRIDGE.md) | [§12](MATHEMATICAL_CROSSWALK.md#c12), [§13](MATHEMATICAL_CROSSWALK.md#c13), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f), [Appendix G](MATHEMATICAL_CROSSWALK.md#appendix-g) |
| `finite.cq1_constitutive_certificate.numeric.v1` | `finite-cq1` | `receipts.cq1.check_cq1` | [`cq1`](../../apps/permansson/application-successor/docs/CQ1_LEAN_BRIDGE.md) | [§12](MATHEMATICAL_CROSSWALK.md#c12), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f) |
| `finite.first_exit_and_survival.numeric.v1` | `finite-exit` | `receipts.exit.check_exit` | [`exit`](../../apps/permansson/application-successor/docs/EXIT_LEAN_BRIDGE.md) | [§10](MATHEMATICAL_CROSSWALK.md#c10), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix D](MATHEMATICAL_CROSSWALK.md#appendix-d), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.frozen_menu.numeric.v1` | `frozen-menu` | `receipts.menu.check_menu` | [`menu`](../../apps/permansson/application-successor/docs/MENU_LEAN_BRIDGE.md) | [§17](MATHEMATICAL_CROSSWALK.md#c17), [§20](MATHEMATICAL_CROSSWALK.md#c20), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.hitting_bellman.numeric.v1` | `finite-bellman` | `receipts.control.check_bellman` | [`control-table`](../../apps/permansson/application-successor/docs/CONTROL_TABLE_LEAN_BRIDGE.md) | [§17](MATHEMATICAL_CROSSWALK.md#c17), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.killed_kernel.survival.numeric.v1` | `finite-survival` | `receipts.finite_survival.check_survival_receipt` | [`survival`](../../apps/permansson/application-successor/docs/MENU_LEAN_BRIDGE.md) | [§4](MATHEMATICAL_CROSSWALK.md#c04), [§12](MATHEMATICAL_CROSSWALK.md#c12), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.metric_contraction_perturbation.numeric.v1` | `finite-metric` | `receipts.metric.check_metric` | [`metric`](../../apps/permansson/application-successor/docs/METRIC_LEAN_BRIDGE.md) | [§14](MATHEMATICAL_CROSSWALK.md#c14), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix H](MATHEMATICAL_CROSSWALK.md#appendix-h) |
| `finite.nonlinear_classwise_stationary.numeric.v1` | `nonlinear-stationary` | `receipts.nonlinear.check_nonlinear` | [`nonlinear`](../../apps/permansson/application-successor/docs/NONLINEAR_LEAN_BRIDGE.md) | [§21](MATHEMATICAL_CROSSWALK.md#c21), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.observation_history_tree.numeric.v1` | `finite-belief-tree` | `receipts.belief_tree.check_belief_tree` | [`belief`](../../apps/permansson/application-successor/docs/BELIEF_LEAN_BRIDGE.md) | [§18](MATHEMATICAL_CROSSWALK.md#c18), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j) |
| `finite.one_step_observation_belief.numeric.v1` | `one-step-belief` | `receipts.belief.check_belief` | [`belief`](../../apps/permansson/application-successor/docs/BELIEF_LEAN_BRIDGE.md) | [§18](MATHEMATICAL_CROSSWALK.md#c18), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j) |
| `finite.one_step_risk_infeasibility.numeric.v1` | `one-step-risk-infeasibility` | `receipts.risk_infeasibility.check_risk_infeasibility` | [`risk-infeasibility`](../../apps/permansson/application-successor/docs/RISK_INFEASIBILITY_LEAN_BRIDGE.md) | [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.one_step_risk_occupancy.numeric.v1` | `one-step-risk` | `receipts.risk_occupancy.check_risk` | [`flow`](../../apps/permansson/application-successor/docs/FLOW_LEAN_BRIDGE.md) | [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.patch_grammar.numeric.v1` | `finite-grammar` | `receipts.grammar.check_grammar` | [`grammar`](../../apps/permansson/application-successor/docs/GRAMMAR_LEAN_BRIDGE.md) | [§11](MATHEMATICAL_CROSSWALK.md#c11), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f) |
| `finite.path_perturbation_tv.numeric.v1` | `finite-perturbation` | `receipts.robustness.check_perturbation` | [`perturbation`](../../apps/permansson/application-successor/docs/PERTURBATION_LEAN_BRIDGE.md) | [§13](MATHEMATICAL_CROSSWALK.md#c13), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix G](MATHEMATICAL_CROSSWALK.md#appendix-g) |
| `finite.private_control_stage_saddle.numeric.v1` | `finite-private-stage` | `receipts.private_stage.check_private_stage` | [`private-stage`](../../apps/permansson/application-successor/docs/PRIVATE_STAGE_LEAN_BRIDGE.md) | [§22](MATHEMATICAL_CROSSWALK.md#c22), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix L](MATHEMATICAL_CROSSWALK.md#appendix-l) |
| `finite.random_occupation.numeric.v1` | `finite-occupation` | `receipts.occupation.check_occupation` | [`occupation`](../../apps/permansson/application-successor/docs/OCCUPATION_LEAN_BRIDGE.md) | [§7](MATHEMATICAL_CROSSWALK.md#c07), [§20](MATHEMATICAL_CROSSWALK.md#c20), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix D](MATHEMATICAL_CROSSWALK.md#appendix-d), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `finite.rational_algebra_witness.numeric.v1` | `finite-algebra` | `receipts.algebra.check_algebra` | [`algebra`](../../apps/permansson/application-successor/docs/ALGEBRA_LEAN_BRIDGE.md) | [§26](MATHEMATICAL_CROSSWALK.md#c26), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix M](MATHEMATICAL_CROSSWALK.md#appendix-m) |
| `finite.rectangular_vs_committed_nature.numeric.v1` | `finite-robust-nature` | `receipts.robust_nature.check_nature` | [`robust-nature`](../../apps/permansson/application-successor/docs/ROBUST_LEAN_BRIDGE.md) | [§22](MATHEMATICAL_CROSSWALK.md#c22), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix L](MATHEMATICAL_CROSSWALK.md#appendix-l) |
| `finite.residence_monitor.numeric.v1` | `finite-residence` | `receipts.residence.check_residence` | [`residence`](../../apps/permansson/application-successor/docs/RESIDENCE_LEAN_BRIDGE.md) | [§17](MATHEMATICAL_CROSSWALK.md#c17), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j) |
| `finite.two_player_protocol.numeric.v1` | `finite-multiagent` | `receipts.multiagent.check_multiagent` | [`multiagent`](../../apps/permansson/application-successor/docs/MULTIAGENT_LEAN_BRIDGE.md) | [§24](MATHEMATICAL_CROSSWALK.md#c24), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix L](MATHEMATICAL_CROSSWALK.md#appendix-l) |
| `finite.typed_quotient.numeric.v1` | `finite-quotient` | `receipts.quotients.check_quotient` | [`quotient`](../../apps/permansson/application-successor/docs/QUOTIENT_LEAN_BRIDGE.md) | [§16](MATHEMATICAL_CROSSWALK.md#c16), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix I](MATHEMATICAL_CROSSWALK.md#appendix-i) |
| `lp.exact_rational.independent_verification.v1` | `lp-check` | `receipts.lp` | [`lp`](../../apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md) | [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |
| `lp.exact_rational.optimality.numeric.v1` | `lp-propose` | `receipts.lp.check_lp_certificate` | [`lp`](../../apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md) | [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k) |

Source authorities: the [numeric registry](../../apps/permansson/application-successor/src/permansson_app/data/capabilities.json),
[capability table](../../apps/permansson/application-successor/docs/CAPABILITY_SCOPES.md),
[candidate family registry](../../apps/permansson/application-successor/src/permansson_app/proof/lean_candidates.py)
and [source-bound bridge status](../../apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md).
All 26 identifiers are represented exactly once in the table. The following
scope paragraphs use the same registry snapshot; future implementation changes
need a newly dated source comparison.

## Numeric and reflected-instance scopes

The **numeric scope** text below is the registry's literal scope string at the
pinned snapshot. Phrases about absent Lean claims describe what the numeric
command's receipt asserts. The associated source-bound candidate families are
implemented separately, as the family column and reflection scope show.
The **reflection scope** is taken from the documented bridge interface; it
describes supported instances, not a theorem over all JSON requests or an
empirically identified mechanism. The bridge documents give the detailed
premises and mutation checks. No fresh compiler run is asserted by this map.

### `finite-adaptive-grammar`

**Profile:** `finite.adaptive_block_control.numeric.v1`. **Paper:** [§11](MATHEMATICAL_CROSSWALK.md#c11), [§17](MATHEMATICAL_CROSSWALK.md#c17), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j).

**Numeric scope:** Exact adaptive control over the declared admitted blocks of a finite patch grammar (at most 8 blocks, 12 joint states, 8 transitions): before every alpha/P/U stage the controller selects one whole admitted block and its history may select a different one next time; P is never changed. The exact Bellman table over (joint state, still-inside flag) gives the survival or exit optimum over every full-history behavioral block controller, with tied optimal blocks, every frozen block value and the adaptivity gain. No downward closure, unadmitted joint block, overlap-model certificate, Lean or empirical identification claim.

**Reflection scope:** at most 8 blocks, horizon ≤ 6 for Lean; no frozen-block comparison, overlap-model certificate, downward closure or empirical identification. The corresponding module is `AdaptiveBlockReceipt`; see the [`adaptive` bridge](../../apps/permansson/application-successor/docs/ADAPTIVE_LEAN_BRIDGE.md).

### `finite-safety`

**Profile:** `finite.almost_sure_safety_core.numeric.v1`. **Paper:** [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j).

**Numeric scope:** Finite rational greatest almost-sure controlled invariant core <=12 joint states; not survival probability outside core; no Lean or empirical GR/PR qualification

**Reflection scope:** ≤2 per dimension. The corresponding module is `SafetyReceipt`; see the [`safety-core` bridge](../../apps/permansson/application-successor/docs/SAFETY_CORE_LEAN_BRIDGE.md).

### `finite-kernel`

**Profile:** `finite.alpha_P_U.induced_kernel.numeric.v1`. **Paper:** [§3](MATHEMATICAL_CROSSWALK.md#c03), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Finite exact rational alpha/P/U model; held-fixed/causal identification not inferred

**Reflection scope:** ≤2 per dimension. The corresponding module is `FiniteWorldInput`; see the [`finite-world` bridge](../../apps/permansson/application-successor/docs/FINITE_WORLD_LEAN_REIFICATION_V1.md).

### `finite-cq1-transport`

**Profile:** `finite.cq1_certificate_transport.numeric.v1`. **Paper:** [§12](MATHEMATICAL_CROSSWALK.md#c12), [§13](MATHEMATICAL_CROSSWALK.md#c13), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f), [Appendix G](MATHEMATICAL_CROSSWALK.md#appendix-g).

**Numeric scope:** Exact transport of a finite CQ-1 certificate to a declared approximate baseline/treated pair sharing the states, feasible actions and P: one-step budgets are the exact maximal row total variations between the certified and approximate induced kernels, the geometric envelopes 1-(1-delta)^L give the transported persistence error min(1, eta+e0) and margin kappa-e0-eJ (transported only when positive), and the approximate pair's own exact values are reported as a consistency check. Budgets are exact distances between declared models, not empirical error estimates; no Exact GR/PR, QSD, Lean or empirical identification claim.

**Reflection scope:** horizon ≤ 6 for Lean, joint states ≤ 12; budgets are exact model distances, not empirical errors; no Exact GR/PR or QSD. The corresponding module is `CQ1TransportReceipt`; see the [`cq1-transport` bridge](../../apps/permansson/application-successor/docs/CQ1_TRANSPORT_LEAN_BRIDGE.md).

### `finite-cq1`

**Profile:** `finite.cq1_constitutive_certificate.numeric.v1`. **Paper:** [§12](MATHEMATICAL_CROSSWALK.md#c12), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f).

**Numeric scope:** Exact finite CQ-1 certificate for one declared alpha/U intervention with P and feasibility held fixed: killed survival in the region from every region state (finite persistence gate), prefix survival in a property set under both models on a comparison set of at least two states, and the uniform margin. <=12 joint states, horizon <=16. No error-budget transport, Exact GR/PR, QSD, Lean or empirical identification claim.

**Reflection scope:** ≤2 per dimension, horizon 0..6; prefix-survival property only; no error-budget transport, Exact GR/PR or QSD. The corresponding module is `FiniteScoreReceipt`; see the [`cq1` bridge](../../apps/permansson/application-successor/docs/CQ1_LEAN_BRIDGE.md).

### `finite-exit`

**Profile:** `finite.first_exit_and_survival.numeric.v1`. **Paper:** [§10](MATHEMATICAL_CROSSWALK.md#c10), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix D](MATHEMATICAL_CROSSWALK.md#appendix-d), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Finite region first-exit destination subprobability and never-exit mass; never normalize away nonexit

**Reflection scope:** ≤2 per dimension, horizon 0..6; no restart law, switch retention or GR/PR. The corresponding module is `ExitReceipt`; see the [`exit` bridge](../../apps/permansson/application-successor/docs/EXIT_LEAN_BRIDGE.md).

### `frozen-menu`

**Profile:** `finite.frozen_menu.numeric.v1`. **Paper:** [§17](MATHEMATICAL_CROSSWALK.md#c17), [§20](MATHEMATICAL_CROSSWALK.md#c20), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Exact finite-horizon objective over 1..8 fully enumerated declared interventions; includes all tied optimizers, not the universe of controls

**Reflection scope:** ≤2 per dimension, ≤4 members, 1..6 transitions; optimality over the declared menu only. The corresponding module is `MenuReceipt`; see the [`menu` bridge](../../apps/permansson/application-successor/docs/MENU_LEAN_BRIDGE.md).

### `finite-bellman`

**Profile:** `finite.hitting_bellman.numeric.v1`. **Paper:** [§17](MATHEMATICAL_CROSSWALK.md#c17), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Finite <=12-state <=24-step fully observed rational hitting Bellman; deterministic remaining-horizon Markov; P/U held fixed; no Lean or GR/PR certification

**Reflection scope:** ≤2 per dimension, 1..6 transitions. The corresponding module is `ControlTableReceipt`; see the [`control-table` bridge](../../apps/permansson/application-successor/docs/CONTROL_TABLE_LEAN_BRIDGE.md).

### `finite-survival`

**Profile:** `finite.killed_kernel.survival.numeric.v1`. **Paper:** [§4](MATHEMATICAL_CROSSWALK.md#c04), [§12](MATHEMATICAL_CROSSWALK.md#c12), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Finite horizon 0..32; <=12 joint states, full declared region and comparison set; not Exact GR/PR

**Reflection scope:** ≤2 per dimension, 1..6 transitions; finite-horizon diagnostic only. The corresponding module is `MenuReceipt` (survival tables); see the [`survival` bridge](../../apps/permansson/application-successor/docs/MENU_LEAN_BRIDGE.md).

### `finite-metric`

**Profile:** `finite.metric_contraction_perturbation.numeric.v1`. **Paper:** [§14](MATHEMATICAL_CROSSWALK.md#c14), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix H](MATHEMATICAL_CROSSWALK.md#appendix-h).

**Numeric scope:** Exact finite W1 transport on a declared metric over <=4 joint states: every baseline row-pair distance with an optimal coupling and an attaining 1-Lipschitz potential, contraction factor, per-row defects against a perturbed alpha/P/U model, unique invariant laws, their exact distance and the A3 bound delta/(1-rho) only under strict contraction. No Polish-space moment argument, Lean or empirical identification claim.

**Reflection scope:** ≤2 per dimension (≤4 joint states); strict contraction only; no Polish-space moment argument, occupation-margin transport or empirical metric. The corresponding module is `MetricReceipt`; see the [`metric` bridge](../../apps/permansson/application-successor/docs/METRIC_LEAN_BRIDGE.md).

### `nonlinear-stationary`

**Profile:** `finite.nonlinear_classwise_stationary.numeric.v1`. **Paper:** [§21](MATHEMATICAL_CROSSWALK.md#c21), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** All feasible deterministic stationary policies, <=8 finite joint states and <=64 policies, Boolean F(p)=1-|p-2/3| applied to each recurrent-class law before expectation; numeric only

**Reflection scope:** ≤2 per dimension, ≤16 policies; no randomized or history-dependent policies. The corresponding module is `NonlinearReceipt`; see the [`nonlinear` bridge](../../apps/permansson/application-successor/docs/NONLINEAR_LEAN_BRIDGE.md).

### `finite-belief-tree`

**Profile:** `finite.observation_history_tree.numeric.v1`. **Paper:** [§18](MATHEMATICAL_CROSSWALK.md#c18), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j).

**Numeric scope:** One to three transitions; <=2 strategic and <=3 hidden world states, <=3 observations/actions. Observation before action at each stage, P then U; exhaustive bounded finite observation-history deterministic policy class with exact Bayesian joint-state beliefs, common hidden-support feasibility and independent unnormalized-flow/replayed-path verification. No general POMDP, Lean replay or empirical GR/PR identification.

**Reflection scope:** ≤2 per dimension, ≤3 observations, horizon 1..3; no posterior/score restatement, hidden-state controllers or empirical observation model. The corresponding module is `BeliefTreeReceipt`; see the [`belief` bridge](../../apps/permansson/application-successor/docs/BELIEF_LEAN_BRIDGE.md).

### `one-step-belief`

**Profile:** `finite.one_step_observation_belief.numeric.v1`. **Paper:** [§18](MATHEMATICAL_CROSSWALK.md#c18), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j).

**Numeric scope:** One-transition, one strategic state, 1..3 hidden world states, observations and actions. Exact observation likelihoods and Bayesian posterior where reachable; one action shared across all hidden states in each observation support; bounded complete deterministic observation-policy enumeration. Unreachable observation never normalized. No multistage POMDP, independent Lean proof, empirical identification or GR/PR status.

**Reflection scope:** ≤2 per dimension, ≤3 observations, horizon 1..3; no posterior/score restatement, hidden-state controllers or empirical observation model. The corresponding module is `BeliefTreeReceipt`; see the [`belief` bridge](../../apps/permansson/application-successor/docs/BELIEF_LEAN_BRIDGE.md).

### `one-step-risk-infeasibility`

**Profile:** `finite.one_step_risk_infeasibility.numeric.v1`. **Paper:** [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Exact Farkas certificate that the one-step risk cap of a one-step-risk request cannot be met: per-state floors (the least next-step risk over the declared feasible actions of the actual P.U rows), every attaining action, the least risk mass of any fully observed randomized policy from the initial law, and its shortfall over the cap. Refuses when a policy meets the cap. One transition only; no multi-stage, private-information, Lean or empirical identification claim.

**Reflection scope:** one transition, at most 4 joint states and 5 occupancy variables; no multi-stage occupancy, private information or empirical identification. The corresponding module is `FlowInfeasibilityReceipt`; see the [`risk-infeasibility` bridge](../../apps/permansson/application-successor/docs/RISK_INFEASIBILITY_LEAN_BRIDGE.md).

### `one-step-risk`

**Profile:** `finite.one_step_risk_occupancy.numeric.v1`. **Paper:** [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** One-transition, fully observed, finite, exact rational randomized state-feedback optimum from a declared initial law, complete feasible action sets, and risk event; independent primal/dual LP certificate and actual P/U law reconstruction. At most four joint states and five occupancy variables. No multistage, private-information, unbounded-policy, Lean or empirical identification claim.

**Reflection scope:** ≤2 per dimension; one transition only; no Farkas route, multi-stage, robust or private-information claim. The corresponding module is `FlowReceipt`; see the [`flow` bridge](../../apps/permansson/application-successor/docs/FLOW_LEAN_BRIDGE.md).

### `finite-grammar`

**Profile:** `finite.patch_grammar.numeric.v1`. **Paper:** [§11](MATHEMATICAL_CROSSWALK.md#c11), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix F](MATHEMATICAL_CROSSWALK.md#appendix-f).

**Numeric scope:** Exact finite alpha/U explicitly admitted block grammar and per-comparison finite survival/exit effects, all inclusion-minimal positive admitted blocks, four-corner interactions. Not a PR certificate.

**Reflection scope:** ≤2 per dimension, ≤8 blocks, horizon 0..6; no downward closure, constitutive or PR certificate. The corresponding module is `GrammarReceipt`; see the [`grammar` bridge](../../apps/permansson/application-successor/docs/GRAMMAR_LEAN_BRIDGE.md).

### `finite-perturbation`

**Profile:** `finite.path_perturbation_tv.numeric.v1`. **Paper:** [§13](MATHEMATICAL_CROSSWALK.md#c13), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix G](MATHEMATICAL_CROSSWALK.md#appendix-g).

**Numeric scope:** Exact finite-horizon path event survival and TV coupling bound, <=12 states, horizon <=32; never long-run GR/PR or causal identity

**Reflection scope:** ≤2 per dimension, horizon 0..6; finite horizon only, no history budgets or original margins. The corresponding module is `QuantitativeReceipt`; see the [`perturbation` bridge](../../apps/permansson/application-successor/docs/PERTURBATION_LEAN_BRIDGE.md).

### `finite-private-stage`

**Profile:** `finite.private_control_stage_saddle.numeric.v1`. **Paper:** [§22](MATHEMATICAL_CROSSWALK.md#c22), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix L](MATHEMATICAL_CROSSWALK.md#appendix-l).

**Numeric scope:** Exact one-stage private-control robust value: nature sees the controller's mixed strategy but not the realized control (at most 4 controls and 4 nature parameters, payoffs of any sign). Exhaustive exact vertex enumeration of both programs returns an optimal rational controller mixture and a nature mixture forming a two-sided saddle certificate; the pure-control (revealed-control) value and the randomization gain are reported. No multi-stage private game, committed nature, learning, Lean or empirical identification claim.

**Reflection scope:** one stage, at most 4 controls and 4 parameters; no multi-stage private games, committed nature, learning or empirical identification. The corresponding module is `PrivateStageReceipt`; see the [`private-stage` bridge](../../apps/permansson/application-successor/docs/PRIVATE_STAGE_LEAN_BRIDGE.md).

### `finite-occupation`

**Profile:** `finite.random_occupation.numeric.v1`. **Paper:** [§7](MATHEMATICAL_CROSSWALK.md#c07), [§20](MATHEMATICAL_CROSSWALK.md#c20), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix D](MATHEMATICAL_CROSSWALK.md#appendix-d), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Finite rational multichain bottom classes, absorption and random limiting occupation; not empirical GR/PR

**Reflection scope:** ≤2 per dimension; no GR/PR recovery or original-margin corollary. The corresponding module is `OccupationReceipt`; see the [`occupation` bridge](../../apps/permansson/application-successor/docs/OCCUPATION_LEAN_BRIDGE.md).

### `finite-algebra`

**Profile:** `finite.rational_algebra_witness.numeric.v1`. **Paper:** [§26](MATHEMATICAL_CROSSWALK.md#c26), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix M](MATHEMATICAL_CROSSWALK.md#appendix-m).

**Numeric scope:** Exact rational witnesses for four specialized real-algebra profiles on <=4-dimensional matrices and vectors: seam equations and common mode, an LDL positive-semidefinite witness with the shell Schur complement, singular compatibility (preimage gap or incompatible kernel vector), and the Gram gap, witness and perturbation threshold. Feature or operator identification with a strategic source is an explicit unmet premise; no Lean or empirical identification claim.

**Reflection scope:** dimension ≤ 4 (shell ≤ 3); feature or operator identification with a strategic source is an explicit unmet premise. The corresponding module is `RationalAlgebraReceipt`; see the [`algebra` bridge](../../apps/permansson/application-successor/docs/ALGEBRA_LEAN_BRIDGE.md).

### `finite-robust-nature`

**Profile:** `finite.rectangular_vs_committed_nature.numeric.v1`. **Paper:** [§22](MATHEMATICAL_CROSSWALK.md#c22), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix L](MATHEMATICAL_CROSSWALK.md#appendix-l).

**Numeric scope:** Finite rational max-min rectangular nature chooses a complete physical P row after each observed control; fixed deterministic Markov policy compared with one whole P model committed at t=0. Fully observed <=12 joint states, <=6 nature models, <=12 transitions. No committed-controller optimum or private-information claim; no Lean or empirical identification.

**Reflection scope:** ≤2 per dimension, horizon 0..6; no committed-game or private-stage optimality. The corresponding module is `RobustReceipt`; see the [`robust-nature` bridge](../../apps/permansson/application-successor/docs/ROBUST_LEAN_BRIDGE.md).

### `finite-residence`

**Profile:** `finite.residence_monitor.numeric.v1`. **Paper:** [§17](MATHEMATICAL_CROSSWALK.md#c17), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix J](MATHEMATICAL_CROSSWALK.md#appendix-j).

**Numeric scope:** Fully observed <=8-state finite Bellman over explicit first-entry/retryable/avoid monitors, deadlines <=8 and dwell <=4; numeric only; no through-horizon risk certificate

**Reflection scope:** ≤2 per dimension, 1..6 transitions. The corresponding module is `ResidenceReceipt`; see the [`residence` bridge](../../apps/permansson/application-successor/docs/RESIDENCE_LEAN_BRIDGE.md).

### `finite-multiagent`

**Profile:** `finite.two_player_protocol.numeric.v1`. **Paper:** [§24](MATHEMATICAL_CROSSWALK.md#c24), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix L](MATHEMATICAL_CROSSWALK.md#appendix-l).

**Numeric scope:** Exact finite two-player protocol with product actions: per-player action and private-update tables, a common update and physical P (each dimension <=2, both players with the same private-state and action counts); baseline, closed-loop (treated player's mechanism replaced) and open-loop (declared anchor profile, then the replacement) joint kernels and their row total variation. P is never changed. No asymmetric types, mediated or correlated actions, private clocks, Lean or empirical game identification claim.

**Reflection scope:** each dimension ≤ 2, symmetric player state/action counts; no asymmetric types, mediated or correlated actions, private clocks or empirical game identification. The corresponding module is `MultiAgentReceipt`; see the [`multiagent` bridge](../../apps/permansson/application-successor/docs/MULTIAGENT_LEAN_BRIDGE.md).

### `finite-quotient`

**Profile:** `finite.typed_quotient.numeric.v1`. **Paper:** [§16](MATHEMATICAL_CROSSWALK.md#c16), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix I](MATHEMATICAL_CROSSWALK.md#appendix-i).

**Numeric scope:** Exactly strongly lumpable typed strategic/world coordinate projection for baseline and each frozen alpha/U intervention, complete fibers and finite horizon survival/exit transport. Does not construct coarse alpha/P/U or certify Exact GR/PR.

**Reflection scope:** ≤2 per dimension, ≤4 profiles, horizon 0..6; no coarse α/P/U, Q1–Q3 domination or original margins. The corresponding module is `QuotientReceipt`; see the [`quotient` bridge](../../apps/permansson/application-successor/docs/QUOTIENT_LEAN_BRIDGE.md).

### `lp-check`

**Profile:** `lp.exact_rational.independent_verification.v1`. **Paper:** [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Consumer-side exact rational primal/dual optimum or Farkas infeasibility; no provider equality

**Reflection scope:** ≤3 variables, ≤6 normalized constraints. The corresponding module is `LinearProgramReceipt`; see the [`lp` bridge](../../apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md).

### `lp-propose`

**Profile:** `lp.exact_rational.optimality.numeric.v1`. **Paper:** [§19](MATHEMATICAL_CROSSWALK.md#c19), [§29](MATHEMATICAL_CROSSWALK.md#c29), [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

**Numeric scope:** Bounded exact rational <=6-variable LP; failure to locate a certificate never means infeasible

**Reflection scope:** ≤3 variables, ≤6 normalized constraints. The corresponding module is `LinearProgramReceipt`; see the [`lp` bridge](../../apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md).

## Native C10 and C11

Read manuscript **§29.4, “Native C10 and C11 replay”** (`sub:C29:04`; printed page
114, PDF page 124), together with the algorithms and original-semantic recovery in
[§20](MATHEMATICAL_CROSSWALK.md#c20), the source-evidence discussion in
[§29](MATHEMATICAL_CROSSWALK.md#c29), and [Appendix K](MATHEMATICAL_CROSSWALK.md#appendix-k).

| Route | Supported input | What genuine replay establishes | Preserved boundary |
| --- | --- | --- | --- |
| [C10 CLI v0.1.0](../../apps/permansson/closure-successor/README.md) / `c10.fixed_six_state.numeric.v1` | The frozen six-state model, ordered menu `full, half, tiny, identity, u-only, b-only`, and complete comparison starts `[1,2]` | Literal six-state equality, the named comparison margins, selected optimum/ties and original global finite-menu maximum through the generated bridge and pinned compiler/axiom checks | Arbitrary finite matrices are unsupported; the existing `VERSION.json` still says `DRAFT__COMPILER_CI_PENDING` and is not reconciled by a paper link |
| [C11 CLI v0.2.0](../../apps/permansson/closure-successor-c11/README.md) / `c11.stationary_1_to_6.numeric.v1` | A supported rational stochastic matrix on 1–6 states and Boolean descriptor, including periodic/multichain examples | The reified complete stationary family, literal balance equations and descriptor shares | The underlying producer's larger domain does not enlarge the native CLI bound; this is not an external strategic-mechanism or empirical PR certificate |

Both native replay modes require a genuine clean repository, pinned providers and
toolchain, strict bounded input and a fresh output directory outside the source
tree. Their numeric modes do not invoke Lean. Native replay rejects unavailable
or failed compilation. The successor's `run --source-root` route wraps its native
numeric providers; the source-bound native replay commands retain their separate
interfaces.

## Evidence fields remain separate

The successor produces the following report states; a manuscript citation does
not change them:

| Field | Value or source | Meaning |
| --- | --- | --- |
| `lean_status` | `NOT_EXECUTED` | The numeric application does not run Lean |
| `mathematical_implementation` | `NUMERIC_ONLY` | Exact rational computation in the application report |
| `numerical_verification` | Independent check's actual status | Arithmetic/witness validation on the declared finite input |
| `kernel_checked_proof` | `NOT_EXECUTED` | Compiler execution is a separate operation |
| `independent_mathematical_certification` | `NOT_ASSESSED` | Independent research acceptance is external |
| `application_release_acceptance` | `NOT_ASSESSED` | The individual report does not issue release approval |
| `empirical_identification` | `NOT_IDENTIFIED` | Primitives are declared rather than identified from data by this application |
| `publication_approval` | `NOT_ASSESSED` | The report does not authorize publication |
| `scientific_claims_verified` | `false` | Numeric checking does not certify a scientific interpretation |

The nine distinct reporting coordinates—`validity`, `epistemic_mode`,
`selection_status`, `identification_status`, `statistical_status`,
`provenance_status`, `substantive_pr_status`, `direction_status` and
`uniform_gap_status`—remain `null` in these application reports. Their being
distinct does not assert statistical independence. The
[evidence guide](../../apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md)
defines the literal fields, and the
[acceptance record](../../apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md)
separately records the actual software release and bounded Lean evidence.

## How to review one paper-to-application route

1. Find the paper label and its actual hypotheses in the mathematical crosswalk.
2. Select the exact profile, command and input contract from the table above.
3. Check the independent receipt equations and any optimum or infeasibility witness.
4. Inspect the generated Lean family's reflected dimensions, source-binding checks
   and the theorem it transfers; compare its premises and conclusion with the paper.
5. Keep the compiler/axiom/mutation receipt and its source identity separate from
   the numeric receipt and from historical acceptance or empirical identification.
6. Check [current residual status](RESIDUAL_STATUS.md) before describing a stronger
   historical or general mathematical requirement as closed.

The [application reviewer guide](../../apps/permansson/application-successor/docs/REVIEWER_GUIDE.md)
and [verification guide](VERIFICATION.md) contain the execution routes. This map
records no new compiler, release, independent-case or empirical acceptance result.

## Remaining implementation and identification scope

The existing application roadmap retains benchmark `FIX-01`, expert non-finite
conditional evidence `ADV-01`, parts of the cross-profile contract layer,
source-grade domain importers and other explicitly unimplemented scope. A paper
derivation does not activate a missing application profile. Multi-stage private
games, committed-game optimality, overlap-model atom certificates and general
Exact GR/PR or QSD claims must be assessed against their actual interfaces rather
than inferred from nearby finite profiles. Source-grade causal identification,
independent mathematical case acceptance and runtime evidence promotion remain
separate obligations. See the
[application roadmap](../../apps/permansson/application-successor/docs/ROADMAP.md)
and [current residual status](RESIDUAL_STATUS.md).

## Maintenance rule

This page is the complete paper-to-application matrix. The application-local
`PAPER2_MAPPING.md` is a concise reading projection pinned to an exact revision of
this page; it does not maintain a second mutable set of numerical bounds or
acceptance decisions. On a future profile or manuscript change, compare the
literal registry, family map, bridge bounds and paper labels together, then record
the new source identity. The original application standard, native versions,
released wheel and historical evidence retain their own identities.
