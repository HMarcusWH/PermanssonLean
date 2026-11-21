# Reading the reviewed paper alongside the application

[Application documentation](README.md) · [Capabilities](CAPABILITY_SCOPES.md) · [Evidence fields](EVIDENCE_AND_RECEIPTS.md)

The reviewed manuscript **Permansson Regimes: Structure, Intervention, and
Computation Beyond Equilibrium**, v2.0.1 (20 November 2026), explains the
mathematics behind the finite computation and reflection routes. Use the
[versioned publication hub](https://github.com/HMarcusWH/PermanssonLean/blob/39f97d409e2731d286bbf5b835a8ae6acc038667/paper2/README.md)
for its PDF, source/concordance package, review record and citation.

The [complete paper-to-application compatibility map](https://github.com/HMarcusWH/PermanssonLean/blob/f7e969f027f166068a050a91c92ebda6296f412a/docs/paper2/APPLICATION_COMPATIBILITY.md)
is authoritative for the reading correspondence. This page is its concise
application-local projection. It gives topic routes, while the existing
[capability scopes](CAPABILITY_SCOPES.md), linked bridge documents and actual
registry remain the implementation contracts. The table does not assert an
independent equivalence proof for every mapped paper statement.

## Read in this order

1. **§29.1–29.2:** exact typed input, independent receipts and literal-data reflection.
2. **§29.3:** all 26 exact numeric profiles; use the table below to find a topic.
3. **§29.4:** the separate native C10/C11 replay routes.
4. **§29.5 and §30:** legacy contracts, release evidence, negative controls and
   source concordance.
5. **Appendix P:** the precise residual obligations; use the
   [current residual ledger](https://github.com/HMarcusWH/PermanssonLean/blob/f7e969f027f166068a050a91c92ebda6296f412a/docs/paper2/RESIDUAL_STATUS.md)
   for their source/evidence distinctions.

Paper labels are resolved through the
[mathematical crosswalk](https://github.com/HMarcusWH/PermanssonLean/blob/f7e969f027f166068a050a91c92ebda6296f412a/docs/paper2/MATHEMATICAL_CROSSWALK.md).
The section numbers below refer to paper v2.0.1, not reference-guide chapters.

## All 26 profile reading routes

| Registered profile | Command | Paper sections; appendices |
| --- | --- | --- |
| `finite.adaptive_block_control.numeric.v1` | `finite-adaptive-grammar` | 11, 17, 29; F, J |
| `finite.almost_sure_safety_core.numeric.v1` | `finite-safety` | 19, 29; J |
| `finite.alpha_P_U.induced_kernel.numeric.v1` | `finite-kernel` | 3, 29; K |
| `finite.cq1_certificate_transport.numeric.v1` | `finite-cq1-transport` | 12, 13, 29; F, G |
| `finite.cq1_constitutive_certificate.numeric.v1` | `finite-cq1` | 12, 29; F |
| `finite.first_exit_and_survival.numeric.v1` | `finite-exit` | 10, 29; D, K |
| `finite.frozen_menu.numeric.v1` | `frozen-menu` | 17, 20, 29; J, K |
| `finite.hitting_bellman.numeric.v1` | `finite-bellman` | 17, 29; J, K |
| `finite.killed_kernel.survival.numeric.v1` | `finite-survival` | 4, 12, 29; F, K |
| `finite.metric_contraction_perturbation.numeric.v1` | `finite-metric` | 14, 29; H |
| `finite.nonlinear_classwise_stationary.numeric.v1` | `nonlinear-stationary` | 21, 29; K |
| `finite.observation_history_tree.numeric.v1` | `finite-belief-tree` | 18, 29; J |
| `finite.one_step_observation_belief.numeric.v1` | `one-step-belief` | 18, 29; J |
| `finite.one_step_risk_infeasibility.numeric.v1` | `one-step-risk-infeasibility` | 19, 29; J, K |
| `finite.one_step_risk_occupancy.numeric.v1` | `one-step-risk` | 19, 29; J, K |
| `finite.patch_grammar.numeric.v1` | `finite-grammar` | 11, 29; F |
| `finite.path_perturbation_tv.numeric.v1` | `finite-perturbation` | 13, 29; G |
| `finite.private_control_stage_saddle.numeric.v1` | `finite-private-stage` | 22, 29; L |
| `finite.random_occupation.numeric.v1` | `finite-occupation` | 7, 20, 29; D, K |
| `finite.rational_algebra_witness.numeric.v1` | `finite-algebra` | 26, 29; M |
| `finite.rectangular_vs_committed_nature.numeric.v1` | `finite-robust-nature` | 22, 29; L |
| `finite.residence_monitor.numeric.v1` | `finite-residence` | 17, 29; J |
| `finite.two_player_protocol.numeric.v1` | `finite-multiagent` | 24, 29; L |
| `finite.typed_quotient.numeric.v1` | `finite-quotient` | 16, 29; I |
| `lp.exact_rational.independent_verification.v1` | `lp-check` | 19, 29; K |
| `lp.exact_rational.optimality.numeric.v1` | `lp-propose` | 19, 29; K |

The [capability table](CAPABILITY_SCOPES.md) gives each command's independent checker
and candidate family. Numerical dimensions, horizons and reflection limits are
intentionally not duplicated in this reading projection; use that table and its
bridge links for the literal scope.

## Native and historical routes

- **C10:** §29.4 and Appendix K discuss the frozen six-state menu and complete
  comparison set `[1,2]`. This remains the C10 native input profile.
- **C11:** §29.4, §20 and Appendix K discuss exact stationary families. The native
  CLI remains bounded to 1–6 states with a Boolean descriptor.
- **Legacy validation:** §29.5 distinguishes structural validation of an application
  packet from numerical computation, proof replay and scientific identification.
  The successor wrapper preserves the historical validator's source contract.

## Version and evidence meaning

The paper is a reviewed manuscript draft. This documentation update does not
change application version 0.2.0, its released wheel or its platform scope.
The current source tree can contain new reading documentation that was not part
of the November 1 release. See [release acceptance](RELEASE_ACCEPTANCE.md).

Checked numeric-profile `scientific_report.json` files retain
`kernel_checked_proof=NOT_EXECUTED`, `scientific_claims_verified=false`,
`empirical_identification=NOT_IDENTIFIED` and
`publication_approval=NOT_ASSESSED`. The native wrapper instead writes
`application_result.json` with `lean_status=NOT_EXECUTED` and its own gate
fields; raw receipts also have profile-specific shapes. See the
[evidence guide](EVIDENCE_AND_RECEIPTS.md) for the exact records. Source-bound
Lean families and the separate native replay routes keep their existing
evidence meanings. A paper link does not update a report or grant independent
research-case acceptance.

All external links on this page are pinned GitHub URLs so this documentation
continues to work when the application is copied or installed without the rest
of the repository. The publication and central-doc commits have distinct roles.
