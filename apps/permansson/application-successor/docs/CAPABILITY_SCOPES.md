# Capability scopes

Every profile below is registered in `src/permansson_app/data/capabilities.json`,
has its own command line, and has an independent exact checker that does not
import the producer. Every profile reports `lean_status=NOT_EXECUTED` and
`scientific_claims_verified=false`. The exact numeric scope of each profile —
dimensions, horizons and what is *not* claimed — is the `scope` string of its
registry entry. `permansson-app capabilities` prints those strings.

## Closed native providers

| Capability | Route |
| --- | --- |
| `c10.fixed_six_state.numeric.v1` | `permansson-app run` (native C10 provider) |
| `c11.stationary_1_to_6.numeric.v1` | `permansson-app run` (native C11 provider) |

These wrap the existing C10/C11 providers unchanged.

## Exact numeric profiles and their Lean families

The last column is the source-bound Lean candidate family. Emit a candidate
with `permansson-app lean-emit --family <family>` and recheck its bytes with
`lean-recheck`. Each family is bounded: the linked bridge document states the
Lean-side limits (for example the horizons that are reflected) and the
semantic mutations its live replay rejects.

| Profile | Command | Independent checker | Lean family |
| --- | --- | --- | --- |
| `finite.adaptive_block_control.numeric.v1` | `finite-adaptive-grammar` | `receipts.adaptive.check_adaptive` | `adaptive` ([doc](ADAPTIVE_LEAN_BRIDGE.md)) |
| `finite.almost_sure_safety_core.numeric.v1` | `finite-safety` | `receipts.safety.check_safety_core` | `safety-core` ([doc](SAFETY_CORE_LEAN_BRIDGE.md)) |
| `finite.alpha_P_U.induced_kernel.numeric.v1` | `finite-kernel` | `receipts.finite_world.check_finite_receipt` | `finite-world` ([doc](FINITE_WORLD_LEAN_REIFICATION_V1.md)) |
| `finite.cq1_certificate_transport.numeric.v1` | `finite-cq1-transport` | `receipts.cq1_transport.check_cq1_transport` | `cq1-transport` ([doc](CQ1_TRANSPORT_LEAN_BRIDGE.md)) |
| `finite.cq1_constitutive_certificate.numeric.v1` | `finite-cq1` | `receipts.cq1.check_cq1` | `cq1` ([doc](CQ1_LEAN_BRIDGE.md)) |
| `finite.first_exit_and_survival.numeric.v1` | `finite-exit` | `receipts.exit.check_exit` | `exit` ([doc](EXIT_LEAN_BRIDGE.md)) |
| `finite.frozen_menu.numeric.v1` | `frozen-menu` | `receipts.menu.check_menu` | `menu` ([doc](MENU_LEAN_BRIDGE.md)) |
| `finite.hitting_bellman.numeric.v1` | `finite-bellman` | `receipts.control.check_bellman` | `control-table` ([doc](CONTROL_TABLE_LEAN_BRIDGE.md)) |
| `finite.killed_kernel.survival.numeric.v1` | `finite-survival` | `receipts.finite_survival.check_survival_receipt` | `survival` ([doc](MENU_LEAN_BRIDGE.md)) |
| `finite.metric_contraction_perturbation.numeric.v1` | `finite-metric` | `receipts.metric.check_metric` | `metric` ([doc](METRIC_LEAN_BRIDGE.md)) |
| `finite.nonlinear_classwise_stationary.numeric.v1` | `nonlinear-stationary` | `receipts.nonlinear.check_nonlinear` | `nonlinear` ([doc](NONLINEAR_LEAN_BRIDGE.md)) |
| `finite.observation_history_tree.numeric.v1` | `finite-belief-tree` | `receipts.belief_tree.check_belief_tree` | `belief` ([doc](BELIEF_LEAN_BRIDGE.md)) |
| `finite.one_step_observation_belief.numeric.v1` | `one-step-belief` | `receipts.belief.check_belief` | `belief` ([doc](BELIEF_LEAN_BRIDGE.md)) |
| `finite.one_step_risk_infeasibility.numeric.v1` | `one-step-risk-infeasibility` | `receipts.risk_infeasibility.check_risk_infeasibility` | `risk-infeasibility` ([doc](RISK_INFEASIBILITY_LEAN_BRIDGE.md)) |
| `finite.one_step_risk_occupancy.numeric.v1` | `one-step-risk` | `receipts.risk_occupancy.check_risk` | `flow` ([doc](FLOW_LEAN_BRIDGE.md)) |
| `finite.patch_grammar.numeric.v1` | `finite-grammar` | `receipts.grammar.check_grammar` | `grammar` ([doc](GRAMMAR_LEAN_BRIDGE.md)) |
| `finite.path_perturbation_tv.numeric.v1` | `finite-perturbation` | `receipts.robustness.check_perturbation` | `perturbation` ([doc](PERTURBATION_LEAN_BRIDGE.md)) |
| `finite.private_control_stage_saddle.numeric.v1` | `finite-private-stage` | `receipts.private_stage.check_private_stage` | `private-stage` ([doc](PRIVATE_STAGE_LEAN_BRIDGE.md)) |
| `finite.random_occupation.numeric.v1` | `finite-occupation` | `receipts.occupation.check_occupation` | `occupation` ([doc](OCCUPATION_LEAN_BRIDGE.md)) |
| `finite.rational_algebra_witness.numeric.v1` | `finite-algebra` | `receipts.algebra.check_algebra` | `algebra` ([doc](ALGEBRA_LEAN_BRIDGE.md)) |
| `finite.rectangular_vs_committed_nature.numeric.v1` | `finite-robust-nature` | `receipts.robust_nature.check_nature` | `robust-nature` ([doc](ROBUST_LEAN_BRIDGE.md)) |
| `finite.residence_monitor.numeric.v1` | `finite-residence` | `receipts.residence.check_residence` | `residence` ([doc](RESIDENCE_LEAN_BRIDGE.md)) |
| `finite.two_player_protocol.numeric.v1` | `finite-multiagent` | `receipts.multiagent.check_multiagent` | `multiagent` ([doc](MULTIAGENT_LEAN_BRIDGE.md)) |
| `finite.typed_quotient.numeric.v1` | `finite-quotient` | `receipts.quotients.check_quotient` | `quotient` ([doc](QUOTIENT_LEAN_BRIDGE.md)) |
| `lp.exact_rational.independent_verification.v1` | `lp-check` | `receipts.lp` | `lp` ([doc](LP_CERTIFICATE_LEAN_BRIDGE.md)) |
| `lp.exact_rational.optimality.numeric.v1` | `lp-propose` | `receipts.lp.check_lp_certificate` | `lp` ([doc](LP_CERTIFICATE_LEAN_BRIDGE.md)) |

## Reading a scope

- A *numeric* result is exact rational arithmetic with an independent
  recomputation. It is not a Lean proof.
- A *Lean family* means a candidate can be emitted and compiled with the
  pinned toolchain. Application outputs still say `NOT_EXECUTED`, because the
  application does not run or authenticate the compiler; see
  [`NATIVE_PROOF_REPLAY.md`](NATIVE_PROOF_REPLAY.md).
- No profile claims empirical identification, Exact GR/PR, independent
  mathematical certification or release acceptance. See
  [`EVIDENCE_AND_RECEIPTS.md`](EVIDENCE_AND_RECEIPTS.md).
