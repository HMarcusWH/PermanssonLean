# Solver and stationary selected-scope review

Reviewed against `spec/chapters/06_solver.md`, `07_stationary_families.md`, and
the exact `selected_scope` fields of `spec/registries/closure_contracts.json`.
This is a statement-level scope review, independent of the 45-case acceptance
ledger and independent of final source-head/merge CI. It does not enlarge a
selected finite contract into the broader atlas programme.

## Material omission found and repaired

D2-P03 requires a separate through-horizon risk flag in addition to success
before danger. The original success monitor correctly retains completed
success after later danger, but that behavior alone does not record the event
`exists t <= N, danger(Y_t)`.

The additive `ReverseSolver/ThroughHorizonRiskMonitor.lean` now appends a Bool
flag to an arbitrary original monitor. It reads the initial observation and
every successor, even when the original monitor is in a terminal phase.
`initial_risk_iff_literal` and `initial_risk_iff_time` identify the flag with
the independent literal event. `actual_risk_integral_eq_literal` and
`actual_risk_probability_eq_occupancy` identify it under the independently
normalized full-history occupancy law, for every allowed real behavioral
controller. `actual_success_integral_eq_original` preserves the original
success reward under that same law. The rational `riskScore` lies in [0,1]
and is an actual terminal linear risk score for the existing flow LP.

`ThroughHorizonRiskFixture.lean` separately checks danger at zero, simultaneous
target/danger, danger after completed success (both success and risk equal
one), and failure without danger. Both module compilations and the actual
20-declaration source-bound signature/transitive-axiom audit passed. The
discovered `test_paper_through_risk_lean.py` passed one test in 35.408 seconds.
The durable receipt is `through_horizon_risk_receipt.json`; its full checked
statements are in `through_horizon_risk_signatures_axioms.txt`.

## Other reviewed selected conclusions

No further material missing conclusion or stronger hidden input was found in
the following selected solver/stationary clauses:

| Selected target | Actual statement or construction examined |
| --- | --- |
| D2-R01 | `behavioralResidence_optimal_and_attained`, `rollingResidence_optimal_and_attained`, compact streak/event induction with N=T+m and m+1 observations. |
| D2-P01 | `monitor_optimal_and_attained`, `monitor_initialLaw_optimal_and_attained`; real full-history behavioral weights, actual chronological normalization, history-reconstructed deterministic attainer. |
| D2-P02 | `firstEntryTest_iff_block`, `firstRun_correct`, `behavioralFirstEntry_optimal_and_attained`; time-zero/deadline/irreversible first-run semantics. |
| D2-P03 | `behavioralAvoidResidence_optimal_and_attained` plus the separate through-horizon risk repair above. |
| D2-P04 | `actual_history_flow_equivalence`, `actual_success_risk_range_eq_flow`, `solveRiskFlow_none_iff_no_behavioral_policy`, `solveRiskFlow_some_actual_optimal`; exact rational active-set enumeration and actual legal x/d reconstruction, including zero-mass branches. |
| D2-P05 | `rectangular_game_law_saddle` against all admitted real behavioral controller/nature histories; nature receives realized control. Separate `returned_actual_strategic_value` solves the hidden-private-draw stage LP. |
| D2-P06 | `actual_history_conditional`, `alpha_envelope`, `value_convex`, `monitored_history_dominated`, `monitored_history_attained`; common legal control menu, full hidden physical/monitor pair, actual observation-history law, zero-denominator fallback. |
| D2-P07 | `deterministic_stationary_infinite_optimum`, `infiniteSafety_isGreatest`, `invariantCore_iff_almostSureSafety`; actual infinite event, decreasing finite values, limiting fixed point, finite greatest-invariant iteration. |
| D2-P08 | `adaptive_block_optimal_and_attained`, `typedChronologicalLaw_eq`; actual alpha/P/U block atoms, preselected block per stage, fixed world, compatible/admitted rational menu. |
| D2-P09 | `rationalObjective_eq_actual`, `stationary_menu_actual_optimal_and_attained`, `equal_descriptor_laws_equal_values`; actual C10 class-entry weights and C11 descriptor-limit laws over every admissible deterministic stationary policy. |
| C11-P01 | `referenceMatrix_det_ne_zero`, `referenceWeights_probability`, `referenceStationaryFamily_check`, `referenceClassCandidate_eq_native`; every nonempty finite rational stochastic matrix, canonical complete duplicate-free bottom-class list, explicit determinant weights, zero extension and genuine typed class law. |

The C11 proof derives nonsingularity directly over the rationals and proves
its real determinant cast in `referenceWeights_probability`. This is a proof
of the same explicit constructor, with no numerical nonsingularity oracle,
periodicity exclusion, or twelve-state mathematical resource restriction.

## Premises and optional extensions kept separate

- D-CLASS's predeclared exact functional evaluator is an explicit premise of
  the selected contract. It is certified on the constructed rational class
  laws; it is not an assumed policy/occupation or absorption equivalence.
- D-BLOCK's admissibility, overlap compatibility and rational atom
  certificates are the selected certified-menu inputs. Equality of the
  resulting actual chronological laws and the optimizer is proved.
- D-BELIEF's common legal menu is required by the selected alpha-vector
  contract. Arbitrary belief-dependent menus are excluded there.
- LP efficiency, strong duality and the optional weak-dual checker are not
  needed for the total exact vertex constructor. The rolling residence code
  gives the stated finite table dimensions; it does not claim rational bit
  complexity or a separate machine cost-model theorem.
- General adaptive asymptotic synthesis, static-hidden-model rectangular
  recursion, nonfinite infinite retention, and the optional full-horizon
  no-danger success variant remain outside these selected statements.

## F1 and grammar spot checks

No additional material selected-clause gap was found in the finite
feasibility, product-player, correlated-mediator, causal or compatible-grammar
interfaces inspected. In particular, `FeasibleAnchors` proves the actual
fibre intersection criterion and least legal selector; `FiniteMediation`
derives observational identification from the declared product-noise SCM and
has an on-support positivity theorem. `OriginalLowerSetTransport` proves the
actual margin match before using the stated strict lower-set coverage gate.

Two profile boundaries must remain visible: the player-swap canonical path
and original-margin bridges currently have explicit finite coordinate-space
assumptions (the chapter gives a finite-sum proof); the general measurable
finite-index product construction is a separate proved profile. The natural
private-clock strengthening for F1-P03 is separately checked in the X1
agent's countable-state/finite-action/world profile. The final unrestricted
measurable-coordinate closure is now independently checked in
`MEASURABLE_NAT_CLOCK_SCOPE.md`: three additive modules, 51-export actual
source/signature/axiom audit, and a discovered integration test.
