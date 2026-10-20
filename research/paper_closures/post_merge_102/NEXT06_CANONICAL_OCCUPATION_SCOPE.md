# NEXT-06.1 — Native phase-model implementation scope

Source baseline: `3931e4dccafb47b3cdf70177c0cf337102c90731` (tree `0ffd313dcd5efd1cf90a85ee458024b1b28cd3f8`). Parent build contract:
`PERMANSSON-POST102-PARALLEL-BUILD-FINAL-2026-10-20`, P-06 wave 1.

## Mathematical model

Strategic memory `S=Fin 3`, physical world `X=Bool`, action `A=Bool`.
Every controller has literally the same `P((phase,x),a)=delta_a` and
`U((phase,x),a,x')=delta_(phase+1 mod 3)`; only alpha differs.
`period_three_matrix_eq_induced` identifies all thirty-six singleton
entries of the *actual* `alpha -> P -> U` kernel with exact rational
zero/one atoms. It is not a separate six-state physical model.

The selected controller chooses `a=(phase != 2)`. Starting at
`(0,false)`, the native state sequence is
`(0,false) -> (1,true) -> (2,true) -> (0,false)`.
The policy is stationary on the augmented state; it is not a
Bool-only stationary feedback policy.

## Explicit residuals

This phase-1 construction does not yet prove the infinite-path
occupation-limit law, class-by-class nonlinear functional, canonical
path-law expectation, deterministic phase-blind optimality, or original
D-09 multichain aggregation. Those belong to P-06 wave 2 and P-AUDIT.

A stationary randomized Bool-only controller can match value 1;
no superiority claim may quantify over that larger policy class.
No exact GR/PR or empirical classification follows from this witness.

Verification: independent Python exact finite arithmetic complements the
Lean theorem and must never be relabeled as a Lean proof. CI/axiom and
semantic-mutant receipts must be bound to their actual source heads.

## NEXT-06.2 canonical-limit substage (draft, pending compiler)

Using the genuine native model (phase `Fin 3`, physical `Bool`),
`NonlinearPeriodThreeCanonical.lean` proposes
`native_inducedKernel_eq_deterministic` as a finite-state equality to the
actual `nextState` Dirac kernel, and
`native_actual_occupation_ae_limit` as a specialization of the already
proved true canonical a.s. empirical occupation theorem to the original
typed `StrategicWorldModel.pathLaw`. No strategic/world quotient is used.

This **does not** discharge the class identity, exact `1/3` weights,
physical `2/3` true occupation, actual nonlinear expected score, complete
four-policy `5/6` theorem, randomized tie boundary or historical D-09
multichain acceptance. All remain required for P-06.2 full closure.

Build source base: `6bc86eaa71fb26a5e86e2d7ffd88e4c1af4f0760`. No certification or publication claim
until source HEAD, synthetic merge, compiler axioms and negative tests pass.
