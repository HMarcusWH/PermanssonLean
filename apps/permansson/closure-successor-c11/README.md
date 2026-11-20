# Permansson C11 closure successor v0.2.0

This is a separately versioned C11 application slice beside (not a rewrite
of) the [merged C10 v0.1.0 implementation](../closure-successor/README.md)
and the frozen original `application/` directory. It reuses the repository's
exact C11 stationary producer, independent checker and genuine finite Lean
proof generator. This statement does **not** promote C10 to a formally accepted
application release: its current `VERSION.json` still records
`DRAFT__COMPILER_CI_PENDING`, requiring separate reconciliation.

## Reading the reviewed second-edition paper

Manuscript v2.0.1 **§29.4, “Native C10 and C11 replay”** (`sub:C29:04`; printed
page 114, PDF page 124) explains this route's place in the evidence chain. Read
the [reviewed PDF](https://github.com/HMarcusWH/PermanssonLean/blob/8630e80b604223aa0fadff92d6a7c2749cd8be5b/paper2/v2.0.1/Permansson_Regimes_v2_0_1_Reviewed_Manuscript_2026-11-20.pdf#page=124),
the [versioned publication hub](https://github.com/HMarcusWH/PermanssonLean/blob/8630e80b604223aa0fadff92d6a7c2749cd8be5b/paper2/README.md),
and the [current native-route comparison](https://github.com/HMarcusWH/PermanssonLean/blob/2f20d86e42a8b0ed15f59d5a480a2b61efc80f7a/docs/paper2/APPLICATION_COMPATIBILITY.md#native-c10-and-c11).
The paper's algorithms and semantic proofs are in §20, §29 and Appendix K.

The native input remains a 1–6-state rational stochastic matrix with a Boolean
descriptor. The manuscript does not enlarge that bound or change the evidence
meaning of a reified stationary-family replay.

## Supported inputs

Strict JSON with exactly `n`, `matrix` and `descriptor` keys. `n` is 1..6, rows are finite exact rational strings summing to 1, descriptor is a Boolean per state. Per-entry bit budgets and duplicate-key constraints are enforced by the original C11 producer. Both periodic and multichain examples are provided.

```
python apps/permansson/closure-successor-c11/cli.py \
  apps/permansson/closure-successor-c11/examples/multiclass_three_state.json \
  --mode replay --output /tmp/c11-multiclass-fresh
```

The steps are external input → `c11_stationary_execution.execute` → independently checked complete bottom-class list, exact stationary weights and balance equations → `c11_emit_stationary_lean.emit_source` → pinned Lean compiler → all generated theorem-axiom reports → structured source-bound receipt. `--mode numeric` never runs Lean and must never report a Lean certificate. Genuine `replay` requires a clean Git checkout and verified provider object hashes and exits nonzero if the compiler is unavailable, rejects the proof, or fails to print every theorem axiom audit.

Result statuses are deliberately distinct: exact numerical calculation, genuine Lean kernel replay, **scientific_claims_verified=false**, and **empirical_identification=NOT_IDENTIFIED**. Lean proves the stationary probabilities for the **reified** input finite matrix; the CLI does not prove the JSON parser, external causal/world identification, original Exact GR/PR, strategic model or regime invariance. It cannot justify operational action.

## Not included

No automatic mapping from an external model to the frozen strategic-world histories and legal interventions. No nonlinear policy/robust nature/partial observation optimality theorem. No empirical certification. A supported input is not necessarily an identified real-world model. Bigger models need explicit performance/testing review rather than a silent increase in limits.

All evidence must be written to a fresh, empty directory outside the repository. No file under the preserved `application/` root is changed.
