# Permansson C11 closure successor v0.2.0

This is a **new** explicit C11 application slice beside (not a rewrite of) the already accepted C10 v0.1.0 successor and the frozen original `application/` directory. It reuses the repo's exact C11 stationary producer, independent checker and genuine finite Lean proof generator.

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
